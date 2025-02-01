using System.CommandLine;
using Microsoft.Z3;
using SDC.AST;
using SDC.Converter;
using SDC.PreProcessingPass;

namespace SDC.CLI;

class SDC
{
    static void DefineOperation<T>(IEnumerable<TypeReference> types, List<T> methods, List<Func<TypeReference, T>> builders)
    {
        foreach (var type in types)
        {
            foreach (var builder in builders)
            {
                methods.Add(builder(type));
            }

        }
    }

    static void DefinePreludeOperations(IEnumerable<TypeReference> sorts, List<MethodDefinition> methods, List<FunctionDefinition> functions)
    {
        DefineOperation(sorts, methods, PreludeOperations.MethodBuilders);
        DefineOperation(sorts, functions, PreludeOperations.FunctionBuilders);
    }

    static MethodDefinition DefineSpecMethod(BoolExpr[] methodConstraints, ISet<TypeReference> preludeTypes)
    {
        MethodConverter m = new MethodConverter();
        MethodDefinition methodDef = m.Convert("Constraints", methodConstraints, preludeTypes);

        if (methodDef.ResultParameter == null)
        {
            throw new Exception("Missing result parameter");
        }

        return methodDef;
    }

    static FunctionDefinition DefineSpec(BoolExpr[] functionConstraints, ISet<TypeReference> preludeTypes)
    {
        FunctionConverter f = new FunctionConverter();
        FunctionDefinition functionDef = f.Convert("Spec", functionConstraints, preludeTypes);
        return functionDef;
    }

    static void WriteMainToDisk(Program program, MethodDefinition methodDef, DirectoryInfo outputDir, string fileName)
    {
        MainGenerator mainGenerator = new MainGenerator();
        mainGenerator.GenerateMain(program, methodDef);

        outputDir.Create();
        File.WriteAllText(Path.Join(new string[] { outputDir.FullName, fileName }), ASTWriter.Serialize(program));
    }

    static Expression BuildPointwiseEq(MethodDefinition impl, FunctionDefinition spec)
    {
        IdentifierExpression functionIdExpr = new IdentifierExpression(spec.Identifier);
        List<Expression> freeVariables = impl.Parameters.Select(p => p.Variable.ToExpression()).Cast<Expression>().ToList();
        Expression methodResultVarExpr = impl.ResultParameter.Variable.ToExpression();
        return new BinaryExpression(new CallExpression(functionIdExpr, freeVariables), Operator.Equal, methodResultVarExpr);
    }

    static void ApplyPreprocessingPasses(in BoolExpr[] constraints)
    {
        for (var i = 0; i < constraints.Length; i++)
        {
            constraints[i] = (BoolExpr)PreprocessingPasses.Preprocess(constraints[i]);
        }
    }

    static void PreprocessSMTFile(FileInfo inputSMTFile, DirectoryInfo outputDir)
    {
        string smt2FunctionContent = File.ReadAllText(inputSMTFile.FullName);

        using (Context ctx = new Context())
        {
            BoolExpr[] constraints = ctx.ParseSMTLIB2String(smt2FunctionContent, null, null, null, null);
            ApplyPreprocessingPasses(constraints);

            Solver s = ctx.MkSolver();
            s.Add(constraints);

            outputDir.Create();
            File.WriteAllText(Path.Join(new string[] { outputDir.FullName, "preprocess.smt2" }), s.ToString());
        }
    }
    static void CompileFunction(FileInfo inputSMTFunction, DirectoryInfo outputDir)
    {
        string smt2FunctionContent = File.ReadAllText(inputSMTFunction.FullName);

        using (Context ctx = new Context())
        {
            HashSet<TypeReference> preludeTypes = new();
            List<FunctionDefinition> functions = new();
            BoolExpr[] functionConstraints = ctx.ParseSMTLIB2String(smt2FunctionContent, null, null, null, null);
            ApplyPreprocessingPasses(functionConstraints);
            FunctionDefinition functionDef = DefineSpec(functionConstraints, preludeTypes);
            functions.Add(functionDef);

            List<MethodDefinition> methods = new List<MethodDefinition>();
            DefinePreludeOperations(preludeTypes, methods, functions);

            Program program = new Program(new List<Import>(), functions, methods);

            outputDir.Create();
            File.WriteAllText(Path.Join(new string[] { outputDir.FullName, "compiled.dfy" }), ASTWriter.Serialize(program));
        }
    }

    static void CompilePointwise(FileInfo inputSMTFunction, FileInfo inputSMTMethod, DirectoryInfo outputDir)
    {
        string smt2FunctionContent = File.ReadAllText(inputSMTFunction.FullName);
        string smt2MethodContent = File.ReadAllText(inputSMTMethod.FullName);

        using (Context ctx = new Context())
        {
            BoolExpr[] methodConstraints = ctx.ParseSMTLIB2String(smt2MethodContent, null, null, null, null);
            ApplyPreprocessingPasses(methodConstraints);
            List<MethodDefinition> methods = new();
            HashSet<TypeReference> preludeTypes = new();
            MethodDefinition methodDef = DefineSpecMethod(methodConstraints, preludeTypes);
            methods.Add(methodDef);

            List<FunctionDefinition> functions = new();
            BoolExpr[] functionConstraints = ctx.ParseSMTLIB2String(smt2FunctionContent, null, null, null, null);
            ApplyPreprocessingPasses(functionConstraints);
            FunctionDefinition functionDef = DefineSpec(functionConstraints, preludeTypes);
            functions.Add(functionDef);


            // In case any optimization removes a free variable, both cases must match.
            if (methodDef.Parameters.Count > functionDef.Parameters.Count)
            {
                functionDef.Parameters = methodDef.Parameters.ToList();
            }
            else
            {
                methodDef.Parameters = functionDef.Parameters.ToList();
            }

            methodDef.Ensures = BuildPointwiseEq(methodDef, functionDef);

            DefinePreludeOperations(preludeTypes, methods, functions);

            Program program = new Program(new List<Import>(), functions, methods);

            WriteMainToDisk(program, methodDef, outputDir, "compiled.dfy");
        }
    }

    static FunctionDefinition DefineModelSpec(BoolExpr[] modelConstraints, List<Expression> freeVariables, out Expression modelSatExpr)
    {
        FunctionConverter requireFunction = new FunctionConverter();
        FunctionDefinition modelDef = requireFunction.Convert("Model", modelConstraints, new HashSet<TypeReference>());
        modelSatExpr = new BinaryExpression(new CallExpression(new IdentifierExpression(modelDef.Identifier), freeVariables), Operator.Equal, LiteralExpression.True);
        return modelDef;
    }

    static Expression EvalModel(Context ctx, BoolExpr[] modelConstraints, BoolExpr[] methodConstraints)
    {
        Solver solver = ctx.MkSolver();
        solver.Assert(modelConstraints);
        solver.Check();

        Microsoft.Z3.Expr satValue = solver.Model.Eval(ctx.MkAnd(methodConstraints), false);
        bool isConstantValue = satValue.IsFalse || satValue.IsTrue;
        if (!isConstantValue)
        {
            throw new Exception("The input model model does not instantiate the input constraints.");
        }

        Expression expectedValue = satValue.IsFalse ? LiteralExpression.False : LiteralExpression.True;
        return expectedValue;
    }

    static void CompileModel(FileInfo inputSMTModel, FileInfo? inputSMTFunction, FileInfo inputSMTMethod, DirectoryInfo outputDir)
    {
        string smt2ModelContent = File.ReadAllText(inputSMTModel.FullName);
        string? smt2FunctionContent = inputSMTFunction != null ? File.ReadAllText(inputSMTFunction.FullName) : null;
        string smt2MethodContent = File.ReadAllText(inputSMTMethod.FullName);

        using (Context ctx = new Context())
        {
            BoolExpr[] methodConstraints = ctx.ParseSMTLIB2String(smt2MethodContent, null, null, null, null);
            ApplyPreprocessingPasses(methodConstraints);
            List<MethodDefinition> methods = new();
            HashSet<TypeReference> preludeTypes = new();
            MethodDefinition methodDef = DefineSpecMethod(methodConstraints, preludeTypes);
            methods.Add(methodDef);

            List<Expression> freeVariables = methodDef.Parameters.Select(p => p.Variable.ToExpression()).Cast<Expression>().ToList();
            List<FunctionDefinition> functions = new();
            if (smt2FunctionContent != null)
            {
                BoolExpr[] functionConstraints = ctx.ParseSMTLIB2String(smt2FunctionContent, null, null, null, null);
                ApplyPreprocessingPasses(functionConstraints);
                FunctionDefinition functionDef = DefineSpec(functionConstraints, preludeTypes);
                functions.Add(functionDef);
                methodDef.Ensures = BuildPointwiseEq(methodDef, functionDef);
            }

            BoolExpr[] modelConstraints = ctx.ParseSMTLIB2String(smt2ModelContent, null, null, null, null);
            ApplyPreprocessingPasses(methodConstraints);
            FunctionDefinition modelDef = DefineModelSpec(modelConstraints, freeVariables, out Expression modelSatExpr);
            functions.Add(modelDef);
            methodDef.Requires = modelSatExpr;

            Expression expectedValue = EvalModel(ctx, modelConstraints, methodConstraints);

            // Verify that the result matches the model's evaluation.
            Expression expectedValueEquality = new BinaryExpression(methodDef.ResultParameter.Variable.ToExpression(), Operator.Equal, expectedValue);
            methodDef.Ensures = methodDef.Ensures != null ? new BinaryExpression(methodDef.Ensures, Operator.BooleanAnd, expectedValueEquality) : expectedValueEquality;

            DefinePreludeOperations(preludeTypes, methods, functions);

            Program program = new Program(new List<Import>(), functions, methods);
            WriteMainToDisk(program, methodDef, outputDir, "compiled.dfy");
        }
    }

    static async Task<int> Main(string[] args)
    {
        var outputOption = new Option<DirectoryInfo>(
            name: "--output-dir",
            description: "Output directory for the Dafny translation.")
        {
            IsRequired = true
        };

        var rootCommand = new RootCommand("The SMT Dafny Compiler (SDC)");

        var preprocessCommand = new Command("preprocess", "Applies the preprocessing SMT passes on the input SMT2 file.");
        rootCommand.AddCommand(preprocessCommand);
        {
            Option<FileInfo> inputOption = new Option<FileInfo>(
                name: "--input-smt2",
                description: "The input SMT2 file.")
            {
                IsRequired = true
            };

            preprocessCommand.AddOption(inputOption);
            preprocessCommand.AddOption(outputOption);

            preprocessCommand.SetHandler((inputSMT, outputDir) =>
            {
                if (!inputSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input SMT2 file '{inputSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (outputDir.Exists)
                {
                    Console.Error.WriteLine($"Error: The output directory '{outputDir.FullName}' already exists.");
                    return Task.FromResult(1);
                }

                PreprocessSMTFile(inputSMT, outputDir);

                return Task.FromResult(0);
            },
            inputOption, outputOption);
        }

        var compileCommand = new Command("compile", "Compile an SMT2 file into a Dafny program.");
        rootCommand.AddCommand(compileCommand);

        {
            var pointwiseCommand = new Command("pointwise", "Compile a 'pointwise equivalence' test between the spec and method SMT2 files.");
            compileCommand.AddCommand(pointwiseCommand);
            pointwiseCommand.AddOption(outputOption);
            Option<FileInfo> inputFunctionOption = new Option<FileInfo>(
                name: "--input-smt2-function",
                description: "The input SMT2 file for the Dafny translation (function / mathematical specification).")
            {
                IsRequired = true
            };
            pointwiseCommand.AddOption(inputFunctionOption);
            Option<FileInfo> inputMethodOption = new Option<FileInfo>(
                name: "--input-smt2-method",
                description: "The input SMT2 file for the Dafny translation (method / imperative code).")
            {
                IsRequired = true
            };
            pointwiseCommand.AddOption(inputMethodOption);

            pointwiseCommand.SetHandler((inputFunctionSMT, inputMethodSMT, outputDir) =>
            {
                if (!inputFunctionSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input function file '{inputFunctionSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (!inputMethodSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input method file '{inputMethodSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (outputDir.Exists)
                {
                    Console.Error.WriteLine($"Error: The output directory '{outputDir.FullName}' already exists.");
                    return Task.FromResult(1);
                }

                CompilePointwise(inputFunctionSMT, inputMethodSMT, outputDir);

                return Task.FromResult(0);
            },
            inputFunctionOption, inputMethodOption, outputOption);
        }

        {
            var functionCommand = new Command("function", "Compile a Dafny function computing an input SMT2 formula.");
            compileCommand.AddCommand(functionCommand);
            functionCommand.AddOption(outputOption);
            Option<FileInfo> inputFunctionOption = new Option<FileInfo>(
                name: "--input-smt2-function",
                description: "The input SMT2 file for the Dafny translation.")
            {
                IsRequired = true
            };
            functionCommand.Add(inputFunctionOption);
            functionCommand.SetHandler((inputFunctionSMT, outputDir) =>
            {
                if (!inputFunctionSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input function file '{inputFunctionSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (outputDir.Exists)
                {
                    Console.Error.WriteLine($"Error: The output directory '{outputDir.FullName}' already exists.");
                    return Task.FromResult(1);
                }

                CompileFunction(inputFunctionSMT, outputDir);

                return Task.FromResult(0);
            },
            inputFunctionOption, outputOption);
        }

        {
            var modelCommand = new Command("model", "Compile a 'model' test for an SMT2 file.");
            compileCommand.AddCommand(modelCommand);
            modelCommand.AddOption(outputOption);
            Option<FileInfo> inputFunctionOption = new Option<FileInfo>(
                name: "--input-smt2-function",
                description: "The input SMT2 file for the Dafny translation (function / mathematical specification) -- optional.")
            {
                IsRequired = false
            };
            modelCommand.AddOption(inputFunctionOption);
            Option<FileInfo> inputMethodOption = new Option<FileInfo>(
                name: "--input-smt2-method",
                description: "The input SMT2 file for the Dafny translation (method / imperative code).")
            {
                IsRequired = true
            };
            modelCommand.AddOption(inputMethodOption);
            var inputModelOption = new Option<FileInfo>(
                name: "--input-smt2-model",
                description: "The input SMT2 file encoding the model that should be tested.")
            {
                IsRequired = true
            };
            modelCommand.AddOption(inputModelOption);


            modelCommand.SetHandler((inputModelSMT, inputFunctionSMT, inputMethodSMT, outputDir) =>
            {
                if (!inputModelSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input model file '{inputModelSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (inputFunctionSMT != null && !inputFunctionSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input function file '{inputFunctionSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (!inputMethodSMT.Exists)
                {
                    Console.Error.WriteLine($"Error: The input method file '{inputMethodSMT.FullName}' does not exist.");
                    return Task.FromResult(1);
                }

                if (outputDir.Exists)
                {
                    Console.Error.WriteLine($"Error: The output directory '{outputDir.FullName}' already exists.");
                    return Task.FromResult(1);
                }

                CompileModel(inputModelSMT, inputFunctionSMT, inputMethodSMT, outputDir);

                return Task.FromResult(0);
            },
            inputModelOption, inputFunctionOption, inputMethodOption, outputOption);
        }



        return await rootCommand.InvokeAsync(args);
    }
}
