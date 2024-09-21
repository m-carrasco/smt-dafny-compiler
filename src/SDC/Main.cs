using System.CommandLine;
using Microsoft.Z3;
using SDC.AST;
using SDC.Converter;
using SDC.Stubs;

namespace SDC.CLI;

class SDC
{
    static void CompilePointwise(FileInfo inputSMTFunction, FileInfo inputSMTMethod, DirectoryInfo outputDir)
    {
        string smt2FunctionContent = File.ReadAllText(inputSMTFunction.FullName);
        string smt2MethodContent = File.ReadAllText(inputSMTMethod.FullName);

        using (Context ctx = new Context())
        {
            BoolExpr[] methodConstraints = ctx.ParseSMTLIB2String(smt2MethodContent, null, null, null, null);
            MethodConverter m = new MethodConverter();
            string methodName = "Constraints";
            var methodDef = m.Convert(methodName, methodConstraints);

            if (methodDef.ResultParameter == null)
            {
                throw new Exception("Missing result parameter");
            }

            List<MethodDefinition> methods = m.SafeDivSorts.Select(s => SafeDiv.GetSafeDivMethodCode(s)).ToList();
            methods.Add(methodDef);

            FunctionConverter f = new FunctionConverter();
            string functionName = "Spec";
            BoolExpr[] functionConstraints = ctx.ParseSMTLIB2String(smt2FunctionContent, null, null, null, null);
            var functionDef = f.Convert(functionName, functionConstraints);

            List<FunctionDefinition> functions = f.SafeDivSorts.Select(s => SafeDiv.GetSafeDivFunctionCode(s)).ToList();
            functions.Add(functionDef);

            List<Expression> ensureParams = methodDef.Parameters.Select(p => p.Variable.ToExpression()).Cast<Expression>().ToList();

            methodDef.Ensures = new BinaryExpression(new CallExpression(new IdentifierExpression(functionDef.Identifier), ensureParams), Operator.Equal, methodDef.ResultParameter.Variable.ToExpression());
            Program program = new Program(new List<Import>(), functions, methods);

            MainGenerator mainGenerator = new MainGenerator();
            mainGenerator.GenerateMain(program, methodDef);

            outputDir.Create();
            File.WriteAllText(Path.Join(new string[] { outputDir.FullName, "compiled.dfy" }), ASTWriter.Serialize(program));
        }
    }

    static void CompileModel(FileInfo inputSMTModel, FileInfo? inputSMTFunction, FileInfo inputSMTMethod, DirectoryInfo outputDir)
    {
        string smt2ModelContent = File.ReadAllText(inputSMTModel.FullName);
        string? smt2FunctionContent = inputSMTFunction != null ? File.ReadAllText(inputSMTFunction.FullName) : null;
        string smt2MethodContent = File.ReadAllText(inputSMTMethod.FullName);

        using (Context ctx = new Context())
        {
            BoolExpr[] methodConstraints = ctx.ParseSMTLIB2String(smt2MethodContent, null, null, null, null);
            MethodConverter m = new MethodConverter();
            string methodName = "Constraints";
            var methodDef = m.Convert(methodName, methodConstraints);

            if (methodDef.ResultParameter == null)
            {
                throw new Exception("Missing result parameter");
            }

            List<MethodDefinition> methods = m.SafeDivSorts.Select(s => SafeDiv.GetSafeDivMethodCode(s)).ToList();
            methods.Add(methodDef);

            List<Expression> freeVariables = methodDef.Parameters.Select(p => p.Variable.ToExpression()).Cast<Expression>().ToList();
            List<FunctionDefinition> functions = new List<FunctionDefinition>();
            if (smt2FunctionContent != null)
            {
                FunctionConverter f = new FunctionConverter();
                string functionName = "Spec";
                BoolExpr[] functionConstraints = ctx.ParseSMTLIB2String(smt2FunctionContent, null, null, null, null);
                var functionDef = f.Convert(functionName, functionConstraints);

                functions.AddRange(f.SafeDivSorts.Select(s => SafeDiv.GetSafeDivFunctionCode(s)));
                functions.Add(functionDef);


                methodDef.Ensures = new BinaryExpression(new CallExpression(new IdentifierExpression(functionDef.Identifier), freeVariables), Operator.Equal, methodDef.ResultParameter.Variable.ToExpression());
            }

            FunctionConverter requireFunction = new FunctionConverter();
            BoolExpr[] modelConstraints = ctx.ParseSMTLIB2String(smt2ModelContent, null, null, null, null);
            var modelDef = requireFunction.Convert("Model", modelConstraints);
            functions.Add(modelDef);
            methodDef.Requires = new BinaryExpression(new CallExpression(new IdentifierExpression(modelDef.Identifier), freeVariables), Operator.Equal, LiteralExpression.True);

            // Retrieve the SAT value for the given model and constraints.
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
            // Verify that the result matches the model's evaluation.
            Expression expectedValueEquality = new BinaryExpression(methodDef.ResultParameter.Variable.ToExpression(), Operator.Equal, expectedValue);
            methodDef.Ensures = methodDef.Ensures != null ? new BinaryExpression(methodDef.Ensures, Operator.And, expectedValueEquality) : expectedValueEquality;

            Program program = new Program(new List<Import>(), functions, methods);

            MainGenerator mainGenerator = new MainGenerator();
            mainGenerator.GenerateMain(program, methodDef);

            outputDir.Create();
            File.WriteAllText(Path.Join(new string[] { outputDir.FullName, "compiled.dfy" }), ASTWriter.Serialize(program));
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
