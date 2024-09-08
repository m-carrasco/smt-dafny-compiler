using System;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Z3;
using SDC.AST;
using SDC.Converter;
using SDC.Stubs;

namespace SDC.CLI;

class SDC
{
    static void Compile(FileInfo inputSMT, DirectoryInfo outputDir)
    {
        string smt2Content = File.ReadAllText(inputSMT.FullName);

        using (Context ctx = new Context())
        {
            BoolExpr[] constraints = ctx.ParseSMTLIB2String(smt2Content, null, null, null, null);

            MethodConverter m = new MethodConverter();
            string methodName = "Constraints";
            var methodDef = m.Convert(methodName, constraints);

            if (methodDef.ResultParameter == null)
            {
                throw new Exception("Missing result parameter");
            }

            List<MethodDefinition> methods = m.SafeDivSorts.Select(s => SafeDiv.GetSafeDivMethodCode(s)).ToList();
            methods.Add(methodDef);

            FunctionConverter f = new FunctionConverter();
            string functionName = "Spec";
            var functionDef = f.Convert(functionName, constraints);

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

    static async Task<int> Main(string[] args)
    {
        var inputOption = new Option<FileInfo>(
            name: "--input-smt2",
            description: "The input SMT2 file for Dafny translation.")
        {
            IsRequired = true
        };

        var outputOption = new Option<DirectoryInfo>(
            name: "--output-dir",
            description: "Output directory for the Dafny translation.")
        {
            IsRequired = true
        };

        var rootCommand = new RootCommand("The SMT Dafny Compiler (SDC)");
        rootCommand.AddOption(inputOption);
        rootCommand.AddOption(outputOption);

        rootCommand.SetHandler((inputSMT, outputDir) =>
        {
            if (!inputSMT.Exists)
            {
                Console.Error.WriteLine($"Error: The input file '{inputSMT.FullName}' does not exist.");
                return Task.FromResult(1);
            }

            if (outputDir.Exists)
            {
                Console.Error.WriteLine($"Error: The output directory '{outputDir.FullName}' already exists.");
                return Task.FromResult(1);
            }

            // Proceed with the rest of your application logic here
            Compile(inputSMT, outputDir);

            return Task.FromResult(0);
        },
        inputOption, outputOption);

        return await rootCommand.InvokeAsync(args);
    }
}
