namespace SDC.Converter;

using Microsoft.Z3;
using SDC.AST;
using SDC.Stubs;
using Z3BoolExpr = Microsoft.Z3.BoolExpr;
using Z3Expr = Microsoft.Z3.Expr;

public class MainGenerator
{

    public void GenerateMain(Program p, MethodDefinition method)
    {
        var imports = new List<Import>() { new Import("opened Std.Wrappers"), new Import("opened Std.FileIO") };
        var attributes = new List<Attribute>() { new Attribute("verify", LiteralExpression.False) };

        var argv = new VariableDefinition(new VariableReference("argv"), new TypeReference("seq<string>"));
        var parameters = new List<VariableDefinition> { argv };

        var res = new VariableDefinition(new VariableReference("res"), new TypeReference("Result<seq<bv8>, string>"));
        var bytes = new VariableDefinition(new VariableReference("bytes"), new TypeReference("seq<bv8>"));
        var sat = new VariableDefinition(new VariableReference("sat"), new TypeReference("bool"));
        var localVariables = new List<VariableDefinition> { res, bytes, sat };

        var statements = new List<Statement>();

        var argvIsTwo = new BinaryExpression(new ModulusExpression(argv.Variable.ToExpression()), Operator.Equal, new LiteralExpression("2"));
        statements.Add(new ExpectStatement(argvIsTwo, new LiteralExpression("\"unexpected argv size\"")));

        var newLine = new LiteralExpression("\"\\n\"");
        //statements.Add(new PrintStatement(new List<Expression>() {argv.Variable.ToExpression(), newLine}));

        var filePath = new IndexExpression(argv.Variable.ToExpression(), new LiteralExpression("1"));
        statements.Add(new AssignmentStatement(res.Variable, new CallExpression(new IdentifierExpression("FileIO.ReadBytesFromFile"), new List<Expression>() { filePath })));

        var successCond = new FieldAccessExpression(res.Variable.ToExpression(), new IdentifierExpression("Success?"));
        Expression message = new LiteralExpression("\"Unexpected failure reading file: \"");
        message = new BinaryExpression(message, Operator.Add, new FieldAccessExpression(res.Variable.ToExpression(), new IdentifierExpression("error")));

        statements.Add(new ExpectStatement(successCond, message));

        Expression readBytesValues = new FieldAccessExpression(res.Variable.ToExpression(), new IdentifierExpression("value"));
        Expression readBytesLen = readBytesValues;
        readBytesLen = new ModulusExpression(readBytesLen);
        int requiredBytes = method.Parameters.Select(p => ConcatBV.RequiredBytes(p.Type)).Sum();
        readBytesLen = new BinaryExpression(readBytesLen, Operator.GreaterEq, new LiteralExpression(requiredBytes.ToString()));
        statements.Add(new ExpectStatement(readBytesLen, new LiteralExpression("\"unexpected input buffer size\"")));

        var methodParameters = method.Parameters.Select(p => new VariableDefinition(new VariableReference("p_" + p.Variable.Identifier), p.Type)).ToList();
        localVariables.AddRange(methodParameters);
        int offset = 0;
        int parameterIndex = 0;

        Dictionary<TypeReference, MethodDefinition> concatMethods = new();
        foreach (VariableDefinition v in method.Parameters)
        {
            var parameterType = v.Type;
            int parameterByteSize = ConcatBV.RequiredBytes(parameterType);

            List<Expression> currentBytes = new List<Expression>();
            for (int i = 0; i < parameterByteSize; i++)
            {
                currentBytes.Add(new IndexExpression(readBytesValues, new LiteralExpression(offset.ToString())));
                offset++;
            }

            Expression sequence = new SequenceExpression(currentBytes);
            statements.Add(new AssignmentStatement(bytes.Variable, sequence));


            if (!concatMethods.TryGetValue(parameterType, out MethodDefinition concatMethod))
            {
                if (parameterType.IsBVType())
                {
                    concatMethod = ConcatBV.GetConcatBVMethodCode(parameterType);
                }
                else if (parameterType.IsBoolType())
                {
                    concatMethod = ConcatBool.GetConcatBoolMethodCode(parameterType);
                }
                else
                {
                    throw new NotSupportedException($"Unsupported parameter type {parameterType.Identifier}");
                }
                concatMethods[parameterType] = concatMethod;
                p.Methods.Add(concatMethod);
            }

            var currentVariable = methodParameters[parameterIndex++];
            statements.Add(new AssignmentStatement(currentVariable.Variable, new CallExpression(new IdentifierExpression(concatMethod.Identifier), new List<Expression>() { bytes.Variable.ToExpression() })));

            statements.Add(new PrintStatement(new List<Expression>() { new LiteralExpression($"\"variable {v.Variable.Identifier}: \""), currentVariable.Variable.ToExpression(), newLine }));
        }

        var methodParametersExpression = methodParameters.Select(v => v.Variable.ToExpression()).Cast<Expression>().ToList();
        statements.Add(new AssignmentStatement(sat.Variable, new CallExpression(new IdentifierExpression(method.Identifier), methodParametersExpression)));
        statements.Add(new PrintStatement(new List<Expression>() { new LiteralExpression("\"sat: \""), sat.Variable.ToExpression(), newLine }));

        var main = new MethodDefinition("Main", parameters, null, null, null, statements, localVariables, new List<Attribute>() { new Attribute("verify", LiteralExpression.False) });

        p.Methods.Add(main);
        p.Imports.Add(new Import("Std.FileIO"));
        p.Imports.Add(new Import("opened Std.Wrappers"));
    }
};
