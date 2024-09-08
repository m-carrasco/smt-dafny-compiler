namespace SDC.Stubs;

using System.Numerics;
using SDC.AST;

public class SafeDiv
{
    public static IdentifierExpression GetSafeDivMethodIdentifier(SDC.AST.TypeReference type)
    {
        return new IdentifierExpression("SafeDivMethod_@TYPENAME".Replace("@TYPENAME", type.Identifier));
    }

    private static LiteralExpression MaxValueBits(TypeReference type)
    {
        string identifier = type.Identifier;
        if (identifier.StartsWith("bv"))
        {
            int bits = int.Parse(identifier.Substring(2));
            BigInteger maxValue = BigInteger.Pow(2, bits) - 1;
            return new LiteralExpression(maxValue.ToString());
        }

        throw new ArgumentException("BV type expected");
    }
    public static MethodDefinition GetSafeDivMethodCode(SDC.AST.TypeReference type)
    {
        var xDef = new VariableDefinition(new VariableReference("x"), type);
        var yDef = new VariableDefinition(new VariableReference("y"), type);
        var rDef = new VariableDefinition(new VariableReference("r"), type);

        var parameters = new List<VariableDefinition>() { xDef, yDef };

        var division = new BinaryExpression(xDef.Variable.ToExpression(), Operator.Division, yDef.Variable.ToExpression());
        var condition = new BinaryExpression(yDef.Variable.ToExpression(), Operator.NotEqual, LiteralExpression.Zero);
        var maxValue = MaxValueBits(type);
        var ifThenElse = new MathIfThenElse(condition, division, maxValue);

        var ensures = new BinaryExpression(ifThenElse, Operator.Equal, rDef.Variable.ToExpression());

        var statement = new IfCodeStatement(condition, new List<Statement>() { new ReturnStatement(division) }, new List<Statement>() { new ReturnStatement(maxValue) });
        var statements = new List<Statement>() { statement };

        var methodDef = new MethodDefinition(GetSafeDivMethodIdentifier(type).Identifier, parameters, rDef, null, ensures, statements, new List<VariableDefinition>(), new List<Attribute>() { new Attribute("verify", LiteralExpression.False) });

        return methodDef;
    }


    public static IdentifierExpression GetSafeDivFunctionIdentifier(SDC.AST.TypeReference type)
    {
        return new IdentifierExpression("SafeDivFunction_@TYPENAME".Replace("@TYPENAME", type.Identifier));
    }


    public static FunctionDefinition GetSafeDivFunctionCode(SDC.AST.TypeReference type)
    {
        var xDef = new VariableDefinition(new VariableReference("x"), type);
        var yDef = new VariableDefinition(new VariableReference("y"), type);
        List<VariableDefinition> variableDefinitions = new List<VariableDefinition>() {
            xDef, yDef
        };
        var condition = new BinaryExpression(yDef.Variable.ToExpression(), Operator.NotEqual, LiteralExpression.Zero);
        var ifThenElse = new MathIfThenElse(condition, new BinaryExpression(xDef.Variable.ToExpression(), Operator.Division, yDef.Variable.ToExpression()), MaxValueBits(type));
        FunctionDefinition functionDefinition = new FunctionDefinition(GetSafeDivFunctionIdentifier(type).Identifier, variableDefinitions, type, ifThenElse);
        return functionDefinition;
    }

}
