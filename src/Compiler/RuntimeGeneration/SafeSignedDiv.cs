namespace SDC.Stubs;

using SDC.AST;

public class SafeSignedDiv
{
    public static IdentifierExpression GetSafeDivMethodIdentifier(SDC.AST.TypeReference type)
    {
        return new IdentifierExpression("SafeSignedDivMethod_@TYPENAME".Replace("@TYPENAME", type.Identifier));
    }

    public static MethodDefinition GetSafeDivMethodCode(SDC.AST.TypeReference type)
    {
        var xDef = new VariableDefinition(new VariableReference("x"), type);
        var yDef = new VariableDefinition(new VariableReference("y"), type);
        var rDef = new VariableDefinition(new VariableReference("r"), type);

        var parameters = new List<VariableDefinition>() { xDef, yDef };
        var bvSize = type.GetBVSize();
        if (bvSize == 0)
        {
            throw new NotImplementedException("Number of bits is zero.");
        }
        var bvSizeMinusOne = new LiteralExpression((bvSize - 1).ToString());

        var xSignShift = new BinaryExpression(xDef.Variable.ToExpression(), Operator.Shr, bvSizeMinusOne);
        var ySignShift = new BinaryExpression(yDef.Variable.ToExpression(), Operator.Shr, bvSizeMinusOne);

        var xSignIsSet = new BinaryExpression(xSignShift, Operator.Equal, new LiteralExpression("1"));
        var ySignIsSet = new BinaryExpression(ySignShift, Operator.Equal, new LiteralExpression("1"));

        var xByMinusOne = new BinaryExpression(xDef.Variable.ToExpression(), Operator.Multiply, new LiteralExpression("-1"));
        var yByMinusOne = new BinaryExpression(yDef.Variable.ToExpression(), Operator.Multiply, new LiteralExpression("-1"));

        var ifX = new MathIfThenElse(xSignIsSet, xByMinusOne, xDef.Variable.ToExpression());
        var ifY = new MathIfThenElse(ySignIsSet, yByMinusOne, yDef.Variable.ToExpression());

        var callAssignment = new AssignmentStatement(rDef.Variable, new CallExpression(SafeUnsignedDiv.GetSafeDivMethodIdentifier(type), new List<Expression>() { ifX, ifY }));

        var oneNegOperand = new BinaryExpression(new BinaryExpression(xSignShift, Operator.BitwiseXor, ySignShift), Operator.Equal, new LiteralExpression("1"));

        var ifChangeSign = new IfCodeStatement(oneNegOperand, new List<Statement>() { new AssignmentStatement(rDef.Variable, new BinaryExpression(rDef.Variable.ToExpression(), Operator.Multiply, new LiteralExpression("-1"))) }, new List<Statement>() { });

        var statements = new List<Statement>() { callAssignment, ifChangeSign };

        var paramExprs = parameters.Select(p => p.Variable.ToExpression()).ToList().OfType<Expression>().ToList();

        var ensures = new BinaryExpression(new CallExpression(GetSafeDivFunctionIdentifier(type), paramExprs), Operator.Equal, rDef.Variable.ToExpression());
        var methodDef = new MethodDefinition(GetSafeDivMethodIdentifier(type).Identifier, parameters, rDef, null, ensures, statements, new List<VariableDefinition>(), new List<Attribute>() { new Attribute("verify", LiteralExpression.False) });
        return methodDef;
    }

    public static IdentifierExpression GetSafeDivFunctionIdentifier(SDC.AST.TypeReference type)
    {
        return new IdentifierExpression("SafeSignedDivFunction_@TYPENAME".Replace("@TYPENAME", type.Identifier));
    }


    public static FunctionDefinition GetSafeDivFunctionCode(SDC.AST.TypeReference type)
    {
        var xDef = new VariableDefinition(new VariableReference("x"), type);
        var yDef = new VariableDefinition(new VariableReference("y"), type);
        List<VariableDefinition> variableDefinitions = new List<VariableDefinition>() {
            xDef, yDef
        };

        var bvSize = type.GetBVSize();
        if (bvSize == 0)
        {
            throw new NotImplementedException("Number of bits is zero.");
        }
        var bvSizeMinusOne = new LiteralExpression((bvSize - 1).ToString());

        var xSignShift = new BinaryExpression(xDef.Variable.ToExpression(), Operator.Shr, bvSizeMinusOne);
        var ySignShift = new BinaryExpression(yDef.Variable.ToExpression(), Operator.Shr, bvSizeMinusOne);

        var xSignIsSet = new BinaryExpression(xSignShift, Operator.Equal, new LiteralExpression("1"));
        var ySignIsSet = new BinaryExpression(ySignShift, Operator.Equal, new LiteralExpression("1"));

        var xByMinusOne = new BinaryExpression(xDef.Variable.ToExpression(), Operator.Multiply, new LiteralExpression("-1"));
        var yByMinusOne = new BinaryExpression(yDef.Variable.ToExpression(), Operator.Multiply, new LiteralExpression("-1"));

        var ifX = new MathIfThenElse(xSignIsSet, xByMinusOne, xDef.Variable.ToExpression());
        var ifY = new MathIfThenElse(ySignIsSet, yByMinusOne, yDef.Variable.ToExpression());

        var callExpr = new CallExpression(SafeUnsignedDiv.GetSafeDivFunctionIdentifier(type), new List<Expression>() { ifX, ifY });

        var oneNegOperand = new BinaryExpression(new BinaryExpression(xSignShift, Operator.BitwiseXor, ySignShift), Operator.Equal, new LiteralExpression("1"));

        var result = new MathIfThenElse(oneNegOperand, new BinaryExpression(callExpr, Operator.Multiply, new LiteralExpression("-1")), callExpr);

        FunctionDefinition functionDefinition = new FunctionDefinition(GetSafeDivFunctionIdentifier(type).Identifier, variableDefinitions, type, result);
        return functionDefinition;
    }

}
