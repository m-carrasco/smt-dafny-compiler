namespace SDC.Stubs;
using SDC.AST;
public class ConcatBool{


    public static IdentifierExpression GetConcatBVMethodIdentifier(SDC.AST.TypeReference type){
        return new IdentifierExpression("ConcatBool_@TYPENAME".Replace("@TYPENAME", type.Identifier));
    }

    public static MethodDefinition GetConcatBoolMethodCode(SDC.AST.TypeReference type){
        string name = GetConcatBVMethodIdentifier(type).Identifier;

        var sDef = new VariableDefinition(new VariableReference("s"), new TypeReference("seq<bv8>"));
        var rDef = new VariableDefinition(new VariableReference("r"), type);

        int requiredBytes = ConcatBV.RequiredBytes(type);
        Expression requires = null;
        var statements = new List<Statement>
        {
            new ExpectStatement(new BinaryExpression(new ModulusExpression(sDef.Variable.ToExpression()), Operator.GreaterEq, new LiteralExpression(requiredBytes.ToString())), new LiteralExpression("\"unexpected size\"")),
        };
        
        Expression indexExpr = new IndexExpression(sDef.Variable.ToExpression(), new LiteralExpression("0"));
        Expression condition = new BinaryExpression(indexExpr, Operator.Equal, new LiteralExpression("0"));

        statements.Add(new ReturnStatement(new MathIfThenElse(condition, new LiteralExpression("false"), new LiteralExpression("true"))));

        return new MethodDefinition(name, new List<VariableDefinition>() {sDef}, rDef, requires, null, statements, new List<VariableDefinition>() {} , new List<Attribute>(){new Attribute("verify", LiteralExpression.False)});
    }

}