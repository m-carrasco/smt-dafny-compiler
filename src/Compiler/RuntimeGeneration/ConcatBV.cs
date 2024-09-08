namespace SDC.Stubs;
using System.Numerics;
using SDC.AST;
public class ConcatBV
{

    public static int RequiredBytes(TypeReference type)
    {
        string identifier = type.Identifier;
        if (type.IsBVType())
        {
            int bits = int.Parse(identifier.Substring(2));
            return (bits + 7) / 8;
        }

        if (type.IsBoolType())
        {
            return 1;
        }

        throw new ArgumentException($"Unexpected type expected {identifier}");
    }

    public static IdentifierExpression GetConcatBVMethodIdentifier(SDC.AST.TypeReference type)
    {
        return new IdentifierExpression("ConcatBV_@TYPENAME".Replace("@TYPENAME", type.Identifier));
    }

    /*

    method {:verify false} Concat_bv32(s: seq<bv8>) returns (r: bv32)
    {
        expect |s| >= 4, "unexpected size";
        r := 0;
        r := r | (s[0] as bv32) << 0; 
        r := r | (s[1] as bv32) << 8; 
        r := r | (s[2] as bv32) << 16;
        r := r | (s[3] as bv32) << 24;
    }

    */

    public static MethodDefinition GetConcatBVMethodCode(SDC.AST.TypeReference type)
    {
        string name = GetConcatBVMethodIdentifier(type).Identifier;

        var sDef = new VariableDefinition(new VariableReference("s"), new TypeReference("seq<bv8>"));
        var rDef = new VariableDefinition(new VariableReference("r"), type);

        int requiredBytes = RequiredBytes(type);
        Expression requires = null;
        var statements = new List<Statement>
        {
            new ExpectStatement(new BinaryExpression(new ModulusExpression(sDef.Variable.ToExpression()), Operator.GreaterEq, new LiteralExpression(requiredBytes.ToString())), new LiteralExpression("\"unexpected size\"")),
            new AssignmentStatement(rDef.Variable, LiteralExpression.Zero)
        };

        int pow = 0;
        for (int i = 0; i < requiredBytes; i++)
        {
            Expression indexExpr = new IndexExpression(sDef.Variable.ToExpression(), new LiteralExpression(i.ToString()));
            var operations = new BinaryExpression(new AsExpression(indexExpr, type), Operator.Shl, new LiteralExpression(pow.ToString()));
            var current = new BinaryExpression(rDef.Variable.ToExpression(), Operator.BitwiseOr, operations);
            statements.Add(new AssignmentStatement(rDef.Variable, current));
            pow += 8;
        }

        return new MethodDefinition(name, new List<VariableDefinition>() { sDef }, rDef, requires, null, statements, new List<VariableDefinition>() { }, new List<Attribute>() { new Attribute("verify", LiteralExpression.False) });
    }

}
