using System.CodeDom.Compiler;
using SDC.AST;
using Microsoft.Z3;

namespace SDC.CompilerTest;

[TestClass]
public class UnitTest1
{
    [TestMethod]
    public void BuildAST()
    {
        /*
            method Formula(x: bv128, y: bv128) returns (sat : bool)
                // Ensure that the implementation matches the spec.
                ensures MathematicalFormula(x, y) == sat
            {
                sat := x > y;
                if (sat == false){
                    return false;
                }

                if (y == 0) { 
                    return false;
                }

                sat := x / y > 10;
                
                if (sat == false){
                    return false;
                }

                return true;
            }
        */
        TypeReference bvType = new TypeReference("bv128");
        TypeReference boolType = new TypeReference("bool");

        VariableReference x = new VariableReference("x");
        VariableReference y = new VariableReference("y");
        List<VariableDefinition> parameters = new List<VariableDefinition>{   new VariableDefinition(x, bvType),
                                                            new VariableDefinition(y, bvType)};
        VariableDefinition resultParameter = new VariableDefinition(new VariableReference("sat"), boolType);
        Expression? requires = null;

        List<Statement> statements = new List<Statement>();
        Expression xGreaterY = new BinaryExpression(x.ToExpression(), Operator.Greater, y.ToExpression());
        statements.Add(new AssignmentStatement(resultParameter.Variable, xGreaterY));

        Expression satIsFalse = new BinaryExpression(resultParameter.Variable.ToExpression(), Operator.Equal, LiteralExpression.False);
        ReturnStatement returnFalse = new ReturnStatement(LiteralExpression.False);

        IfCodeStatement ifSatIsZero = new IfCodeStatement(satIsFalse, new List<Statement>() {returnFalse}, new List<Statement>());
        statements.Add(ifSatIsZero);

        Expression yIsZero = new BinaryExpression(y.ToExpression(), Operator.Equal, LiteralExpression.Zero);

        IfCodeStatement ifYIsZero = new IfCodeStatement(yIsZero, new List<Statement>() {returnFalse}, new List<Statement>());
        statements.Add(ifYIsZero);

        BinaryExpression division = new BinaryExpression(x.ToExpression(), Operator.Division, y.ToExpression());
        BinaryExpression greaterTen = new BinaryExpression(division, Operator.Greater, new LiteralExpression("10"));
        statements.Add(new AssignmentStatement(resultParameter.Variable, greaterTen));
        statements.Add(ifSatIsZero);

        statements.Add(new ReturnStatement(LiteralExpression.True));

        Expression ifThenElse = new MathIfThenElse(new BinaryExpression(y.ToExpression(), Operator.NotEqual, LiteralExpression.Zero), greaterTen, LiteralExpression.False);
        Expression expression = new BinaryExpression(xGreaterY, Operator.And, ifThenElse);
        FunctionDefinition functionDefinition = new FunctionDefinition("MathFormula", parameters, boolType, expression);

        Expression ensures = new BinaryExpression(new CallExpression(functionDefinition.ToExpression(), new List<Expression>() {x.ToExpression(), y.ToExpression()} ), Operator.Equal, resultParameter.Variable.ToExpression());

        var methodDef = new MethodDefinition("Formula", parameters, resultParameter, requires, ensures, statements, new List<VariableDefinition>());

        Program p = new Program(new List<FunctionDefinition> {functionDefinition}, new List<MethodDefinition> {methodDef});

        string expected=@"function MathFormula(x : bv128, y : bv128) : bool
{
    x > y && if y != 0 then x / y > 10 else false 
}

method Formula(x : bv128, y : bv128) returns (sat : bool)
    ensures MathFormula(x, y) == sat
{
    sat := x > y;
    if (sat == false) {
        return false;
    }
    if (y == 0) {
        return false;
    }
    sat := x / y > 10;
    if (sat == false) {
        return false;
    }
    return true;
}

";
        Assert.AreEqual(expected.Trim().Replace("\r\n", "\n"), ASTWriter.Serialize(p).Trim().Replace("\r\n", "\n"));
    }

    [TestMethod]
    public void ConvertToMethod(){
        string smt2 = @"(declare-fun x () (_ BitVec 32))
                    (declare-fun y () (_ BitVec 32))
                    (assert (bvuge x y))
                    (assert (bvuge (bvudiv x y) (_ bv10 32)))
                    (check-sat)
                    (exit)";
        
        using (Context ctx = new Context())
        {
            BoolExpr[] constraints = ctx.ParseSMTLIB2String(smt2, null, null, null, null);

            MethodConverter m = new MethodConverter();
            List<Sort> safeDivSorts = new List<Sort>();
            var methodDef = m.Convert("Constraints", constraints, safeDivSorts);

            List<MethodDefinition> methods = new List<MethodDefinition>();
            foreach (var sort in safeDivSorts){
                methods.Add(SafeDiv.GetSafeDivMethodCode(Z3ExprConverter.Z3SortToDafny(sort)));
            }
            methods.Add(methodDef);

            FunctionConverter f = new FunctionConverter();
            List<Sort> safeDivSortFunction = new List<Sort>();
            var functionDef = f.Convert("Spec", constraints, safeDivSortFunction);
            var functions = new List<FunctionDefinition>();
            foreach (var sort in safeDivSortFunction){
                functions.Add(SafeDiv.GetSafeDivFunctionCode(Z3ExprConverter.Z3SortToDafny(sort)));
            }
            functions.Add(functionDef);

            List<Expression> ensureParams = methodDef.Parameters.Select(p => p.Variable.ToExpression()).Cast<Expression>().ToList();

            methodDef.Ensures = new BinaryExpression(new CallExpression(new IdentifierExpression(functionDef.Identifier), ensureParams), Operator.Equal, methodDef.ResultParameter.Variable.ToExpression());
            Program program = new Program(functions, methods);

            Console.WriteLine(ASTWriter.Serialize(program));
        }

        throw new NotImplementedException();
    }
}