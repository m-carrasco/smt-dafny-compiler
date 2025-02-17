namespace SDC.Converter;
using Microsoft.Z3;
using SDC.AST;
using Z3BoolExpr = Microsoft.Z3.BoolExpr;

public class FunctionConverter
{
    private List<VariableDefinition> _parameters = new List<VariableDefinition>();
    private Z3ExprConverter? _exprConverter;
    public List<TypeReference> SafeDivSorts = new();
    public List<TypeReference> SafeSignedDivSorts = new();
    public SDC.AST.FunctionDefinition Convert(string name, Z3BoolExpr[] assertions, ISet<TypeReference> preludeTypes)
    {
        _exprConverter = Z3ExprConverter.CreateFunctionConverter(preludeTypes, assertions.OfType<Microsoft.Z3.Expr>().ToList());
        _parameters = _exprConverter.Parameters;

        var simplifiedAssertions = Simplifier.RemoveTrueAssertions(assertions);
        var expressions = simplifiedAssertions.Count() > 0 ? simplifiedAssertions.Select(e => _exprConverter.Convert(e)) : new List<Expression>() { LiteralExpression.True };

        Expression expression = expressions.ElementAt(0);
        for (int i = 1; i < expressions.Count(); i++)
        {
            expression = new BinaryExpression(expression, Operator.BooleanAnd, expressions.ElementAt(i));
        }

        _parameters.Sort((a, b) => a.Variable.Identifier.CompareTo(b.Variable.Identifier));
        var functionDef = new SDC.AST.FunctionDefinition(name, _parameters, new SDC.AST.TypeReference("bool"), expression);
        return functionDef;
    }
};
