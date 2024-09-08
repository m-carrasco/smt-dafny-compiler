namespace SDC.Converter;

using Microsoft.Z3;
using SDC.AST;
using Z3BoolExpr = Microsoft.Z3.BoolExpr;
using Z3Expr = Microsoft.Z3.Expr;

public class MethodConverter
{
    private IDictionary<uint, IdentifierExpression> _conversionCache = new Dictionary<uint, IdentifierExpression>();
    private List<VariableDefinition> _localVariables = new List<VariableDefinition>();
    private List<VariableDefinition> _parameters = new List<VariableDefinition>();
    private List<Statement> _statements = new List<Statement>();
    private Z3ExprConverter _exprConverter;
    public List<TypeReference> SafeDivSorts = new();

    public SDC.AST.MethodDefinition Convert(string name, Z3BoolExpr[] assertions)
    {
        _conversionCache = new Dictionary<uint, IdentifierExpression>();
        _localVariables = new List<VariableDefinition>();
        _statements = new List<Statement>();
        // Use the assigned local variable for child expressions.
        _exprConverter = Z3ExprConverter.CreateMethodConverter(e => _conversionCache[e.Id]);
        _parameters = _exprConverter.Parameters;

        foreach (Z3BoolExpr e in assertions)
        {
            IdentifierExpression variableIdentifier = DefineExpression(e);
            var cond = new SDC.AST.BinaryExpression(variableIdentifier, Operator.Equal, LiteralExpression.False);
            IfCodeStatement ifFalse = new(cond, new List<Statement>() { new ReturnStatement(LiteralExpression.False) }, new List<Statement>());
            _statements.Add(ifFalse);
        }

        _statements.Add(new ReturnStatement(LiteralExpression.True));
        _localVariables.Sort((a, b) => a.Variable.Identifier.CompareTo(b.Variable.Identifier));
        var methodDef = new SDC.AST.MethodDefinition(name, _parameters, new VariableDefinition(new VariableReference("sat"), new SDC.AST.TypeReference("bool")), null, null, _statements, _localVariables, new List<Attribute>());

        SafeDivSorts.AddRange(_exprConverter.SafeDivUseSort);

        return methodDef;
    }

    private IdentifierExpression DefineExpression(Z3Expr z3Expr)
    {
        IdentifierExpression result = null;
        if (_conversionCache.TryGetValue(z3Expr.Id, out result))
        {
            return result;
        }

        for (uint i = 0; i < z3Expr.NumArgs; i++)
        {
            Z3Expr e = z3Expr.Args[i];
            DefineExpression(e);
        }

        var dafnyExpr = _exprConverter.Convert(z3Expr);
        SDC.AST.TypeReference dafnyType = Z3ExprConverter.Z3SortToDafny(z3Expr.Sort);
        var variableDef = AssignVariableIdentifier(dafnyType);
        _statements.Add(new AssignmentStatement(variableDef.Variable, dafnyExpr));
        _conversionCache[z3Expr.Id] = variableDef.Variable.ToExpression();
        return _conversionCache[z3Expr.Id];
    }

    private VariableDefinition AssignVariableIdentifier(SDC.AST.TypeReference typeReference)
    {
        VariableDefinition localVariable = new VariableDefinition(new VariableReference($"l{this._localVariables.Count}"), typeReference);
        _localVariables.Add(localVariable);

        return localVariable;
    }
};
