﻿namespace SDC.Converter;
using Microsoft.Z3;
using SDC.AST;
using Z3BoolExpr = Microsoft.Z3.BoolExpr;

public class FunctionConverter
{
    private List<VariableDefinition> _parameters = new List<VariableDefinition>();
    private Z3ExprConverter? _exprConverter;
    public List<TypeReference> SafeDivSorts = new();
    public SDC.AST.FunctionDefinition Convert(string name, Z3BoolExpr[] assertions)
    {
        _exprConverter = Z3ExprConverter.CreateFunctionConverter();
        _parameters = _exprConverter.Parameters;
        var expressions = assertions.Count() > 0 ? assertions.Select(e => _exprConverter.Convert(e)) : new List<Expression>() { LiteralExpression.True };

        Expression expression = expressions.ElementAt(0);
        for (int i = 1; i < expressions.Count(); i++)
        {
            expression = new BinaryExpression(expression, Operator.And, expressions.ElementAt(i));
        }

        var functionDef = new SDC.AST.FunctionDefinition(name, _parameters, new SDC.AST.TypeReference("bool"), expression);
        SafeDivSorts.AddRange(_exprConverter.SafeDivUseSort);
        return functionDef;
    }
};
