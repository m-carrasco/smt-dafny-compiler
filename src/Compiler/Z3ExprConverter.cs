namespace SDC.Converter;

using Microsoft.Z3;
using SDC.AST;
using SDC.Stubs;
using Z3BoolExpr = Microsoft.Z3.BoolExpr;
using Z3Expr = Microsoft.Z3.Expr;

public class Z3ExprConverter
{

    public static SDC.AST.TypeReference Z3SortToDafny(Sort sort)
    {
        if (sort.SortKind == Z3_sort_kind.Z3_BV_SORT)
        {
            var bvSort = (BitVecSort)sort;
            return new SDC.AST.TypeReference($"bv{bvSort.Size}");
        }

        if (sort.SortKind == Z3_sort_kind.Z3_BOOL_SORT)
        {
            return new SDC.AST.TypeReference("bool");
        }

        throw new NotImplementedException();
    }

    enum ConversionKind
    {
        Method,
        Function
    };

    ConversionKind _kind;
    Func<Microsoft.Z3.Expr, Expression> _childConverter;
    IDictionary<uint, Expression> _cache = new Dictionary<uint, Expression>();
    bool _useSafeDiv = true;

    IDictionary<uint, Expression> _conversionCache = new Dictionary<uint, Expression>();

    public List<VariableDefinition> Parameters = new List<VariableDefinition>();

    // The prelude has to be instantiated according to the types that have been detected.
    // This container stores such types.
    private ISet<TypeReference> _preludeTypes;

    private Z3ExprConverter(ConversionKind conversionKind, ISet<TypeReference> preludeTypes)
    {
        _kind = conversionKind;
        _preludeTypes = preludeTypes;
    }

    /*
        The function translation does not use local variables for intermediate results.
        In this mode, we use the same dafny expression for each Z3 expression on each occurrence. 
    */
    public static Z3ExprConverter CreateFunctionConverter(ISet<TypeReference> preludeTypes)
    {
        var r = new Z3ExprConverter(ConversionKind.Function, preludeTypes);
        r._childConverter = (e) => r.Convert(e);
        return r;
    }

    /*
        The method translation uses local variables to store intermediate computations.
        The childLookup returns the variable names.
        The caller must ensure that the child are processed first.
    */
    public static Z3ExprConverter CreateMethodConverter(Func<Microsoft.Z3.Expr, Expression> childLookup, ISet<TypeReference> preludeTypes)
    {
        var r = new Z3ExprConverter(ConversionKind.Method, preludeTypes);
        r._childConverter = childLookup;
        return r;
    }

    private Expression Slt(uint sortSize, Expression a, Expression b)
    {
        // (define-fun slt ((a (_ BitVec 8)) (b (_ BitVec 8))) Bool
        // (or
        //    (and (bvult #x7f a) (bvult b #x80))  ;; a is negative and b is non-negative
        //    (and 
        //        (not (xor (bvult a #x80) (bvult b #x80)))  ;; a and b have the same sign
        //        (bvult a b))))  ;; compare unsigned if same sign)

        uint n = sortSize;

        Expression aIsNegative = new BinaryExpression(new LiteralExpression((n - 1).ToString()), Operator.Less, a);
        LiteralExpression signMask = new LiteralExpression(((int)Math.Pow(2, n - 1)).ToString());
        Expression bIsNonNegative = new BinaryExpression(b, Operator.Less, signMask);

        Expression aNegBNonNeg = new BinaryExpression(aIsNegative, Operator.And, bIsNonNegative);

        Expression xor = Expression.BooleanXor(new BinaryExpression(a, Operator.Less, signMask), new BinaryExpression(b, Operator.Less, signMask));
        Expression bothSameSign = new UnaryExpression(xor, Operator.BooleanNegation);
        Expression compareUnsigned = new BinaryExpression(a, Operator.Less, b);
        Expression bothSignUnsignedCmp = new BinaryExpression(bothSameSign, Operator.And, compareUnsigned);

        return new BinaryExpression(aNegBNonNeg, Operator.Or, bothSignUnsignedCmp);
    }

    /*
        The function returns a Dafny expression from a Z3 expression.
        In addition, it updates public containers holding the free variables found, etc.

        To process sub-expressions use the _childConverter lambda.

        Make sure the function crashes under unsupported Z3 expressions.
        Otherwise, if it doesn't, debugging will be difficult.
    */
    public Expression Convert(Microsoft.Z3.Expr z3Expr)
    {
        if (_conversionCache.TryGetValue(z3Expr.Id, out Expression result))
        {
            return result;
        }

        SDC.AST.Expression dafnyExpr;
        if (z3Expr is Z3BoolExpr)
        {
            if (z3Expr.IsApp)
            {
                switch (z3Expr.FuncDecl.DeclKind)
                {
                    case Z3_decl_kind.Z3_OP_EQ:
                    case Z3_decl_kind.Z3_OP_UGEQ:
                    case Z3_decl_kind.Z3_OP_UGT:
                    case Z3_decl_kind.Z3_OP_ULT:
                        {
                            var operators = new Dictionary<Z3_decl_kind, SDC.AST.Operator>()
                            {
                                [Z3_decl_kind.Z3_OP_UGEQ] = Operator.GreaterEq,
                                [Z3_decl_kind.Z3_OP_EQ] = Operator.Equal,
                                [Z3_decl_kind.Z3_OP_UGT] = Operator.Greater,
                                [Z3_decl_kind.Z3_OP_ULT] = Operator.Less,
                            };

                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = new SDC.AST.BinaryExpression(a0, operators[z3Expr.FuncDecl.DeclKind], a1);
                        }
                        break;
                    case Z3_decl_kind.Z3_OP_SLT:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = Slt(((BitVecExpr)z3Expr.Args[0]).SortSize, a0, a1);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_UNINTERPRETED:
                        {
                            if (z3Expr.IsConst && z3Expr.NumArgs == 0)
                            {
                                Parameters.Add(new VariableDefinition(new VariableReference(z3Expr.FuncDecl.Name.ToString()), Z3SortToDafny(z3Expr.Sort)));
                                dafnyExpr = Parameters.Last().Variable.ToExpression();
                                break;
                            }
                            throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
                        }
                    case Z3_decl_kind.Z3_OP_TRUE:
                        {
                            dafnyExpr = LiteralExpression.True;
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_FALSE:
                        {
                            dafnyExpr = LiteralExpression.False;
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_ITE:
                        {
                            var conditionExpr = _childConverter(z3Expr.Args[0]);
                            var trueExpr = _childConverter(z3Expr.Args[1]);
                            var falseExpr = _childConverter(z3Expr.Args[2]);
                            dafnyExpr = new SDC.AST.MathIfThenElse(conditionExpr, trueExpr, falseExpr);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_AND:
                        {
                            var child = z3Expr.Args.Select(arg => _childConverter(arg)).ToList();
                            if (child.Count < 2)
                            {
                                throw new NotSupportedException("AND expression has less than two sub-expressions");
                            }
                            dafnyExpr = new SDC.AST.BinaryExpression(child[0], SDC.AST.Operator.And, child[1]);
                            for (int i = 2; i < child.Count; i++)
                            {
                                dafnyExpr = new SDC.AST.BinaryExpression(dafnyExpr, SDC.AST.Operator.And, child[i]);
                            }
                            break;
                        }
                    default:
                        throw new NotImplementedException($"Unknown kind {z3Expr.FuncDecl.DeclKind} {z3Expr.ToString()}");
                }
            }
            else
            {
                throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
            }
        }
        else if (z3Expr is BitVecExpr bvExpr)
        {
            if (z3Expr.IsApp)
            {
                var declKind = z3Expr.FuncDecl.DeclKind;
                switch (declKind)
                {
                    case Z3_decl_kind.Z3_OP_BNOT:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            dafnyExpr = new SDC.AST.UnaryExpression(new SDC.AST.AsExpression(a0, Z3SortToDafny(z3Expr.Sort)), Operator.BitwiseNot);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BSMOD:
                        {
                            // Cast operands to ints because bvs do not have this operator in Dafny.
                            // The result must be casted back to a bv.

                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);

                            var t = new TypeReference("int");
                            dafnyExpr = new SDC.AST.BinaryExpression(new SDC.AST.AsExpression(a0, t), Operator.Mod, new SDC.AST.AsExpression(a1, t));
                            dafnyExpr = new SDC.AST.AsExpression(dafnyExpr, Z3SortToDafny(z3Expr.Sort));
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BAND: // Cast operands to bv (in case they are constants)
                    case Z3_decl_kind.Z3_OP_BXOR:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);

                            var t = Z3SortToDafny(z3Expr.Sort);

                            var operators = new Dictionary<Z3_decl_kind, SDC.AST.Operator>()
                            {
                                [Z3_decl_kind.Z3_OP_BAND] = Operator.BitwiseAnd,
                                [Z3_decl_kind.Z3_OP_BXOR] = Operator.BitwiseXor,
                            };

                            dafnyExpr = new SDC.AST.BinaryExpression(new SDC.AST.AsExpression(a0, t), operators[declKind], new SDC.AST.AsExpression(a1, t));
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BUDIV:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            if (_useSafeDiv)
                            {
                                var t = Z3SortToDafny(z3Expr.Sort);
                                var _safeDivIdentifier = _kind == ConversionKind.Method ? SafeUnsignedDiv.GetSafeDivMethodIdentifier(t) : SafeUnsignedDiv.GetSafeDivFunctionIdentifier(t);
                                dafnyExpr = new SDC.AST.CallExpression(_safeDivIdentifier, new List<Expression>() { a0, a1 });
                                // Instantiate the necessary operations in the prelude for this type.
                                _preludeTypes.Add(Z3SortToDafny(z3Expr.Sort));
                            }
                            else
                            {
                                dafnyExpr = new SDC.AST.BinaryExpression(a0, Operator.Division, a1);
                            }
                        }
                        break;
                    case Z3_decl_kind.Z3_OP_BSDIV:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            var t = Z3SortToDafny(z3Expr.Sort);
                            var _safeDivIdentifier = _kind == ConversionKind.Method ? SafeSignedDiv.GetSafeDivMethodIdentifier(t) : SafeSignedDiv.GetSafeDivFunctionIdentifier(t);
                            dafnyExpr = new SDC.AST.CallExpression(_safeDivIdentifier, new List<Expression>() { a0, a1 });
                            // Instantiate the necessary operations in the prelude for this type.
                            _preludeTypes.Add(Z3SortToDafny(z3Expr.Sort));
                        }
                        break;
                    case Z3_decl_kind.Z3_OP_UNINTERPRETED:
                        {
                            if (z3Expr.IsConst && z3Expr.NumArgs == 0)
                            {
                                Parameters.Add(new VariableDefinition(new VariableReference(z3Expr.FuncDecl.Name.ToString()), Z3SortToDafny(z3Expr.Sort)));
                                dafnyExpr = Parameters.Last().Variable.ToExpression();
                                break;
                            }
                            throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
                        }
                    default:
                        throw new NotImplementedException($"Unknown kind {z3Expr.FuncDecl.DeclKind}");
                }
            }
            else if (z3Expr is BitVecNum bitVecNum)
            {
                dafnyExpr = new LiteralExpression(bitVecNum.UInt64.ToString());
            }
            else
            {
                throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
            }
        }
        else
        {
            throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
        }

        _conversionCache[z3Expr.Id] = dafnyExpr;
        return dafnyExpr;
    }
}
