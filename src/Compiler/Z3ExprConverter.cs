namespace SDC.Converter;

using System.Numerics;
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

    private Dictionary<Z3Expr, VariableDefinition> _freeVariables = new Dictionary<Z3Expr, VariableDefinition>();
    public List<VariableDefinition> Parameters => _freeVariables.Values.ToList();

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
    public static Z3ExprConverter CreateFunctionConverter(ISet<TypeReference> preludeTypes, List<Z3Expr> inputExpressions)
    {
        var r = new Z3ExprConverter(ConversionKind.Function, preludeTypes);
        r._childConverter = (e) => r.Convert(e);
        r.FindFreeVariables(inputExpressions);
        return r;
    }

    /*
        The method translation uses local variables to store intermediate computations.
        The childLookup returns the variable names.
        The caller must ensure that the child are processed first.
    */
    public static Z3ExprConverter CreateMethodConverter(Func<Microsoft.Z3.Expr, Expression> childLookup, ISet<TypeReference> preludeTypes, List<Z3Expr> inputExpressions)
    {
        var r = new Z3ExprConverter(ConversionKind.Method, preludeTypes);
        r._childConverter = childLookup;
        r.FindFreeVariables(inputExpressions);
        return r;
    }

    // We must find the free variables before optimizing the expressions that are translated.
    // Otherwise, we may accidentally erase unused variables.
    public void FindFreeVariables(List<Z3Expr> expressions)
    {
        HashSet<Z3Expr> freeVars = new HashSet<Z3Expr>();
        HashSet<Z3Expr> visitedVars = new HashSet<Z3Expr>();
        expressions.ForEach(expr => FreeVariables.CollectFreeVariables(expr, freeVars, visitedVars));

        foreach (Z3Expr z3FreeVar in freeVars)
        {
            VariableDefinition variableDefinition = new VariableDefinition(new VariableReference(z3FreeVar.FuncDecl.Name.ToString()), Z3SortToDafny(z3FreeVar.Sort));
            _freeVariables.Add(z3FreeVar, variableDefinition);
        }
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
        var targetType = new TypeReference($"bv{n}");
        ulong nonSignMask = (1UL << (int)(sortSize - 1)) - 1;

        var dafnyNonSignMask = new AsExpression(new LiteralExpression(nonSignMask.ToString()), targetType);
        Expression aIsNegative = new BinaryExpression(dafnyNonSignMask, Operator.Less, a);
        var signMask = new AsExpression(new LiteralExpression(BigInteger.Pow(2, (int)n - 1).ToString()), targetType);
        Expression bIsNonNegative = new BinaryExpression(b, Operator.Less, signMask);

        Expression aNegBNonNeg = new BinaryExpression(aIsNegative, Operator.BooleanAnd, bIsNonNegative);

        Expression xor = Expression.BooleanXor(new BinaryExpression(a, Operator.Less, signMask), new BinaryExpression(b, Operator.Less, signMask));
        Expression bothSameSign = new UnaryExpression(xor, Operator.BooleanNegation);
        Expression compareUnsigned = new BinaryExpression(a, Operator.Less, b);
        Expression bothSignUnsignedCmp = new BinaryExpression(bothSameSign, Operator.BooleanAnd, compareUnsigned);

        return new BinaryExpression(aNegBNonNeg, Operator.BooleanOr, bothSignUnsignedCmp);
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
                var declKind = z3Expr.FuncDecl.DeclKind;
                switch (declKind)
                {
                    case Z3_decl_kind.Z3_OP_EQ:
                    case Z3_decl_kind.Z3_OP_DISTINCT:
                    case Z3_decl_kind.Z3_OP_UGEQ:
                    case Z3_decl_kind.Z3_OP_UGT:
                    case Z3_decl_kind.Z3_OP_ULT:
                    case Z3_decl_kind.Z3_OP_ULEQ:
                    case Z3_decl_kind.Z3_OP_AND:
                    case Z3_decl_kind.Z3_OP_OR:
                        {
                            var operators = new Dictionary<Z3_decl_kind, SDC.AST.Operator>()
                            {
                                [Z3_decl_kind.Z3_OP_UGEQ] = Operator.GreaterEq,
                                [Z3_decl_kind.Z3_OP_ULEQ] = Operator.LessEq,
                                [Z3_decl_kind.Z3_OP_EQ] = Operator.Equal,
                                [Z3_decl_kind.Z3_OP_UGT] = Operator.Greater,
                                [Z3_decl_kind.Z3_OP_ULT] = Operator.Less,
                                [Z3_decl_kind.Z3_OP_DISTINCT] = Operator.NotEqual,
                                [Z3_decl_kind.Z3_OP_AND] = Operator.BooleanAnd,
                                [Z3_decl_kind.Z3_OP_OR] = Operator.BooleanOr,
                            };

                            if (z3Expr.NumArgs != 2)
                            {
                                throw new NotSupportedException("The expression has less than two sub-expressions");
                            }

                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = new SDC.AST.BinaryExpression(a0, operators[z3Expr.FuncDecl.DeclKind], a1);
                        }
                        break;
                    case Z3_decl_kind.Z3_OP_XOR:
                        {
                            if (z3Expr.NumArgs != 2)
                            {
                                throw new NotSupportedException("The expression has less than two sub-expressions");
                            }

                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = Expression.BooleanXor(a0, a1);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_SLT:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = Slt(((BitVecExpr)z3Expr.Args[0]).SortSize, a0, a1);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_SLEQ:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = new UnaryExpression(Slt(((BitVecExpr)z3Expr.Args[0]).SortSize, a1, a0), Operator.BooleanNegation);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_SGT:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = Slt(((BitVecExpr)z3Expr.Args[0]).SortSize, a1, a0);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_SGEQ:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = new UnaryExpression(Slt(((BitVecExpr)z3Expr.Args[0]).SortSize, a0, a1), Operator.BooleanNegation);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_UNINTERPRETED:
                        {
                            if (z3Expr.IsConst && z3Expr.NumArgs == 0)
                            {
                                // If this map access is invalid it is because FindFreeVariables was not called or failed
                                dafnyExpr = _freeVariables[z3Expr].Variable.ToExpression();
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
                    case Z3_decl_kind.Z3_OP_NOT:
                        {
                            var condition = _childConverter(z3Expr.Args[0]);

                            dafnyExpr = new UnaryExpression(condition, Operator.BooleanNegation);
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
                    case Z3_decl_kind.Z3_OP_BNEG:
                        {

                            var operators = new Dictionary<Z3_decl_kind, SDC.AST.Operator>()
                            {
                                [Z3_decl_kind.Z3_OP_BNOT] = Operator.BitwiseNot,
                                [Z3_decl_kind.Z3_OP_BNEG] = Operator.BitwiseNeg,
                            };

                            var a0 = _childConverter(z3Expr.Args[0]);
                            dafnyExpr = new SDC.AST.UnaryExpression(new SDC.AST.AsExpression(a0, Z3SortToDafny(z3Expr.Sort)), operators[declKind]);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BUREM:
                        {
                            // Cast operands to ints because bvs do not have this operator in Dafny.
                            // The result must be casted back to a bv.

                            var t = new TypeReference("int");
                            var a0 = new SDC.AST.AsExpression(_childConverter(z3Expr.Args[0]), t);
                            var a1 = new SDC.AST.AsExpression(_childConverter(z3Expr.Args[1]), t);
                            dafnyExpr = new SDC.AST.BinaryExpression(a0, Operator.Mod, a1);
                            dafnyExpr = new MathIfThenElse(new SDC.AST.BinaryExpression(a1, Operator.Equal, LiteralExpression.Zero), a0, dafnyExpr);
                            dafnyExpr = new SDC.AST.AsExpression(dafnyExpr, Z3SortToDafny(z3Expr.Sort));
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BAND: // Cast operands to bv (in case they are constants)
                    case Z3_decl_kind.Z3_OP_BXOR:
                    case Z3_decl_kind.Z3_OP_BADD:
                    case Z3_decl_kind.Z3_OP_BSUB:
                    case Z3_decl_kind.Z3_OP_BMUL:
                    case Z3_decl_kind.Z3_OP_BOR:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);

                            var t = Z3SortToDafny(z3Expr.Sort);

                            var operators = new Dictionary<Z3_decl_kind, SDC.AST.Operator>()
                            {
                                [Z3_decl_kind.Z3_OP_BAND] = Operator.BitwiseAnd,
                                [Z3_decl_kind.Z3_OP_BOR] = Operator.BitwiseOr,
                                [Z3_decl_kind.Z3_OP_BXOR] = Operator.BitwiseXor,
                                [Z3_decl_kind.Z3_OP_BADD] = Operator.Add,
                                [Z3_decl_kind.Z3_OP_BSUB] = Operator.Minus,
                                [Z3_decl_kind.Z3_OP_BMUL] = Operator.Multiply,
                            };

                            dafnyExpr = new SDC.AST.BinaryExpression(new SDC.AST.AsExpression(a0, t), operators[declKind], new SDC.AST.AsExpression(a1, t));
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BCOMP:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);

                            var t = Z3SortToDafny(z3Expr.Args[0].Sort);

                            var eq = new BinaryExpression(new AsExpression(a0, t), Operator.Equal, new AsExpression(a1, t));

                            dafnyExpr = new MathIfThenElse(new BinaryExpression(eq, Operator.Equal, LiteralExpression.True), new AsExpression(LiteralExpression.One, new TypeReference("bv1")), new AsExpression(LiteralExpression.Zero, new TypeReference("bv1")));
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_BSHL:
                    case Z3_decl_kind.Z3_OP_BLSHR:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);

                            var t = Z3SortToDafny(z3Expr.Sort);

                            var operators = new Dictionary<Z3_decl_kind, SDC.AST.Operator>()
                            {
                                [Z3_decl_kind.Z3_OP_BSHL] = Operator.Shl,
                                [Z3_decl_kind.Z3_OP_BLSHR] = Operator.Shr
                            };

                            // Only cast the LHS
                            dafnyExpr = new SDC.AST.BinaryExpression(new SDC.AST.AsExpression(a0, t), operators[declKind], a1);
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
                                // If this map access is invalid it is because FindFreeVariables was not called or failed
                                dafnyExpr = _freeVariables[z3Expr].Variable.ToExpression();
                                break;
                            }
                            throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
                        }
                    case Z3_decl_kind.Z3_OP_ITE:
                        {
                            var condExpr = _childConverter(z3Expr.Args[0]);
                            var trueExpr = _childConverter(z3Expr.Args[1]);
                            var falseExpr = _childConverter(z3Expr.Args[2]);

                            dafnyExpr = new MathIfThenElse(condExpr, trueExpr, falseExpr);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_EXTRACT:
                        {
                            //Our translation follows this:
                            //method Extract(x: bv32, i: int, j: int) returns (res: bv3)
                            //{
                            //  var mask : bv32;
                            //  mask := ( (1 as bv32) << (i - j + 1)) - 1;  // Mask to isolate the relevant bits
                            //  res := (((x >> j) & (mask as bv32)) as int) as bv3;             // Shift and mask to extract the bits
                            //}

                            var high = new LiteralExpression(z3Expr.FuncDecl.Parameters[0].Int.ToString());
                            var low = new LiteralExpression(z3Expr.FuncDecl.Parameters[1].Int.ToString());
                            var targetBVSort = Z3SortToDafny(z3Expr.Args[0].Sort);
                            var targetBV = _childConverter(z3Expr.Args[0]);

                            var shiftLHS = new AsExpression(LiteralExpression.One, targetBVSort);
                            var shiftRHS = new BinaryExpression(new BinaryExpression(high, Operator.Minus, low), Operator.Add, LiteralExpression.One);
                            var shift = new BinaryExpression(shiftLHS, Operator.Shl, shiftRHS);
                            var mask = new BinaryExpression(shift, Operator.Minus, LiteralExpression.One);

                            Expression extract = new BinaryExpression(targetBV, Operator.Shr, low);
                            extract = new BinaryExpression(extract, Operator.BitwiseAnd, new AsExpression(mask, targetBVSort));
                            extract = new AsExpression(extract, new TypeReference("int"));
                            extract = new AsExpression(extract, Z3SortToDafny(z3Expr.Sort));
                            dafnyExpr = extract;
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_ROTATE_LEFT:
                    case Z3_decl_kind.Z3_OP_ROTATE_RIGHT:
                        {
                            var rotateBits = new LiteralExpression(z3Expr.FuncDecl.Parameters[0].Int.ToString());
                            var targetBV = _childConverter(z3Expr.Args[0]);
                            var targetBVSort = Z3SortToDafny(z3Expr.Args[0].Sort);
                            targetBV = new AsExpression(targetBV, targetBVSort);

                            var mode = declKind == Z3_decl_kind.Z3_OP_ROTATE_LEFT ? RotateMode.LEFT : RotateMode.RIGHT;
                            dafnyExpr = new RotateExpression(targetBV, rotateBits, mode);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_CONCAT:
                        {
                            var totalBits = ((BitVecSort)z3Expr.Sort).Size;
                            dafnyExpr = Concat(totalBits, new Queue<Z3Expr>(z3Expr.Args), totalBits);
                            break;
                        }
                    case Z3_decl_kind.Z3_OP_ZERO_EXT:
                        {
                            var totalBits = ((BitVecSort)z3Expr.Sort).Size;
                            var childExpressionSize = ((BitVecSort)z3Expr.Args[0].Sort).Size;
                            dafnyExpr = ZeroExtend(totalBits, childExpressionSize, _childConverter(z3Expr.Args[0]));
                            break;
                        }
                    default:
                        throw new NotImplementedException($"Unknown kind {z3Expr.FuncDecl.DeclKind}");
                }
            }
            else if (z3Expr is BitVecNum bitVecNum)
            {
                dafnyExpr = new AsExpression(new LiteralExpression(bitVecNum.UInt64.ToString()), new TypeReference($"bv{bitVecNum.SortSize}"));
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

    private Expression ZeroExtend(uint totalBits, uint childTotalBits, Expression childExpr)
    {
        var totalBitsType = new TypeReference($"bv{totalBits}");
        var childExpression = new AsExpression(childExpr, totalBitsType);

        Expression dafnyExpr = LiteralExpression.Zero;
        dafnyExpr = new AsExpression(dafnyExpr, totalBitsType);

        dafnyExpr = new BinaryExpression(dafnyExpr, Operator.Shl, new LiteralExpression(childTotalBits.ToString()));
        dafnyExpr = new BinaryExpression(dafnyExpr, Operator.BitwiseOr, childExpression);
        return dafnyExpr;
    }

    private Expression OneExtend(uint totalBits, uint childTotalBits, Expression childExpr)
    {
        var totalBitsType = new TypeReference($"bv{totalBits}");
        var childExpression = new AsExpression(childExpr, totalBitsType);

        uint oneTotalBits = totalBits - childTotalBits;

        var extendBitsType = new TypeReference($"bv{oneTotalBits}");
        Expression dafnyExpr = LiteralExpression.Zero;
        dafnyExpr = new AsExpression(dafnyExpr, extendBitsType);

        dafnyExpr = new BinaryExpression(dafnyExpr, Operator.Minus, new AsExpression(LiteralExpression.One, extendBitsType));
        dafnyExpr = new AsExpression(dafnyExpr, totalBitsType);

        dafnyExpr = new BinaryExpression(dafnyExpr, Operator.Shl, new LiteralExpression(childTotalBits.ToString()));
        dafnyExpr = new BinaryExpression(dafnyExpr, Operator.BitwiseOr, childExpression);
        return dafnyExpr;
    }

    private Expression Concat(uint totalBits, Queue<Z3Expr> expressions, uint expressionsBits)
    {
        var bvAZ3 = expressions.Dequeue();
        var bvA = _childConverter(bvAZ3);
        uint bvASize = ((BitVecSort)bvAZ3.Sort).Size;

        Expression result = new AsExpression(bvA, new TypeReference($"bv{totalBits}"));

        if (expressions.Count == 0)
        {
            return result;
        }

        uint remainingBits = expressionsBits - bvASize;
        result = new BinaryExpression(result, Operator.Shl, new LiteralExpression(remainingBits.ToString()));

        result = new BinaryExpression(result, Operator.BitwiseOr, Concat(totalBits, expressions, remainingBits));

        return result;
    }
}
