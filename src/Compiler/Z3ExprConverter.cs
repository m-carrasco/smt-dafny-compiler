namespace SDC.Converter;

using SDC.AST;
using SDC.Stubs;
using Microsoft.Z3;
using Z3BoolExpr = Microsoft.Z3.BoolExpr;
using Z3Expr = Microsoft.Z3.Expr;

public class Z3ExprConverter{

    public static SDC.AST.TypeReference Z3SortToDafny(Sort sort){
        if (sort.SortKind == Z3_sort_kind.Z3_BV_SORT){
            var bvSort = (BitVecSort)sort;
            return new SDC.AST.TypeReference($"bv{bvSort.Size}");
        }

        if (sort.SortKind == Z3_sort_kind.Z3_BOOL_SORT){
            return new SDC.AST.TypeReference("bool");
        }

        throw new NotImplementedException();
    }

    enum ConversionKind{
        Method,
        Function
    };

    ConversionKind _kind;
    Func<Microsoft.Z3.Expr, Expression> _childConverter;
    IDictionary<uint, Expression> _cache = new Dictionary<uint, Expression>();
    bool _useSafeDiv = true;

    IDictionary<uint, Expression> _conversionCache = new Dictionary<uint, Expression>();

    public List<TypeReference> SafeDivUseSort = new List<TypeReference>();
    public List<VariableDefinition> Parameters = new List<VariableDefinition>();

    private Z3ExprConverter(ConversionKind conversionKind){
        _kind = conversionKind;
    }

    /*
        The function translation does not use local variables for intermediate results.
        In this mode, we use the same dafny expression for each Z3 expression on each occurrence. 
    */
    public static Z3ExprConverter CreateFunctionConverter(){
        var r = new Z3ExprConverter(ConversionKind.Function);
        r._childConverter = (e) => r.Convert(e);
        return r;
    }

    /*
        The method translation uses local variables to store intermediate computations.
        The childLookup returns the variable names.
        The caller must ensure that the child are processed first.
    */
    public static Z3ExprConverter CreateMethodConverter(Func<Microsoft.Z3.Expr, Expression> childLookup){
        var r = new Z3ExprConverter(ConversionKind.Method);
        r._childConverter = childLookup;
        return r;
    }

    public Expression Convert(Microsoft.Z3.Expr z3Expr){
        if (_conversionCache.TryGetValue(z3Expr.Id, out Expression result)){
            return result;
        }

        SDC.AST.Expression dafnyExpr;
        if (z3Expr is Z3BoolExpr){
            if (z3Expr.IsApp){
                switch (z3Expr.FuncDecl.DeclKind){
                    case Z3_decl_kind.Z3_OP_UGEQ:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            dafnyExpr = new SDC.AST.BinaryExpression(a0, Operator.GreaterEq, a1);
                        }
                        break;
                    default:
                        throw new NotImplementedException($"Unknown kind {z3Expr.FuncDecl.DeclKind}");
                }
            } else {
                throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
            }
        } else if (z3Expr is BitVecExpr bvExpr){
            if (z3Expr.IsApp){
                switch (z3Expr.FuncDecl.DeclKind){
                    case Z3_decl_kind.Z3_OP_BUDIV:
                        {
                            var a0 = _childConverter(z3Expr.Args[0]);
                            var a1 = _childConverter(z3Expr.Args[1]);
                            if (_useSafeDiv){
                                var t = Z3SortToDafny(z3Expr.Sort);
                                var _safeDivIdentifier = _kind == ConversionKind.Method ? SafeDiv.GetSafeDivMethodIdentifier(t) : SafeDiv.GetSafeDivFunctionIdentifier(t);
                                dafnyExpr = new SDC.AST.CallExpression(_safeDivIdentifier, new List<Expression>() {a0, a1});
                                SafeDivUseSort.Add(Z3SortToDafny(z3Expr.Sort));
                            } else{
                                dafnyExpr = new SDC.AST.BinaryExpression(a0, Operator.Division, a1);
                            }
                        }
                        break;
                        case Z3_decl_kind.Z3_OP_UNINTERPRETED:
                        {
                            if (z3Expr.IsConst && z3Expr.NumArgs == 0){
                                Parameters.Add(new VariableDefinition(new VariableReference(z3Expr.FuncDecl.Name.ToString()), Z3SortToDafny(z3Expr.Sort)));
                                dafnyExpr = Parameters.Last().Variable.ToExpression();
                                break;
                            }
                            throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
                        }
                    default:
                        throw new NotImplementedException($"Unknown kind {z3Expr.FuncDecl.DeclKind}");
                }
            } else if (z3Expr is BitVecNum bitVecNum) {
                dafnyExpr = new LiteralExpression(bitVecNum.UInt64.ToString());
            } else {
                throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
            }
        } else {
            throw new NotImplementedException($"Unknown expression {z3Expr.ToString()}");
        }

        _conversionCache[z3Expr.Id] = dafnyExpr;
        return dafnyExpr;
    }
}