namespace SDC.PreProcessingPass;

using Microsoft.Z3;

public class PreprocessingPasses
{

    public static Expr Preprocess(Expr expr)
    {
        return ReplaceBvsmod(expr);
    }

    private static Expr ReplaceBvsmod(Expr expr)
    {
        if (expr.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSMOD)
        {
            var s = (BitVecExpr)expr.Args[0];
            var t = (BitVecExpr)expr.Args[1];
            return InlineBvsmod(s, t, expr.Context);
        }
        else if (expr.NumArgs > 0)
        {
            Expr[] newArgs = new Expr[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++)
            {
                newArgs[i] = ReplaceBvsmod(expr.Arg(i));
            }
            return expr.FuncDecl.Apply(newArgs);
        }
        else
        {
            return expr;
        }
    }

    private static BitVecExpr InlineBvsmod(BitVecExpr s, BitVecExpr t, Context ctx)
    {
        // This is following the definition of bvsmod in https://smt-lib.org/logics-all.shtml#QF_BV

        uint m = s.SortSize; // Bit-width of s (and t, assuming same width).
        var msb_s = ctx.MkExtract(m - 1, m - 1, s);
        var msb_t = ctx.MkExtract(m - 1, m - 1, t);

        // Create abs_s and abs_t based on the sign bit.
        var abs_s = ctx.MkITE(ctx.MkEq(msb_s, ctx.MkBV(0, 1)), s, ctx.MkBVNeg(s)) as BitVecExpr;
        var abs_t = ctx.MkITE(ctx.MkEq(msb_t, ctx.MkBV(0, 1)), t, ctx.MkBVNeg(t)) as BitVecExpr;

        // Unsigned remainder of abs_s and abs_t.
        var u = ctx.MkBVURem(abs_s, abs_t);

        return (BitVecExpr)ctx.MkITE(
            ctx.MkEq(u, ctx.MkBV(0, m)),
            u,
            ctx.MkITE(
                ctx.MkAnd(ctx.MkEq(msb_s, ctx.MkBV(0, 1)), ctx.MkEq(msb_t, ctx.MkBV(0, 1))),
                u,
                ctx.MkITE(
                    ctx.MkAnd(ctx.MkEq(msb_s, ctx.MkBV(1, 1)), ctx.MkEq(msb_t, ctx.MkBV(0, 1))),
                    ctx.MkBVAdd(ctx.MkBVNeg(u), t),
                    ctx.MkITE(
                        ctx.MkAnd(ctx.MkEq(msb_s, ctx.MkBV(0, 1)), ctx.MkEq(msb_t, ctx.MkBV(1, 1))),
                        ctx.MkBVAdd(u, t),
                        ctx.MkBVNeg(u)
                    )
                )
            )
        );
    }

}

