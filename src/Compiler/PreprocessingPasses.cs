namespace SDC.PreProcessingPass;

using Microsoft.Z3;

public class PreprocessingPasses
{

    public static Expr Preprocess(Expr expr)
    {
        // TODO: Improve the replacement efficency.
        //      At the moment we traverse the whole expression for each routine.

        // Be careful with the ordering.
        // Some replacements could potential rely on others being applied before.
        expr = ReplaceBvsmod(expr);
        expr = ReplaceBvnor(expr);
        expr = ReplaceRepeat(expr);

        return expr;
    }

    private static Expr ReplaceExpr(Expr expr, Func<Expr, bool> shouldReplace, Func<Expr, Expr> inlineFunc)
    {
        if (shouldReplace(expr))
        {
            return inlineFunc(expr);
        }
        else if (expr.NumArgs > 0)
        {
            Expr[] newArgs = new Expr[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++)
            {
                newArgs[i] = ReplaceExpr(expr.Arg(i), shouldReplace, inlineFunc);
            }
            return expr.FuncDecl.Apply(newArgs);
        }
        else
        {
            return expr;
        }
    }


    private static Expr ReplaceBvsmod(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSMOD,
            InlineBvsmod
        );
    }

    private static BitVecExpr InlineBvsmod(Expr expr)
    {
        // This is following the definition of bvsmod in https://smt-lib.org/logics-all.shtml#QF_BV

        var s = (BitVecExpr)expr.Args[0];
        var t = (BitVecExpr)expr.Args[1];
        var ctx = expr.Context;

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

    private static Expr ReplaceBvnor(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNOR,
            InlineBvnor
        );
    }

    private static Expr InlineBvnor(Expr expr)
    {
        var s = (BitVecExpr)expr.Args[0];
        var t = (BitVecExpr)expr.Args[1];
        var ctx = expr.Context;

        // bvnor is defined as bvnot(bvor s t)
        var bvorExpr = ctx.MkBVOR(s, t);
        return ctx.MkBVNot(bvorExpr);
    }

    private static Expr ReplaceRepeat(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_REPEAT,
            InlineRepeat
        );
    }

    private static Expr InlineRepeat(Expr expr)
    {
        var ctx = expr.Context;
        var t = (BitVecExpr)expr.Args[0];
        uint repeatCount = (uint)expr.FuncDecl.Parameters[0].Int;  // Get the repeat count parameter

        return BuildRepeat(ctx, t, repeatCount);
    }

    private static BitVecExpr BuildRepeat(Context ctx, BitVecExpr t, uint repeatCount)
    {
        if (repeatCount == 1)
        {
            // Base case: repeat 1 just returns t
            return t;
        }
        else
        {
            // Recursive case: concatenate t with the repeat of t, j-1 times
            return ctx.MkConcat(t, BuildRepeat(ctx, t, repeatCount - 1));
        }
    }
}

