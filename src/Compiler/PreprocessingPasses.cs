namespace SDC.PreProcessingPass;

using Microsoft.Z3;

public class PreprocessingPasses
{

    public static Expr Preprocess(Expr expr)
    {
        // TODO: Improve the replacement efficency.
        //      At the moment we traverse the whole expression for each routine.

        // Be careful with the ordering.
        // Some replacements could potential rely on others being applied before/after.
        expr = ReplaceBvsmod(expr);
        expr = ReplaceBvnor(expr);
        expr = ReplaceRepeat(expr);
        expr = ReplaceBvnand(expr);
        expr = ReplaceBvxnor(expr);
        expr = ReplaceBvashr(expr);
        expr = ReplaceBvsrem(expr);

        return expr;
    }

    private static Expr ReplaceExpr(Expr expr, Func<Expr, bool> shouldReplace, Func<Expr, Expr> inlineFunc)
    {
        // If the expression has arguments, process them first.
        if (expr.NumArgs > 0)
        {
            Expr[] newArgs = new Expr[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++)
            {
                // Recursively apply ReplaceExpr to each argument.
                newArgs[i] = ReplaceExpr(expr.Arg(i), shouldReplace, inlineFunc);
            }

            // After processing children, apply them to the function declaration to reconstruct the expression.
            expr = expr.FuncDecl.Apply(newArgs);
        }

        // Now, check if the current (potentially modified) expression should be replaced.
        if (shouldReplace(expr))
        {
            return inlineFunc(expr);
        }

        // Return the expression as-is if no replacement was needed.
        return expr;
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

    private static Expr ReplaceBvnand(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNAND,
            InlineBvnand
        );
    }

    private static Expr InlineBvnand(Expr expr)
    {
        var ctx = expr.Context;
        var s = (BitVecExpr)expr.Args[0];
        var t = (BitVecExpr)expr.Args[1];

        // bvnand is defined as bvnot(bvand s t)
        var bvandExpr = ctx.MkBVAND(s, t);
        return ctx.MkBVNot(bvandExpr);
    }


    private static Expr ReplaceBvxnor(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BXNOR,
            InlineBvxnor
        );
    }

    private static Expr InlineBvxnor(Expr expr)
    {
        var ctx = expr.Context;
        var s = (BitVecExpr)expr.Args[0];
        var t = (BitVecExpr)expr.Args[1];

        // bvxnor is defined as (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
        var bvand1 = ctx.MkBVAND(s, t);
        var bvand2 = ctx.MkBVAND(ctx.MkBVNot(s), ctx.MkBVNot(t));

        return ctx.MkBVOR(bvand1, bvand2);
    }


    private static Expr ReplaceBvashr(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BASHR,
            InlineBvashr
        );
    }

    private static Expr InlineBvashr(Expr expr)
    {
        /*
            (bvashr s t) abbreviates 
                (ite (= ((_ extract |m-1| |m-1|) s) #b0)
                    (bvlshr s t)
                    (bvnot (bvlshr (bvnot s) t)))

        */
        var ctx = expr.Context;
        var s = (BitVecExpr)expr.Args[0];
        var t = (BitVecExpr)expr.Args[1];

        uint m = s.SortSize;  // Bit-width of s
        var msb_s = ctx.MkExtract(m - 1, m - 1, s);  // Extract the most significant bit of s

        // Define the two cases for the result of the arithmetic shift right
        var lshrResult = ctx.MkBVLSHR(s, t);  // Logical shift right of s by t
        var negLshrResult = ctx.MkBVNot(ctx.MkBVLSHR(ctx.MkBVNot(s), t));  // bvnot(bvlshr(bvnot(s), t))

        // Construct the if-then-else expression for the bvashr
        return ctx.MkITE(
            ctx.MkEq(msb_s, ctx.MkBV(0, 1)),  // Check if the MSB of s is 0
            lshrResult,  // If MSB is 0, return lshr(s, t)
            negLshrResult  // If MSB is 1, return bvnot(lshr(bvnot(s), t))
        );
    }

    private static Expr ReplaceBvsrem(Expr expr)
    {
        return ReplaceExpr(
            expr,
            e => e.FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSREM,
            InlineBvsrem
        );
    }

    private static Expr InlineBvsrem(Expr expr)
    {
        /*
        (bvsrem s t) abbreviates
            (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                    (?msb_t ((_ extract |m-1| |m-1|) t)))
                (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                    (bvurem s t)
                (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                    (bvneg (bvurem (bvneg s) t))
                (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                    (bvurem s (bvneg t)))
                    (bvneg (bvurem (bvneg s) (bvneg t))))))
        */
        var ctx = expr.Context;
        var s = (BitVecExpr)expr.Args[0];
        var t = (BitVecExpr)expr.Args[1];
        uint m = s.SortSize;

        // Extract the most significant bits (MSBs) of s and t to determine their signs
        var msb_s = ctx.MkExtract(m - 1, m - 1, s);
        var msb_t = ctx.MkExtract(m - 1, m - 1, t);

        // Define the cases based on the MSB values of s and t
        var urem_s_t = ctx.MkBVURem(s, t);                      // bvurem(s, t)
        var neg_urem_neg_s_t = ctx.MkBVNeg(ctx.MkBVURem(ctx.MkBVNeg(s), t));   // bvneg(bvurem(bvneg(s), t))
        var urem_s_neg_t = ctx.MkBVURem(s, ctx.MkBVNeg(t));     // bvurem(s, bvneg(t))
        var neg_urem_neg_s_neg_t = ctx.MkBVNeg(ctx.MkBVURem(ctx.MkBVNeg(s), ctx.MkBVNeg(t)));  // bvneg(bvurem(bvneg(s), bvneg(t)))

        // Construct the nested if-then-else (ite) expressions for bvsrem
        return ctx.MkITE(
            ctx.MkAnd(ctx.MkEq(msb_s, ctx.MkBV(0, 1)), ctx.MkEq(msb_t, ctx.MkBV(0, 1))),  // Case: s >= 0 and t >= 0
            urem_s_t,
            ctx.MkITE(
                ctx.MkAnd(ctx.MkEq(msb_s, ctx.MkBV(1, 1)), ctx.MkEq(msb_t, ctx.MkBV(0, 1))),  // Case: s < 0 and t >= 0
                neg_urem_neg_s_t,
                ctx.MkITE(
                    ctx.MkAnd(ctx.MkEq(msb_s, ctx.MkBV(0, 1)), ctx.MkEq(msb_t, ctx.MkBV(1, 1))),  // Case: s >= 0 and t < 0
                    urem_s_neg_t,
                    neg_urem_neg_s_neg_t  // Case: s < 0 and t < 0
                )
            )
        );
    }

}

