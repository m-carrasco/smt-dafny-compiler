
namespace SDC;
using Microsoft.Z3;

public class Simplifier
{
    public static BoolExpr BuildAnd(Context ctx, List<BoolExpr> conjuncts)
    {
        if (conjuncts.Count == 0)
        {
            throw new ArgumentException("List cannot be empty");
        }

        if (conjuncts.Any(c => c.IsFalse))
        {
            return ctx.MkFalse();
        }

        conjuncts = conjuncts.FindAll(c => !c.IsTrue);

        BoolExpr result;
        switch (conjuncts.Count)
        {
            case 0:
                result = ctx.MkTrue();
                break;
            case 1:
                result = conjuncts.First();
                break;
            default:
                result = ctx.MkAnd(conjuncts.ToArray());
                break;
        }

        return result;
    }

    public static BoolExpr BuildOr(Context ctx, List<BoolExpr> disjuncts)
    {
        if (disjuncts.Count == 0)
        {
            throw new ArgumentException("List cannot be empty");
        }

        if (disjuncts.Any(c => c.IsTrue))
        {
            return ctx.MkTrue();
        }

        disjuncts = disjuncts.FindAll(c => !c.IsFalse);

        BoolExpr result;
        switch (disjuncts.Count)
        {
            case 0:
                result = ctx.MkFalse();
                break;
            case 1:
                result = disjuncts.First();
                break;
            default:
                result = ctx.MkOr(disjuncts.ToArray());
                break;
        }

        return result;
    }

    // This is useful to simplify without introducing new constructs that are assumed to be erased already.
    public static BoolExpr ReplaceWithConstIfPossible(BoolExpr expr)
    {
        var simplified = expr.Simplify();

        if (simplified.IsTrue)
        {
            return expr.Context.MkTrue();
        }
        else if (simplified.IsFalse)
        {
            return expr.Context.MkFalse();
        }
        else
        {
            return expr;
        }
    }

    // This will just remove those that are true, but it won't return the simplified expressions.
    // The intent is to preserve the preporcessing passes.
    public static List<Expr> RemoveTrueAssertions(BoolExpr[] assertions)
    {
        List<Expr> result = new List<Expr>();

        foreach (BoolExpr assertion in assertions)
        {
            var simplified = assertion.Simplify();

            if (!simplified.IsTrue)
            {
                result.Add(assertion);
            }
        }

        return result;
    }
}
