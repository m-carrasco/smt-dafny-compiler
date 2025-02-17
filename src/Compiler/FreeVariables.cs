using Microsoft.Z3;

namespace SDC;

public class FreeVariables
{
    public static void CollectFreeVariables(Expr expr, HashSet<Expr> freeVars, HashSet<Expr> visited)
    {
        if (visited.Contains(expr))
        {
            return; // Avoid redundant traversal
        }
        visited.Add(expr);

        if (expr.IsTrue || expr.IsFalse || expr.IsNumeral)
        {
            return;
        }

        if (expr.IsConst && expr.NumArgs == 0)  // Constants (variables in SMT)
        {
            freeVars.Add(expr);
        }

        // Recursively visit sub-expressions
        for (uint i = 0; i < expr.NumArgs; i++)
        {
            CollectFreeVariables(expr.Arg(i), freeVars, visited);
        }
    }
}
