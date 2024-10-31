namespace SDC.AST;

public class VariableDefinition
{
    public VariableReference Variable;
    public TypeReference Type;

    public VariableDefinition(VariableReference variable, TypeReference type)
    {
        this.Variable = variable;
        this.Type = type;
    }
};

public interface IASTVisitable
{
    void Accept(IASTVisitor visitor);
};

public interface IIdentifier : IASTVisitable
{
    string Identifier { get; }
};

public interface IASTVisitor
{
    void Visit(IIdentifier identifier);
    void Visit(Attribute e);
    void Visit(MethodDefinition e);
    void Visit(FunctionDefinition e);
    void Visit(AssignmentStatement e);
    void Visit(IfCodeStatement e);
    void Visit(CallStatement e);
    void Visit(BinaryExpression e);
    void Visit(UnaryExpression e);
    void Visit(ModulusExpression e);
    void Visit(IndexExpression e);
    void Visit(SequenceExpression e);
    void Visit(MathIfThenElse e);
    void Visit(LiteralExpression e);
    void Visit(CallExpression e);
    void Visit(AsExpression e);
    void Visit(FieldAccessExpression e);
    void Visit(ReturnStatement e);
    void Visit(PrintStatement e);
    void Visit(ExpectStatement e);
    void Visit(Import e);
    void Visit(SDC.AST.Program e);
};

public class TypeReference : IIdentifier, IASTVisitable
{
    public string Identifier => _identifier;
    private string _identifier;

    public TypeReference(string identifier)
    {
        _identifier = identifier;
    }

    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }

    public override bool Equals(object obj)
    {
        var item = obj as TypeReference;

        if (item == null)
        {
            return false;
        }

        return Identifier.Equals(item.Identifier);
    }

    public override int GetHashCode()
    {
        return Identifier.GetHashCode();
    }

    public bool IsBoolType()
    {
        return _identifier.Equals("bool");
    }

    public bool IsBVType()
    {
        return _identifier.StartsWith("bv");
    }

    public int GetBVSize()
    {
        if (IsBVType())
        {
            int bits = int.Parse(this.Identifier.Substring(2));
            return bits;
        }

        throw new ArgumentException("BV type expected");
    }

};

public class VariableReference : IIdentifier, IASTVisitable
{
    public string Identifier => _identifier;
    private string _identifier;

    public VariableReference(string identifier)
    {
        _identifier = identifier;
    }

    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }

    public IdentifierExpression ToExpression()
    {
        return new IdentifierExpression(Identifier);
    }
};

public abstract class Expression : IASTVisitable
{
    public abstract void Accept(IASTVisitor visitor);

    public static Expression BooleanXor(Expression a, Expression b)
    {
        //A XOR B= (A∨B) ∧ ¬(A∧B)
        return new BinaryExpression(new BinaryExpression(a, Operator.BooleanOr, b), Operator.BooleanAnd, new UnaryExpression(new BinaryExpression(a, Operator.BooleanAnd, b), Operator.BooleanNegation));
    }
};

public enum Operator
{
    Greater,
    GreaterEq,
    Less,
    LessEq,
    Equal,
    NotEqual,
    Division,
    BooleanAnd,
    BooleanOr,
    BooleanNegation,
    BitwiseOr,
    BitwiseAnd,
    BitwiseNot,
    BitwiseXor,
    BitwiseNeg,
    Mod,
    Minus,
    Add,
    Multiply,
    Shl,
    Shr,
};

public class FieldAccessExpression : Expression, IASTVisitable
{
    public Expression Object;
    public IdentifierExpression Field;

    public FieldAccessExpression(Expression o, IdentifierExpression f)
    {
        Object = o;
        Field = f;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class AsExpression : Expression
{
    public Expression Expression;
    public TypeReference Type;
    public AsExpression(Expression expression, TypeReference type)
    {
        Expression = expression;
        Type = type;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
}

public class Attribute : IASTVisitable
{
    public String Name;
    public Expression? Value;

    public Attribute(string name, Expression value)
    {
        Name = name;
        Value = value;
    }
    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
}
public class CallExpression : Expression, IASTVisitable
{
    public IdentifierExpression CalledExpression;
    public List<Expression> Parameters;

    public CallExpression(IdentifierExpression calledExpression, List<Expression> parameters)
    {
        CalledExpression = calledExpression;
        Parameters = parameters;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class IdentifierExpression : Expression, IIdentifier
{
    public IdentifierExpression(string identifier)
    {
        this._identifier = identifier;
    }

    public string Identifier => _identifier;
    private string _identifier;
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class BinaryExpression : Expression
{
    public Expression LHS;
    public Expression RHS;
    public Operator Op;

    public BinaryExpression(Expression lhs, Operator op, Expression rhs)
    {
        LHS = lhs;
        Op = op;
        RHS = rhs;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class UnaryExpression : Expression
{
    public Expression Expr;
    public Operator Op;

    public UnaryExpression(Expression expr, Operator op)
    {
        Expr = expr;
        Op = op;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class MathIfThenElse : Expression
{
    public Expression Condition;
    public Expression TrueExpression;
    public Expression FalseExpression;
    public MathIfThenElse(Expression condition, Expression trueExpression, Expression falseExpression)
    {
        Condition = condition;
        TrueExpression = trueExpression;
        FalseExpression = falseExpression;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public abstract class Statement : IASTVisitable
{
    abstract public void Accept(IASTVisitor visitor);
};

public class ModulusExpression : Expression, IASTVisitable
{
    public Expression Expr;
    public ModulusExpression(Expression e)
    {
        Expr = e;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
}

public class IndexExpression : Expression
{
    public Expression ArrayLike;
    public Expression Index;
    public IndexExpression(Expression arrayLike, Expression index)
    {
        ArrayLike = arrayLike;
        Index = index;

    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
}

public class LiteralExpression : Expression, IASTVisitable
{
    static public readonly LiteralExpression False = new LiteralExpression("false");
    static public readonly LiteralExpression True = new LiteralExpression("true");
    static public readonly LiteralExpression Zero = new LiteralExpression("0");
    static public readonly LiteralExpression One = new LiteralExpression("1");

    public static LiteralExpression Create(string literal)
    {
        return new LiteralExpression(literal);
    }

    public string Literal;
    public LiteralExpression(string literal)
    {
        Literal = literal;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class ExpectStatement : Statement
{
    public Expression Condition;
    public Expression Message;

    public ExpectStatement(Expression condition, Expression message)
    {
        Condition = condition;
        Message = message;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class AssignmentStatement : Statement
{
    public AssignmentStatement(VariableReference lhs, Expression rhs)
    {
        LHS = lhs;
        RHS = rhs;
    }

    public VariableReference LHS;
    public Expression RHS;

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class CallStatement : Statement
{
    public CallExpression CallExpression;
    public CallStatement(CallExpression callExpression)
    {
        CallExpression = callExpression;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class ReturnStatement : Statement
{
    public ReturnStatement(Expression returnedValue)
    {
        ReturnedValue = returnedValue;
    }

    public Expression ReturnedValue;

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class IfCodeStatement : Statement
{

    public IfCodeStatement(Expression condition, List<Statement> trueBlock, List<Statement> falseBlock)
    {
        Condition = condition;
        TrueBlock = trueBlock;
        FalseBlock = falseBlock;
    }

    public Expression Condition;
    public List<Statement> TrueBlock;
    public List<Statement> FalseBlock;

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class SequenceExpression : Expression, IASTVisitable
{
    public List<Expression> Elements;
    public SequenceExpression(List<Expression> elements)
    {
        Elements = elements;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class PrintStatement : Statement
{
    public List<Expression> Expressions;

    public PrintStatement(List<Expression> expressions)
    {
        Expressions = expressions;
    }

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class MethodReference : IIdentifier
{
    public string Identifier => _identifier;
    private string _identifier;
    public List<TypeReference> ParameterTypes => _parameterTypes;
    private List<TypeReference> _parameterTypes;

    public MethodReference(string identifier, List<TypeReference> parameterTypes)
    {
        _identifier = identifier;
        _parameterTypes = parameterTypes;
    }
    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
    public IdentifierExpression ToExpression()
    {
        return new IdentifierExpression(Identifier);
    }
};

public class FunctionDefinition : IIdentifier, IASTVisitable
{
    public string Identifier => _identifier;
    private string _identifier;
    public List<VariableDefinition> Parameters;
    public TypeReference ResultType;
    public Expression Expression;

    public FunctionDefinition(string identifier, List<VariableDefinition> parameters, TypeReference resultType, Expression expression)
    {
        this._identifier = identifier;
        this.Parameters = parameters;
        this.ResultType = resultType;
        this.Expression = expression;
    }

    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }

    public IdentifierExpression ToExpression()
    {
        return new IdentifierExpression(Identifier);
    }
};

public class MethodDefinition : IIdentifier, IASTVisitable
{
    public string Identifier => _identifier;
    private string _identifier;
    public List<VariableDefinition> Parameters;
    public VariableDefinition? ResultParameter;
    public List<Statement> Statements;
    public Expression? Requires;
    public Expression? Ensures;
    public List<VariableDefinition> LocalVariables;
    public List<Attribute> Attributes;

    public MethodDefinition(string identifier, List<VariableDefinition> parameters, VariableDefinition? resultParameter, Expression? requires, Expression? ensures, List<Statement> statements, List<VariableDefinition> localVariables, List<Attribute> attributes)
    {
        this._identifier = identifier;
        this.Parameters = parameters;
        this.ResultParameter = resultParameter;
        this.Requires = requires;
        this.Ensures = ensures;
        this.Statements = statements;
        this.LocalVariables = localVariables;
        this.Attributes = attributes;
    }

    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class Import : IASTVisitable
{
    public String Module;
    public Import(String m)
    {
        this.Module = m;
    }
    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};
public class Program : IASTVisitable
{
    public List<Import> Imports;
    public List<FunctionDefinition> Functions;
    public List<MethodDefinition> Methods;
    public Program(List<Import> Imports, List<FunctionDefinition> Functions, List<MethodDefinition> Methods)
    {
        this.Functions = Functions;
        this.Methods = Methods;
        this.Imports = Imports;
    }
    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};
