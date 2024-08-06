namespace SDC.AST;

public class VariableDefinition{
    public VariableReference Variable;
    public TypeReference Type;

    public VariableDefinition(VariableReference variable, TypeReference type){
        this.Variable = variable;
        this.Type = type;
    }
};

public interface IASTVisitable{
    void Accept(IASTVisitor visitor);
};

public interface IIdentifier : IASTVisitable {
    string Identifier { get; }
};

public interface IASTVisitor{
    void Visit(IIdentifier identifier);
    void Visit(MethodDefinition e);
    void Visit(FunctionDefinition e);
    void Visit(AssignmentStatement e);
    void Visit(IfCodeStatement e);
    void Visit(BinaryExpression e);
    void Visit(MathIfThenElse e);
    void Visit(LiteralExpression e);
    void Visit(CallExpression e);
    void Visit(ReturnStatement e);
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
};

public class VariableReference : IIdentifier, IASTVisitable{
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

    public IdentifierExpression ToExpression(){
        return new IdentifierExpression(Identifier);
    }
};

public abstract class Expression : IASTVisitable{
    public abstract void Accept(IASTVisitor visitor);
};

public enum Operator{
    Greater,
    GreaterEq,
    Equal,
    NotEqual,
    Division,
    And
};

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
    public IdentifierExpression(string identifier) {
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

    public BinaryExpression(Expression lhs, Operator op, Expression rhs){
        LHS = lhs;
        Op = op;
        RHS = rhs;
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
    public MathIfThenElse(Expression condition, Expression trueExpression, Expression falseExpression){
        Condition = condition;
        TrueExpression = trueExpression;
        FalseExpression = falseExpression;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public abstract class Statement : IASTVisitable{
    abstract public void Accept(IASTVisitor visitor);
};

public class LiteralExpression : Expression{
    static public readonly LiteralExpression False = new LiteralExpression("false");
    static public readonly LiteralExpression True = new LiteralExpression("true");
    static public readonly LiteralExpression Zero = new LiteralExpression("0");
    public string Literal;
    public LiteralExpression(string literal) {
        Literal = literal;
    }
    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};
public class AssignmentStatement : Statement{
    public AssignmentStatement(VariableReference lhs, Expression rhs){
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

public class ReturnStatement : Statement{
    public ReturnStatement(Expression returnedValue){
        ReturnedValue = returnedValue;
    }

    public Expression ReturnedValue;

    public override void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};

public class IfCodeStatement : Statement{

    public IfCodeStatement(Expression condition, List<Statement> trueBlock, List<Statement> falseBlock){
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

public class MethodReference : IIdentifier {
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
    public IdentifierExpression ToExpression(){
        return new IdentifierExpression(Identifier);
    }
};

public class FunctionDefinition : IIdentifier, IASTVisitable {
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

    public void Accept(IASTVisitor visitor){
        visitor.Visit(this);
    }

    public IdentifierExpression ToExpression(){
        return new IdentifierExpression(Identifier);
    }
};

public class MethodDefinition : IIdentifier, IASTVisitable {
    public string Identifier => _identifier;
    private string _identifier;
    public List<VariableDefinition> Parameters;
    public VariableDefinition? ResultParameter;
    public List<Statement> Statements;
    public Expression? Requires;
    public Expression? Ensures;
    public List<VariableDefinition> LocalVariables;

    public MethodDefinition(string identifier, List<VariableDefinition> parameters, VariableDefinition? resultParameter, Expression? requires, Expression? ensures, List<Statement> statements, List<VariableDefinition> localVariables)
    {
        this._identifier = identifier;
        this.Parameters = parameters;
        this.ResultParameter = resultParameter;
        this.Requires = requires;
        this.Ensures = ensures;
        this.Statements = statements;
        this.LocalVariables = localVariables;
    }

    public void Accept(IASTVisitor visitor){
        visitor.Visit(this);
    }
};

public class Program : IASTVisitable
{
    public List<FunctionDefinition> Functions;
    public List<MethodDefinition> Methods;
    public Program(List<FunctionDefinition> Function, List<MethodDefinition> Method){
        Functions = Function;
        Methods = Method;
    }
    public void Accept(IASTVisitor visitor)
    {
        visitor.Visit(this);
    }
};