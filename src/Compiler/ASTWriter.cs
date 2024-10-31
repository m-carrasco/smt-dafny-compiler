namespace SDC.AST;
using System.CodeDom.Compiler;
using SDC.AST;

public class ASTWriter
{
    public IndentedTextWriter TextWriter;

    public static string Serialize(IASTVisitable v)
    {
        StringWriter stringWriter = new();
        var w = new ASTWriter(new IndentedTextWriter(stringWriter));
        w.Write(v);
        stringWriter.Flush();
        return stringWriter.ToString();
    }

    public ASTWriter(IndentedTextWriter textWriter)
    {
        this.TextWriter = textWriter;
    }

    public static string SerializeOperator(Operator op)
    {
        switch (op)
        {
            case Operator.Equal:
                return "==";
            case Operator.NotEqual:
                return "!=";
            case Operator.Greater:
                return ">";
            case Operator.GreaterEq:
                return ">=";
            case Operator.Less:
                return "<";
            case Operator.LessEq:
                return "<=";
            case Operator.Division:
                return "/";
            case Operator.Mod:
                return "%";
            case Operator.BooleanAnd:
                return "&&";
            case Operator.BooleanOr:
                return "||";
            case Operator.BooleanNegation:
                return "!";
            case Operator.BitwiseOr:
                return "|";
            case Operator.BitwiseAnd:
                return "&";
            case Operator.BitwiseNot:
                return "!";
            case Operator.BitwiseXor:
                return "^";
            case Operator.BitwiseNeg:
                return "-";
            case Operator.Add:
                return "+";
            case Operator.Minus:
                return "-";
            case Operator.Multiply:
                return "*";
            case Operator.Shl:
                return "<<";
            case Operator.Shr:
                return ">>";
        }

        throw new NotImplementedException();
    }

    class Visitor : IASTVisitor
    {
        private IndentedTextWriter _textWriter;

        public Visitor(IndentedTextWriter texterWriter)
        {
            this._textWriter = texterWriter;
        }

        public void Visit(IIdentifier identifier)
        {
            _textWriter.Write(identifier.Identifier);
        }

        public void Visit(SDC.AST.Program p)
        {
            foreach (Import i in p.Imports)
            {
                Visit(i);
            }

            if (p.Imports.Count > 0)
            {
                _textWriter.WriteLine("");
            }

            foreach (FunctionDefinition f in p.Functions)
            {
                Visit(f);
                _textWriter.WriteLine();
            }

            foreach (MethodDefinition m in p.Methods)
            {
                Visit(m);
                _textWriter.WriteLine();
            }
        }

        public void Visit(MethodDefinition e)
        {
            string parameters = string.Join(", ", e.Parameters.Select(p => $"{p.Variable.Identifier} : {p.Type.Identifier}"));

            string result = string.Empty;
            if (e.ResultParameter != null)
            {
                result = $"returns ({e.ResultParameter.Variable.Identifier} : {e.ResultParameter.Type.Identifier})";
            }
            string attributes = string.Join(" ", e.Attributes.Select(a => Serialize(a)));
            _textWriter.WriteLine("method {0} {1}({2}) {3}", attributes, e.Identifier, parameters, result);

            if (e.Requires != null)
            {
                _textWriter.Indent++;
                _textWriter.WriteLine($"requires {Serialize(e.Requires)}");
                _textWriter.Indent--;
            }

            if (e.Ensures != null)
            {
                _textWriter.Indent++;
                _textWriter.WriteLine($"ensures {Serialize(e.Ensures)}");
                _textWriter.Indent--;
            }

            _textWriter.WriteLine("{");
            _textWriter.Indent += 1;

            foreach (VariableDefinition local in e.LocalVariables)
            {
                _textWriter.WriteLine($"var {local.Variable.Identifier} : {local.Type.Identifier};");
            }

            if (e.LocalVariables.Count > 0)
            {
                _textWriter.WriteLine("");
            }

            if (e.Statements != null)
            {
                foreach (Statement s in e.Statements)
                {
                    s.Accept(this);
                }
            }

            _textWriter.Indent -= 1;
            _textWriter.WriteLine("}");
        }

        public void Visit(FieldAccessExpression e)
        {
            _textWriter.Write($"{Serialize(e.Object)}.{e.Field.Identifier}");
        }

        public void Visit(CallStatement e)
        {
            _textWriter.WriteLine($"{Serialize(e.CallExpression)};");
        }

        public void Visit(FunctionDefinition e)
        {
            string parameters = string.Join(", ", e.Parameters.Select(p => $"{p.Variable.Identifier} : {p.Type.Identifier}"));

            _textWriter.WriteLine("function {0}({1}) : {2}", e.Identifier, parameters, Serialize(e.ResultType));

            _textWriter.WriteLine("{");
            _textWriter.Indent += 1;

            _textWriter.WriteLine(Serialize(e.Expression));

            _textWriter.Indent -= 1;
            _textWriter.WriteLine("}");
        }

        public void Visit(SequenceExpression sequenceExpression)
        {
            string elements = string.Join(", ", sequenceExpression.Elements.Select(e => Serialize(e)));
            _textWriter.Write($"[{elements}]");
        }

        public void Visit(Import e)
        {
            _textWriter.WriteLine($"import {e.Module}");
        }

        public void Visit(ExpectStatement e)
        {
            _textWriter.WriteLine($"expect {Serialize(e.Condition)}, {Serialize(e.Message)};");
        }

        public void Visit(PrintStatement e)
        {
            string parameters = string.Join(", ", e.Expressions.Select(e => Serialize(e)));
            _textWriter.WriteLine($"print {parameters};", parameters);
        }

        public void Visit(CallExpression e)
        {
            IEnumerable<string> parameters = e.Parameters.Select(p => Serialize(p));
            string paramList = string.Join(", ", parameters);
            _textWriter.Write($"{e.CalledExpression.Identifier}({paramList})");
        }

        public void Visit(AssignmentStatement e)
        {
            _textWriter.WriteLine($"{Serialize(e.LHS)} := {Serialize(e.RHS)};");
        }

        public void Visit(IfCodeStatement e)
        {
            _textWriter.WriteLine($"if ({Serialize(e.Condition)}) {{");
            _textWriter.Indent++;
            foreach (Statement s in e.TrueBlock)
            {
                s.Accept(this);
            }
            _textWriter.Indent--;


            if (e.FalseBlock.Count == 0)
            {
                _textWriter.WriteLine("}");
            }
            else
            {
                _textWriter.WriteLine("} else {");
                _textWriter.Indent++;
                foreach (Statement s in e.FalseBlock)
                {
                    s.Accept(this);
                }
                _textWriter.Indent--;
                _textWriter.WriteLine("}");
            }

        }

        public void Visit(Attribute e)
        {
            if (e.Value == null)
            {
                _textWriter.Write("{:" + e.Name + " }");
            }
            else
            {
                _textWriter.Write("{:" + e.Name + " " + Serialize(e.Value) + " }");
            }
        }
        public void Visit(BinaryExpression e)
        {
            _textWriter.Write($"({Serialize(e.LHS)} {SerializeOperator(e.Op)} {Serialize(e.RHS)})");
        }

        public void Visit(UnaryExpression e)
        {
            _textWriter.Write($"({SerializeOperator(e.Op)} {Serialize(e.Expr)})");
        }


        public void Visit(MathIfThenElse e)
        {
            _textWriter.Write($"(if {Serialize(e.Condition)} then {Serialize(e.TrueExpression)} else {Serialize(e.FalseExpression)})");
        }

        public void Visit(LiteralExpression e)
        {
            _textWriter.Write(e.Literal);
        }

        public void Visit(ReturnStatement e)
        {
            if (e.ReturnedValue != null)
            {
                _textWriter.WriteLine($"return {Serialize(e.ReturnedValue)};");
            }
            else
            {
                _textWriter.WriteLine("return;");
            }
        }

        public void Visit(ModulusExpression e)
        {
            _textWriter.Write($"|{Serialize(e.Expr)}|");
        }

        public void Visit(IndexExpression e)
        {
            _textWriter.Write($"{Serialize(e.ArrayLike)}[{Serialize(e.Index)}]");
        }

        public void Visit(AsExpression e)
        {
            _textWriter.Write($"({Serialize(e.Expression)} as {Serialize(e.Type)})");
        }
    };

    public void Write(IASTVisitable astVisitable)
    {
        Visitor v = new Visitor(this.TextWriter);
        astVisitable.Accept(v);
    }
};
