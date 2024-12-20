package gvc.weaver
import viper.silver.{ast => vpr}
import viper.silver.ast
import gvc.transformer.{IR, IRSilver}

sealed trait Check

sealed trait ConvertContext
case class LValue() extends ConvertContext
case class RValue() extends ConvertContext
case class Binding() extends ConvertContext

object Check {
  def fromViper(check: vpr.Exp): Check = {
    check match {
      case fieldAccess: vpr.FieldAccessPredicate =>
        CheckExpression.fromViper(fieldAccess.loc, LValue()) match {
          case field: CheckExpression.Field => FieldAccessibilityCheck(field)
          case _ =>
            throw new WeaverException(
              s"Invalid field accessibility: $fieldAccess"
            )
        }

      case predicate: vpr.PredicateAccess =>
        PredicateAccessibilityCheck(
          predicate.predicateName,
          predicate.args
            .map(CheckExpression.fromViper(_, Binding()))
            .toList
        )

      case predicateAccess: vpr.PredicateAccessPredicate =>
        Check.fromViper(predicateAccess.loc)

      case _ =>
        CheckExpression.fromViper(check, RValue())
    }
  }
}

sealed trait PermissionCheck extends Check
sealed trait SeparationCheck
sealed trait AccessibilityCheck

sealed trait FieldPermissionCheck extends PermissionCheck {
  def field: CheckExpression.Field
}

sealed trait PredicatePermissionCheck extends PermissionCheck {
  def predicateName: String
  def arguments: List[CheckExpression]
}

case class FieldSeparationCheck(field: CheckExpression.Field)
    extends FieldPermissionCheck
    with SeparationCheck
{
  override def toString(): String = s"sep($field)"
}

case class FieldAccessibilityCheck(field: CheckExpression.Field)
    extends FieldPermissionCheck
    with AccessibilityCheck
{
  override def toString() = s"acc($field)"
}

case class PredicateSeparationCheck(
    predicateName: String,
    arguments: List[CheckExpression]
) extends PredicatePermissionCheck
    with SeparationCheck
{
  override def toString() = {
    val args = arguments.map(_.toString()).mkString(", ")
    s"sep($predicateName($args))"
  }
}
case class PredicateAccessibilityCheck(
    predicateName: String,
    arguments: List[CheckExpression]
) extends PredicatePermissionCheck
    with AccessibilityCheck
{
  override def toString() = {
    val args = arguments.map(_.toString()).mkString(", ")
    s"$predicateName($args)"
  }
}

sealed trait CheckExpression extends Check {
  def toIR(
      p: IR.Program,
      m: IR.Method,
      returnValue: Option[IR.Expression]
  ): IR.Expression

  def guard: Option[CheckExpression]

  def guarded: CheckExpression = CheckExpression.and(guard, this)
}

object CheckExpression {
  type Expr = CheckExpression

  private def and(a: Option[CheckExpression], b: CheckExpression): CheckExpression = a match {
    case None => b
    case Some(a) => CheckExpression.And(a, b)
  }

  private def and(a: Option[CheckExpression], b: Option[CheckExpression]): Option[CheckExpression] = b match {
    case None => a
    case Some(b) => Some(and(a, b))
  }

  sealed trait Binary extends Expr {
    val left: CheckExpression
    val right: CheckExpression
    def op: IR.BinaryOp
    def toIR(
        p: IR.Program,
        m: IR.Method,
        r: Option[IR.Expression]
    ): IR.Binary =
      new IR.Binary(op, left.toIR(p, m, r), right.toIR(p, m, r))

    def guard = and(left.guard, right.guard)

    override def toString() = s"($left) $op ($right)"
  }

  case class And(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.And
  }
  case class Or(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Or

    // The left guard must always be satisfied
    // The right guard only needs satisfied if the left condition is false
    override def guard = and(left.guard, right.guard.map(g => Or(left, g)))
  }
  case class Add(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Add
  }
  case class Sub(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Subtract
  }
  case class Mul(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Multiply
  }
  case class Div(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Divide
  }
  case class Eq(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Equal
  }
  case class Lt(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Less
  }
  case class LtEq(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.LessOrEqual
  }
  case class Gt(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Greater
  }
  case class GtEq(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.GreaterOrEqual
  }

  sealed trait Unary extends CheckExpression {
    val operand: Expr
    def op: IR.UnaryOp
    def toIR(
        p: IR.Program,
        m: IR.Method,
        r: Option[IR.Expression]
    ): IR.Unary =
      new IR.Unary(op, operand.toIR(p, m, r))
    def guard = operand.guard

    override def toString() = s"$op($operand)"
  }
  case class Not(operand: Expr) extends Unary {
    def op = IR.UnaryOp.Not
  }
  case class Neg(operand: Expr) extends Unary {
    def op = IR.UnaryOp.Negate
  }

  case class Var(name: String) extends Expr {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) = {
      m.variable(name)
    }
    def guard = None
    override def toString() = name
  }

  case class Field(root: Expr, structName: String, fieldName: String)
      extends Expr {
    def getIRField(p: IR.Program) =
      p.struct(structName)
        .fields
        .find(_.name == fieldName)
        .getOrElse(
          throw new WeaverException(s"Field '$fieldName' does not exist")
        )

    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.FieldMember(root.toIR(p, m, r), getIRField(p))
    
    def guard = Some(and(root.guard, Not(Eq(root, NullLit))))
    
    override def toString() = s"$root.$fieldName"
  }

  case class Deref(operand: Expr) extends Expr {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.DereferenceMember(operand.toIR(p, m, r))
    def guard = Some(and(operand.guard, Not(Eq(operand, NullLit))))

    override def toString() = s"*($operand)"
  }

  sealed trait Literal extends Expr {
    def guard = None
  }

  case class IntLit(value: Int) extends Literal {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.IntLit(value)
    override def toString() = value.toString()
  }
  case class CharLit(value: Char) extends Literal {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.CharLit(value)
    override def toString() = s"'$value'"
  }
  case class StrLit(value: String) extends Literal {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.StringLit(value)
    override def toString() = "\"" + value + "\""
  }
  case object NullLit extends Literal {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.NullLit()
    override def toString() = "NULL"
  }
  sealed trait BoolLit extends Literal {
    def value: Boolean
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.BoolLit(value)
    override def toString() = value.toString()
  }
  object BoolLit {
    def apply(value: Boolean): BoolLit = if (value) TrueLit else FalseLit
  }
  case object TrueLit extends BoolLit {
    def value = true
  }
  case object FalseLit extends BoolLit {
    def value = false
  }

  case class FuncApp(fun: String, args: Seq[Expr]) extends Expr {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.FunctionApplication(p.method(fun), args.map(_.toIR(p, m, r)).toList)
    def guard = args.map(Some(_)).foldRight(None.asInstanceOf[Option[CheckExpression]])(and)
  }

  case class Cond(cond: Expr, ifTrue: Expr, ifFalse: Expr) extends Expr {
    def toIR(p: IR.Program, m: IR.Method, r: Option[IR.Expression]) =
      new IR.Conditional(
        cond.toIR(p, m, r),
        ifTrue.toIR(p, m, r),
        ifFalse.toIR(p, m, r)
      )
    
    def guard = and(cond.guard, (ifTrue.guard, ifFalse.guard) match {
      case (None, None) => None

      // Have a guard for both paths
      // Use a ternary to switch on the actual condition
      case (Some(tg), Some(fg)) => Some(Cond(cond, tg, fg))

      // Only have a guard for the true path
      // Either the false path is taken, or the true guard must be satisfied
      case (Some(tg), None) => Some(Or(Not(cond), tg))

      // Only have a guard for the false path
      // Either the true path is taken, or the false guard is satisifed
      case (None, Some(fg)) => Some(Or(cond, fg))
    })

    override def toString() = s"($cond) ? ($ifTrue) : ($ifFalse)"
  }

  case object Result extends Expr {
    def toIR(
        p: IR.Program,
        m: IR.Method,
        returnValue: Option[IR.Expression]
    ): IR.Expression =
      returnValue.getOrElse(
        throw new WeaverException("Invalid \\result expression")
      )
    def guard = None
    override def toString() = "\\result"
  }

  def irValue(value: IR.Expression): Expr = {
    value match {
      case _: IR.ArrayMember | _: IR.Accessibility | _: IR.PredicateInstance |
          _: IR.Imprecise =>
        throw new WeaverException("Invalid expression used as value in spec")
      case o: IR.Old => throw new WeaverException("irValue") // TODO how do we pull out the old value?
      case n: IR.Var => Var(n.name)
      case n: IR.FieldMember =>
        Field(irValue(n.root), n.field.struct.name, n.field.name)
      case n: IR.DereferenceMember => Deref(irValue(n.root))
      case n: IR.Result            => Result
      case n: IR.IntLit               => IntLit(n.value)
      case n: IR.CharLit              => CharLit(n.value)
      case n: IR.BoolLit              => BoolLit(n.value)
      case n: IR.StringLit            => StrLit(n.value)
      case n: IR.NullLit              => NullLit
      case n: IR.Conditional =>
        Cond(irValue(n.condition), irValue(n.ifTrue), irValue(n.ifFalse))
      case n: IR.Binary =>
        val l = irValue(n.left)
        val r = irValue(n.right)
        n.operator match {
          case IR.BinaryOp.Add            => Add(l, r)
          case IR.BinaryOp.Subtract       => Sub(l, r)
          case IR.BinaryOp.Divide         => Div(l, r)
          case IR.BinaryOp.Multiply       => Mul(l, r)
          case IR.BinaryOp.And            => And(l, r)
          case IR.BinaryOp.Or             => Or(l, r)
          case IR.BinaryOp.Equal          => Eq(l, r)
          case IR.BinaryOp.NotEqual       => Not(Eq(l, r))
          case IR.BinaryOp.Less           => Lt(l, r)
          case IR.BinaryOp.LessOrEqual    => LtEq(l, r)
          case IR.BinaryOp.Greater        => Gt(l, r)
          case IR.BinaryOp.GreaterOrEqual => GtEq(l, r)
        }
      case n: IR.Unary =>
        val x = irValue(n.operand)
        n.operator match {
          case IR.UnaryOp.Negate => Neg(x)
          case IR.UnaryOp.Not    => Not(x)
        }
    }
  }

  def fromViper(
      value: vpr.Exp,
      ctx: ConvertContext,
      old: Boolean = false
  ): Expr = {
    def isRefType(typ: vpr.Type) = typ match {
      case vpr.Ref => true
      case _ => false
    }
    println(value)
    def recurOp(value: vpr.Exp) = fromViper(value, RValue(), old)
    value match {
      case eq: vpr.EqCmp  => Eq(recurOp(eq.left), recurOp(eq.right))
      case ne: vpr.NeCmp  => Not(Eq(recurOp(ne.left), recurOp(ne.right)))
      case lt: vpr.LtCmp  => Lt(recurOp(lt.left), recurOp(lt.right))
      case lte: vpr.LeCmp => LtEq(recurOp(lte.left), recurOp(lte.right))
      case gt: vpr.GtCmp  => Gt(recurOp(gt.left), recurOp(gt.right))
      case gte: vpr.GeCmp => GtEq(recurOp(gte.left), recurOp(gte.right))

      case and: vpr.And => And(recurOp(and.left), recurOp(and.right))
      case or: vpr.Or   => Or(recurOp(or.left), recurOp(or.right))

      case add: vpr.Add => Add(recurOp(add.left), recurOp(add.right))
      case sub: vpr.Sub => Sub(recurOp(sub.left), recurOp(sub.right))
      case mul: vpr.Mul => Mul(recurOp(mul.left), recurOp(mul.right))
      case div: vpr.Div => Div(recurOp(div.left), recurOp(div.right))

      case minus: vpr.Minus => Neg(recurOp(minus.exp))
      case not: vpr.Not =>
        recurOp(not.exp) match {
          case Not(f) => f
          case x      => Not(x)
        }

      case fun: vpr.FuncApp => {
        FuncApp(fun.funcname, fun.args.map(fromViper(_, Binding(), old)))
      }

      case access: vpr.FieldAccess
        if ctx == RValue()
          && old
          && isRefType(access.field.typ) => {
        // return pointer
        val root = fromViper(access.rcv, RValue(), old)
        access.field.name match {
          case field => {
            val segments = field.split('.')
            var modifiedRoot = root
            val base =
              if (segments.length != 0) segments(segments.length - 1) else field
            val structName = base.split('$')(0)
            val fieldName = base.split('$')(1)
            if (segments.length > 1) {
              segments
                .slice(0, segments.length - 1)
                .foreach(seg => {
                  val elements = seg.split('$')
                  modifiedRoot = Field(root, elements(0), elements(1))
                })
            }
            println(Field(root, structName, "_old_" ++ fieldName))
            Field(root, "_old_" ++ structName, "_old_" ++ fieldName)
          }
        }
      }

      case access: vpr.FieldAccess => {
        println(access)
        println(access.field)
        val root = fromViper(access.rcv, LValue(), old)
        access.field.name match {
          case field => {
            val segments = field.split('.')
            var modifiedRoot = root
            val base =
              if (segments.length != 0) segments(segments.length - 1) else field
            val structName = base.split('$')(0)
            val fieldName = base.split('$')(1)
            if (segments.length > 1) {
              segments
                .slice(0, segments.length - 1)
                .foreach(seg => {
                  val elements = seg.split('$')
                  modifiedRoot = Field(root, elements(0), elements(1))
                })
            }
            Field(root, structName, fieldName)
          }
        }
      }

      case o: vpr.Old => fromViper(o.exp, ctx, old = true)

      case v: vpr.LocalVar if ctx == LValue() && old =>
        v.name match {
          case IRSilver.Names.ReturnVar => Result
          case IRSilver.Names.RenamedResult => Var(IRSilver.Names.ReservedResult)
          case id =>
            println(Var("_old_" ++ id))
            Var("_old_" ++ id)
        }

      case v: vpr.LocalVar =>
        v.name match {
          case IRSilver.Names.ReturnVar => Result
          case IRSilver.Names.RenamedResult => Var(IRSilver.Names.ReservedResult)
          case id => Var(id)
        }

      case lit: vpr.BoolLit => if (lit.value) TrueLit else FalseLit
      case lit: vpr.IntLit =>
        IntLit(
          lit.i.toInt
        ) // TODO: This could be used as a char type in some circumstances
      case _: vpr.NullLit => NullLit

      case e =>
        throw new WeaverException(
          "Cannot convert Silver expression `" + e.toString() + "`"
        )
    }
  }
}

sealed trait Location

sealed trait AtOp extends Location { val op: IR.Op }
case class Pre(override val op: IR.Op) extends AtOp {
  override def toString() = "PRE:" + op.summary
}
case class Post(override val op: IR.Op) extends AtOp {
  override def toString() = "POST:" + op.summary
}
case class LoopStart(override val op: IR.Op) extends AtOp {
  override def toString() = "START:" + op.summary
}
case class LoopEnd(override val op: IR.Op) extends AtOp {
  override def toString() = "END:" + op.summary
}
case object MethodPre extends Location {
  override def toString() = "requires"
}
case object MethodPost extends Location {
  override def toString() = "ensures"
}

sealed trait Condition
case class NotCondition(value: Condition) extends Condition
case class AndCondition(values: List[Condition]) extends Condition
case class OrCondition(values: List[Condition]) extends Condition
case class ImmediateCondition(value: CheckExpression) extends Condition
case class TrackedCondition(
    location: Location,
    value: CheckExpression
) extends Condition

case class RuntimeCheck(
    location: Location,
    check: Check,
    when: Option[Condition]
)

object RuntimeCheck {
  def dump(checks: Seq[RuntimeCheck]) = {
    System.out.println(
      checks
        .map(c => c.location.toString() + "\n" + c.check.toString())
        .mkString("\n\n")
    )
  }
}
