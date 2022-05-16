package gvc.permutation
import gvc.transformer.IR
import gvc.transformer.IR.{Block, Expression, Method, Predicate}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType

object SpecType extends Enumeration {
  type SpecType = Value
  val Assert, Precondition, Postcondition, Fold, Unfold, Invariant, Predicate =
    Value
}

object ExprType extends Enumeration {
  type ExprType = Value
  val Accessibility, Predicate, Default = Value
}

abstract class SpecVisitor[I, O] {
  var exprIndex = 0
  var specIndex = 0
  var currentContext: Option[Either[Method, Predicate]] = None

  def reset(): Unit = {
    exprIndex = 0
    specIndex = 0
  }

  def previousExpr(): Int = this.exprIndex - 1
  def previousSpec(): Int = this.specIndex - 1

  def visitSpecExpr(
      parent: Either[Method, Predicate],
      template: Expression,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    currentContext = Some(parent)
    exprIndex += 1
  }

  def visitSpecOp(
      parent: Either[Method, Predicate],
      template: IR.Op,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    currentContext = Some(parent)
    exprIndex += 1
  }
  def enterSpec(expr: Option[Expression] = None): Unit = {}

  def leaveSpec(): Unit = {
    this.specIndex += 1
  }

  def visitOp(parent: Either[Method, Predicate], template: IR.Op): Unit = {
    currentContext = Some(parent)
  }

  def visit(input: IR.Program): O = {
    new SpecTraversal[I, O]().visitAST(input, this)
    val output = collectOutput()
    reset()
    output
  }

  def collectAssertion(): Unit
  def collectIf(stmt: IR.If): Unit
  def collectConditional(cond: IR.Conditional): Unit
  def collectWhile(whl: IR.While): Unit

  def enterExpr(): Unit
  def leaveExpr(): Unit
  def enterBlock(): Unit
  def leaveBlock(): Unit

  def leavePredicate(predicate: Predicate): Unit
  def enterPredicate(predicate: Predicate): Unit

  def leaveMethod(method: Method): Unit
  def enterMethod(method: Method): Unit

  def collectOutput(): O
}

class SpecTraversal[I, O] {
  def visitAST(program: IR.Program, visitor: SpecVisitor[I, O]): Unit = {
    program.methods.foreach(visitMethod(_, visitor))
    program.predicates.foreach(visitPredicate(_, visitor))
  }

  class SpecVisitorException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  private def visitPredicate(
      predicate: Predicate,
      visitor: SpecVisitor[I, O]
  ): Unit = {
    visitor.enterPredicate(predicate)
    visitor.enterSpec(Some(predicate.expression))
    visitExpression(
      Right(predicate),
      SpecType.Predicate,
      Some(predicate.expression),
      visitor
    )
    visitor.leaveSpec()
    visitor.leavePredicate(predicate)
  }

  private def visitMethod(method: Method, visitor: SpecVisitor[I, O]): Unit = {
    visitor.enterMethod(method)

    visitor.enterSpec(method.precondition)
    visitExpression(
      Left(method),
      SpecType.Precondition,
      method.precondition,
      visitor
    )
    visitor.leaveSpec()

    visitor.enterSpec(method.postcondition)
    visitExpression(
      Left(method),
      SpecType.Postcondition,
      method.postcondition,
      visitor
    )
    visitor.leaveSpec()

    visitBlock(
      method,
      method.body,
      visitor
    )

    visitor.leaveMethod(method)
  }

  private def visitBlock(
      context: Method,
      block: Block,
      visitor: SpecVisitor[I, O]
  ): Unit = {
    visitor.enterBlock()
    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case assert: IR.Assert =>
          if (assert.kind == IR.AssertKind.Specification) {
            visitor.enterSpec(Some(assert.value))
            visitExpression(
              Left(context),
              SpecType.Assert,
              Some(assert.value),
              visitor
            )
            visitor.leaveSpec()
            visitor.collectAssertion()
          } else {
            visitor.visitOp(Left(context), op)
          }
        case _: IR.Fold =>
          visitor.enterSpec()
          visitor.visitSpecOp(
            Left(context),
            op,
            SpecType.Fold,
            ExprType.Predicate
          )
          visitor.leaveSpec()
        case _: IR.Unfold =>
          visitor.enterSpec()
          visitor.visitSpecOp(
            Left(context),
            op,
            SpecType.Unfold,
            ExprType.Predicate
          )
          visitor.leaveSpec()
        case ifstmt: IR.If =>
          visitBlock(context, ifstmt.ifTrue, visitor)
          visitBlock(context, ifstmt.ifFalse, visitor)
          visitor.collectIf(ifstmt)
        case whl: IR.While =>
          visitor.enterSpec(Some(whl.invariant))
          visitExpression(
            Left(context),
            SpecType.Invariant,
            Some(whl.invariant),
            visitor
          )
          visitor.leaveSpec()
          visitBlock(context, whl.body, visitor)
          visitor.collectWhile(whl)
        case _ => visitor.visitOp(Left(context), op)
      }
    }
    visitor.leaveBlock()
  }

  private def visitExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      visitor: SpecVisitor[I, O]
  ): Unit = {
    visitor.enterExpr()
    buildExpression(context, specType, expression, visitor)
    visitor.leaveExpr()
  }

  private def buildExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      visitor: SpecVisitor[I, O]
  ): Unit = {
    expression match {
      case Some(expr) =>
        expr match {
          case _: IR.Accessibility =>
            visitor.visitSpecExpr(
              context,
              expr,
              specType,
              ExprType.Accessibility
            )
          case _: IR.PredicateInstance =>
            visitor.visitSpecExpr(
              context,
              expr,
              specType,
              ExprType.Predicate
            )
          case imprecise: IR.Imprecise =>
            buildExpression(
              context,
              specType,
              imprecise.precise,
              visitor
            )
          case conditional: IR.Conditional =>
            visitExpression(
              context,
              specType,
              Some(conditional.ifTrue),
              visitor
            )
            visitExpression(
              context,
              specType,
              Some(conditional.ifFalse),
              visitor
            )
            visitor.collectConditional(conditional)
          case binary: IR.Binary =>
            if (binary.operator == IR.BinaryOp.And) {
              buildExpression(context, specType, Some(binary.right), visitor)
              buildExpression(context, specType, Some(binary.left), visitor)
            } else {
              visitor.visitSpecExpr(
                context,
                expr,
                specType,
                exprType = ExprType.Default
              )
            }
          case _ =>
            visitor.visitSpecExpr(
              context,
              expr,
              specType,
              exprType = ExprType.Default
            )
        }
      case None =>
    }
  }
}
