/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import purescala.Types.TypeTree

/** An [[ExpressionGrammar]] whose productions for a given [[Label]]
  * depend only on the underlying [[TypeTree]] of the label
  */
abstract class SimpleExpressionGrammar extends ExpressionGrammar {

  type Prod = ProductionRule[TypeTree, Expr]

  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(
      builder: => Expr,
      outType: Class[_ <: Expr],
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      weight: Double = 1.0) = {
    ProductionRule[TypeTree, Expr](Nil, { (subs: Seq[Expr]) => builder }, outType, tag, cost, weight)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(
      subs: Seq[TypeTree],
      builder: (Seq[Expr] => Expr),
      outType: Class[_ <: Expr],
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      weight: Double = 1.0) = {
    ProductionRule[TypeTree, Expr](subs, builder, outType, tag, cost, weight)
  }

  def filter(f: Prod => Boolean) = {
    new SimpleExpressionGrammar {
      def computeProductions(lab: TypeTree)(implicit ctx: LeonContext) = {
        SimpleExpressionGrammar.this.computeProductions(lab).filter(f)
      }
    }
  }

  // Finalize this to depend only on the type of the label
  final protected[grammars] def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] = {
    computeProductions(lab.getType).map { p =>
      ProductionRule(p.subTrees.map(Label(_)), p.builder, p.outType, p.tag, p.cost, p.weight)
    }
  }

  /** Version of [[ExpressionGrammar.computeProductions]] which depends only a [[TypeTree]] */
  protected[grammars] def computeProductions(tpe: TypeTree)(implicit ctx: LeonContext): Seq[Prod]
}
