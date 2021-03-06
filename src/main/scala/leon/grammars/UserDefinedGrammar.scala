/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import aspects._

import purescala.Common._
import purescala.DefOps._
import purescala.ExprOps._
import purescala.TypeOps.{instantiateType, instantiation_<:, unify}
import purescala.Definitions._
import purescala.Types._
import purescala.Expressions._

import synthesis.{SynthesisContext, FunctionCallsFinder}

object UserDefinedGrammar {
  import Tags._
  def tags = Map(
    "top" -> Top,
    "0" -> Zero,
    "1" -> One,
    "booleanC" -> BooleanC,
    "const" -> Constant,
    "and" -> And,
    "or" -> Or,
    "not" -> Not,
    "plus" -> Plus,
    "minus" -> Minus,
    "times" -> Times,
    "mod" -> Mod,
    "div" -> Div,
    "equals" -> Equals,
    "commut" -> Commut,
    "ite" -> ITE
  )
}

/** Represents a user-defined context-free grammar of expressions */
case class UserDefinedGrammar(sctx: SynthesisContext, program: Program, visibleFrom: Option[Definition], inputs: Seq[Identifier]) extends ExpressionGrammar {
  import Tags._
  import UserDefinedGrammar._
  type Prod = ProductionRule[Label, Expr]

  val visibleDefs = visibleFrom match {
    case Some(d) =>
      visibleFunDefsFrom(d)(program)
    case None =>
      visibleFunDefsFromMain(program)
  }

  case class UserProduction(fd: FunDef, tag: Tag, weight: Int)

  val userProductions = visibleDefs.toSeq.sortBy(_.id).flatMap { fd =>
    val as = fd.extAnnotations

    val isProduction = as.contains("grammar.production")

    if (isProduction) {
      val weight = as("grammar.production").head.getOrElse(1).asInstanceOf[Int]
      val tag = (for {
        t <- as.get("grammar.tag")
        t2 <- t.headOption
        t3 <- t2
        t4 <- tags.get(t3.asInstanceOf[String])
      } yield t4).getOrElse(Top)

      Some(UserProduction(fd, tag, weight))
    } else {
      None
    }
  }


  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, outType: Class[_ <: Expr], tag: Tags.Tag = Tags.Top, cost: Int, weight: Double) = {
    ProductionRule[Label, Expr](Nil, _ => builder, outType, tag, cost, weight)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[Label], builder: (Seq[Expr] => Expr), outType: Class[_ <: Expr], tag: Tags.Tag = Tags.Top, cost: Int, weight: Double) = {
    ProductionRule[Label, Expr](subs, builder, outType, tag, cost, weight)
  }

  def unwrapType(tpe: TypeTree): Option[TypeTree] = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Some(ct.fieldsTypes.head)

      case _ =>
        None
    }
  }

  def tpeToLabel(tpe: TypeTree): Label = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Label(unwrapType(tpe).get).withAspect(RealTyped(ct))

      case _ =>
        Label(tpe)
    }
  }

  def unwrapLabels(e: Expr, m: Map[Identifier, Identifier]): Expr = {
    preMap ({
      case CaseClass(cct, Seq(arg)) if cct.classDef.annotations("grammar.label") =>
        Some(arg)

      case CaseClassSelector(cct, v: Variable, id) if cct.classDef.annotations("grammar.label") =>
        m.get(v.id).map(_.toVariable)

      case _ =>
        None
    }, applyRec = true)(e)
  }

  private[this] var prodsCache = Map[TypeTree, Seq[Prod]]();

  def instantiateProductions(tpe: TypeTree): Seq[Prod] = {

    val lab = tpeToLabel(tpe)

    val types = (userProductions.collect {
      case UserProduction(fd, _, _) if fd.tparams.isEmpty => fd.returnType
    } ++ inputs.map(_.getType)).toSet

    val fcallFinder = new FunctionCallsFinder(types)


    userProductions.flatMap { case UserProduction(fd, tag, w) =>

      fcallFinder.find(fd, tpe).flatMap { tfd =>

        val tmap = (tfd.fd.tparams.map(_.tp) zip tfd.tps).toMap

        val m = fd.params.flatMap { p =>
          val ptype = instantiateType(p.id.getType, tmap)

          unwrapType(ptype).map { tpe =>
            p.id -> FreshIdentifier("p", tpe)
          }
        }.toMap


        val expr = unwrapLabels(fd.fullBody, m)

        expr match {
          // Special built-in "constructor" case, which tells us how often to
          // generate constructors of specific type
          case FunctionInvocation(TypedFunDef(fd, Seq(tp1, tp2)), Seq(rec)) if program.library.selector contains fd =>
            val recType    = instantiateType(tp1, tmap)
            val targetType = instantiateType(tp2, tmap)

            def selectors(rec: Expr, cct: CaseClassType, targetType: TypeTree): Seq[Prod] = {
              cct.fields.filter(_.getType == targetType).map { f =>
                val subs  = List(tpeToLabel(instantiateType(rec.getType, tmap)))

                nonTerminal(subs, { case List(rec) =>
                  val res = CaseClassSelector(cct, rec, f.id)
                  inlineTrivialities(res)
                }, classOf[CaseClassSelector], tag, cost = 1, w)
              }
            }

            recType match {
              case cct: CaseClassType =>
                selectors(rec, cct, targetType)

              case act: AbstractClassType =>
                act.knownCCDescendants.flatMap{ cct =>
                  selectors(rec, cct, targetType)
                }

              case _ =>
                Nil
            }

          // Special built-in "constructor" case, which tells us how often to
          // generate constructors of specific type
          case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq()) if program.library.constructor contains fd =>

            instantiateType(tp, tmap) match {
              case cct: CaseClassType =>
                List(
                  nonTerminal(cct.fields.map(f => tpeToLabel(f.getType)), CaseClass(cct, _), classOf[CaseClass], Tags.tagOf(cct), 1, 1)
                )

              case act: AbstractClassType =>
                val descendents = act.knownCCDescendants;

                descendents.map { cct =>
                  nonTerminal(cct.fields.map(f => tpeToLabel(f.getType)), CaseClass(cct, _), classOf[CaseClass], Tags.tagOf(cct), 1, 1/descendents.size)
                }

              case _ =>
                Nil
            }

          // Special built-in "variable" case, which tells us how often to
          // generate variables of specific type
          case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq()) if program.library.variable contains fd =>
            val targetType = instantiateType(tp, tmap)
            val vars = inputs.filter (_.getType == targetType)

            val size = vars.size.toDouble
            vars map (v => terminal(v.toVariable, classOf[Variable], tag, cost = 1, w/size))

          // Special built-in "closure" case, which tells us how often to
          // generate closures of a specific type
          case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq()) if program.library.closure contains fd =>
            instantiateType(tp, tmap) match {
              case FunctionType(froms, to) =>
                val args = froms.zipWithIndex.map { case (tpe, i) =>
                  ValDef(FreshIdentifier("a"+i, tpe))
                }

                val rlab = tpeToLabel(to).withAspect(aspects.ExtraTerminals(args.map(_.toVariable).toSet))

                List(nonTerminal(Seq(rlab), { case Seq(body) =>
                  Lambda(args, body)
                }, classOf[Lambda], tag, cost = 1, w))

              case _ =>
                Nil
            }

          case _ =>
            if (fd.params.isEmpty) {
              List(terminal(instantiateType(expr, tmap, Map()), classOf[Expr], tag, cost = 1, w))
            } else {
              val holes = fd.params.map(p => m.getOrElse(p.id, p.id))
              val subs  = fd.params.map {
                p => tpeToLabel(instantiateType(p.getType, tmap))
              }

              val replacer = variableReplacer(expr, holes)

              List(nonTerminal(subs, { sexprs => 
                instantiateType(replacer(sexprs), tmap, m)
              }, classOf[Expr], tag, cost = 1, w))
            }
        }
      }
    }
  }

  protected[grammars] def computeProductions(lab: Label)(implicit ctx: LeonContext) = {
    val realType = lab.aspects.collect {
      case RealTyped(tpe) => tpe
    }.headOption.getOrElse(lab.getType)

    val prods = prodsCache.getOrElse(realType, {
      val res = instantiateProductions(realType)
      prodsCache += realType -> res
      res
    })

    val ws = prods map (_.weight)

    if (ws.isEmpty) {
      Nil
    } else if (ws.size == 1) {
      prods.map(_.copy(weight = 1))
    } else {
      val sum = ws.sum
      // log(prob) = log(weight/Σ(weights))
      val logProbs = ws.map(w => Math.log(w/sum))
      val maxLogProb = logProbs.max

      for ((p, logProb) <- prods zip logProbs) yield {
        // cost = normalized log prob.
        val cost = (logProb/maxLogProb).round.toInt
        p.copy(cost = cost, weight = logProb)
      }
    }
  }

}
