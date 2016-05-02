package leon
package laziness

import invariant.util._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import LazinessUtil._
import ProgramUtil._

class FunctionsManager(p: Program) {

  // includes calls made through the specs
  val cg = CallGraphUtil.constructCallGraph(p, false, true,
    // a specialized callee function that ignores functions called inside `withState` calls, because they would have state as an argument
    (inexpr: Expr) => {
      var callees = Set[FunDef]()
      def rec(e: Expr): Unit = e match {
        case cc @ CaseClass(_, args) if isWithStateCons(cc)(p) =>
          ; //nothing to be done
        case f : FunctionInvocation if isIsFun(f)(p) =>
          // we can ignore the arguments to susp invocation as they are not actual calls, but only a test
          ;
        case cc : CaseClass if isMemCons(cc)(p) =>
          ; // we can ignore the arguments to mem
        //note: do not consider field invocations
        case f @ FunctionInvocation(TypedFunDef(callee, _), args) if callee.isRealFunction =>
          callees += callee
          args map rec
        case Operator(args, _) => args map rec
      }
      rec(inexpr)
      callees
    })

  /*
   * Lambdas need not be a part of read roots, because its body needs state, the function creating lambda will be
   * marked as needing state.
   * TODO: why are all applications ValRoots ? Only those applications that may call a memoized function  should be
   * valroots ?
   */
  val (funsNeedStates, funsRetStates, funsNeedStateTps) = {
    var starRoots = Set[FunDef]()
    var readRoots = Set[FunDef]()
    var valRoots = Set[FunDef]()
    userLevelFunctions(p).foreach {
      case fd if fd.hasBody =>
        def rec(e: Expr): Unit = e match {
          case finv@FunctionInvocation(_, Seq(CaseClass(_, Seq(invExpr)))) if isStarInvocation(finv)(p) =>
            starRoots += fd
            invExpr match {
              case Application(l, args) => // we need to prevent the application here from being treated as a `val` root
                (l +: args) foreach rec
              case FunctionInvocation(_, args) =>
                args foreach rec
            }
          case finv@FunctionInvocation(_, args) if cachedInvocation(finv)(p) =>
            readRoots += fd
            args foreach rec
          case Application(l, args) =>
            valRoots += fd
            (l +: args) foreach rec
          case FunctionInvocation(tfd, args) if isMemoized(tfd.fd) =>
            valRoots += fd
            args foreach rec
          case Operator(args, _) =>
            args foreach rec
        }
        rec(fd.body.get)
      case _ => ;
    }
    val valCallers = cg.transitiveCallers(valRoots.toSeq)
    val readfuns = cg.transitiveCallers(readRoots.toSeq)
    val starCallers = cg.transitiveCallers(starRoots.toSeq)
    println("Ret roots: "+valRoots.map(_.id)+" ret funs: "+valCallers.map(_.id))
    println("Read roots: "+readRoots.map(_.id)+" read funs: "+readfuns.map(_.id))
    (readfuns ++ valCallers, valCallers, starCallers ++ readfuns ++ valCallers)
  }

  lazy val callersnTargetOfLambdas = {
    var consRoots = Set[FunDef]()
    //var targets = Set[F]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case l: Lambda =>
            consRoots += fd
            //targets += l
          case _ =>
        }(fd.body.get)
      case _ => ;
    }
    cg.transitiveCallers(consRoots.toSeq) //++ targets
  }

  lazy val cgWithoutSpecs = CallGraphUtil.constructCallGraph(p, true, false)
  lazy val callersOfCached = {
    var roots = Set[FunDef]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case finv: FunctionInvocation if cachedInvocation(finv)(p) =>
            roots += fd
          case _ =>
            ;
        }(fd.body.get)
      case _ => ;
    }
    cgWithoutSpecs.transitiveCallers(roots.toSeq)
  }

  def isRecursive(fd: FunDef) : Boolean = {
    cg.isRecursive(fd)
  }

  def hasStateIndependentBehavior(fd: FunDef) : Boolean = {
    // every function that does not call isEvaluated or is Susp has a state independent behavior
    !callersOfCached.contains(fd)
  }
}
