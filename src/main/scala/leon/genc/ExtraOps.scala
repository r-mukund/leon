/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Common._
import purescala.Definitions._
import purescala.Types._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

private[genc] trait ExtraOps {
  this: CConverter with MiniReporter =>

  // Extra tools on FunDef, especially for annotations
  implicit class FunDefOps(val fd: FunDef) {
    def isMain = fd.id.name == "main"

    def isExtern          = hasAnnotation("extern")
    def isDropped         = hasAnnotation("cCode.drop")
    def isManuallyDefined = hasAnnotation(manualDefAnnotation)

    def getManualDefinition = {
      assert(isManuallyDefined)

      val Seq(Some(code0), includesOpt0) = fd.extAnnotations(manualDefAnnotation)
      val code      = code0.asInstanceOf[String]
      val includes0 = includesOpt0 map { _.asInstanceOf[String] } getOrElse ""

      val includes =
        if (includes0.isEmpty) Nil
        else { includes0 split ':' }.toSeq

      ManualDef(code, includes)
    }

    case class ManualDef(code: String, includes: Seq[String])

    private def hasAnnotation(annot: String) = fd.annotations contains annot
    private val manualDefAnnotation = "cCode.function"
  }

  // Extra tools on ClassDef, especially for annotations, inheritance and generics
  implicit class ClassDefOps(val cd: ClassDef) {
    def isManuallyTyped = hasAnnotation(manualTypeAnnotation)
    def isDropped       = hasAnnotation(droppedAnnotation)

    def getManualType = {
      assert(isManuallyTyped)

      val Seq(Some(alias0), includesOpt0) = cd.extAnnotations(manualTypeAnnotation)
      val alias   = alias0.asInstanceOf[String]
      val include = includesOpt0 map { _.asInstanceOf[String] } getOrElse ""

      ManualType(alias, include)
    }

    case class ManualType(alias: String, include: String)

    def getTopParent: ClassDef = {
      cd.parent map { case AbstractClassType(acd, _) => acd.getTopParent } getOrElse { cd }
    }

    def isCandidateForInheritance = cd.isAbstract || cd.hasParent

    def isGeneric = cd.tparams.length > 0

    // Create a new ClassDef for the given class with the proper fields and parent/children
    // types so that no type parameters remain.
    private[ExtraOps] def generateDef(tps: Seq[TypeTree]): ClassDef = {
      require(tps.length == cd.tparams.length)

      if (!cd.methods.isEmpty)
        internalError(s"Unexpected type with methods ${cd.id}")

      val subst_ = {
        val current = cd.tparams map { _.tp }
        Map[TypeTree, TypeTree](current zip tps: _*)
      }
      def subst(t: TypeTree): TypeTree = subst_.getOrElse(t, t)

      def ccImpl(cd: CaseClassDef): CaseClassDef = {
        // The id has to be a deterministic function of the type parameters
        // used to instantiate the class
        val baseId = cd.id.uniqueName
        implicit val funCtx = FunCtx.empty
        val paramId = tps map { t => convertToType(t).name } mkString (sep = "_")
        val id = cd.id.hackDuplicate(name = baseId + "_" + paramId)

        debug(s"${cd.id} with params $tps is renamed to $id")

        val tparams = Nil
        val fields = cd.fields map valImpl
        val parent = cd.parent map { _.generateDef.asInstanceOf[AbstractClassDef].typed }

        cd.duplicate(id, tparams, fields, parent)
      }

      def acImpl(cd: AbstractClassDef): AbstractClassDef = {
        ???
      }

      def valImpl(vd: ValDef): ValDef = {
        val id = vd.id.hackDuplicate(tpe = subst(vd.getType))
        vd.copy(id = id)
      }

      getTopParent match {
        case ccd: CaseClassDef => ccImpl(ccd)
        case acd: AbstractClassDef => acImpl(acd)
      }
    }

    private def hasAnnotation(annot: String) = cd.annotations contains annot
    private val manualTypeAnnotation = "cCode.typedef"
    private val droppedAnnotation = "cCode.drop"
  }

  // Extra tools on ClassType
  implicit class ClassTypeOps(val ct: ClassType) {
    // See ClassDefOps.generateDef
    def generateDef: ClassDef = {
      // NOTE we don't use  e.g. ClassType.fields even though the types are correct. The
      //      problem is that the identifiers change and therefore would mess field access
      //      in the rest of the code. And we don't want to substitute the class type in
      //      the AST (because GenC's structure doesn't allow that easily).
      ct.classDef.generateDef(ct.tps)
    }
  }
}

