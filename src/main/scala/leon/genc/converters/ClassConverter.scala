/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package converters

import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

import utils.Position

import ExtraOps._

private[converters] trait ClassConverter {
  this: Converters with Normaliser with Builder with MiniReporter =>

  // This registery keeps track of the "top" C structure that represents the class hierarchy.
  private var classRegistery = Map[CaseClassType, CAST.Struct]()

  // Add the given set of ClassDef into the registery
  private def registerFullHierarchy(top: CAST.Struct, set: Seq[CaseClassType]) {
    debug(s"Registering hierarchy with $top for ${set map { _.id }}")

    for (clazz <- set)
      classRegistery = classRegistery + (clazz -> top)
  }

  // Find the matching "top" C struct for a given class definition. If none exists,
  // the definition needs to be processed through convertClass.
  private def getTopStruct(cct: CaseClassType): Option[CAST.Struct] = classRegistery.get(cct)

  // Make the id specific to the current type specialisation and no longer generic
  private def generateClassId(ct: ClassType)(implicit funCtx: FunCtx): CAST.Id = {
    if (ct.classDef.isGeneric) {
      val baseId = ct.id.uniqueName
      val paramId = ct.tps map { t => convertToType(t).name } mkString (sep = "_")
      CAST.Id(baseId + "_" + paramId)
    } else convertToId(ct.id)
  }

  // Register a hierarchy of class.
  //
  // - Find the top abstract class
  // - List all concreate classes
  // - Create a C enum with a value for each concreate class
  // - Create a C struct for each child
  // - Create a C struct with a union member having an entry for each concreate class
  // - Register the enum, union & the structs to ProgConverter
  // - Register the class hierarchy as well
  // - Return the struct representing this class hierarchy
  private def registerClassHierarchy(ct: ClassType)(implicit funCtx: FunCtx): CAST.Type = {
    val top = ct.getTopParent
    val id = generateClassId(top)

    getType(id) getOrElse {
      val children = top.knownCCDescendants

      debug(s"Registrering class hierarchy of ${ct.id}")
      debug(s"Top = ${top.id}")
      debug(s"Children = ${ children map { _.id } mkString ", " }")

      val childrenStructs = children map registerClass

      val name = id.name
      val enumId = CAST.Id(s"tag_${name}_t")

      val enumValues = childrenStructs map { s => CAST.Enum.tagForType(s) }
      val enumType = CAST.Enum(enumId, enumValues)

      val unionType = CAST.Union(CAST.Id(s"union_$name"), childrenStructs)

      val tag = CAST.Var(CAST.Id("tag"), enumType)
      val union = CAST.Var(CAST.Id("value"), unionType)

      val typ = CAST.Struct(CAST.Id(name), tag :: union :: Nil)

      registerEnum(enumType)
      registerType(unionType)
      registerType(typ)

      registerFullHierarchy(typ, children)

      typ
    }
  }

  // The correct type is stored in the ClassType but the correct Ids are stored in the ClassDef!
  private def convertFields(ct: ClassType)(implicit funCtx: FunCtx): Seq[CAST.Var] = {
    val fieldsIds = ct.classDef.fields map { f => convertToId(f.id) }
    val fieldsTypes = ct.fields map { f => convertToType(f.getType) }
    val fields = (fieldsIds zip fieldsTypes) map { case (id, typ) => CAST.Var(id, typ) }
    fields
  }

  // Register a given class (if needed) after converting its data structure to a C one.
  // NOTE it is okay to call this function more than once on the same class definition.
  private def registerClass(ct: ClassType)(implicit funCtx: FunCtx): CAST.Type = {
    val id = generateClassId(ct)

    val typ = getType(id)
    typ foreach { t => debug(s"$t is already defined") }

    typ getOrElse {
      val fields = convertFields(ct)
      val typ = CAST.Struct(id, fields)

      registerType(typ)
      typ
    }
  }

  // Common core of the two convertClass functions; handle some annotation checking.
  private def convertClassCore(cd: ClassDef): Option[CAST.Type] = {
    debug(s"Processing ${cd.id} with annotations: ${cd.annotations}")

    implicit val pos = cd.getPos

    if (cd.isManuallyTyped && cd.isDropped)
      CAST.unsupported(s"${cd.id} cannot be both dropped and manually defined")

    if (cd.isGeneric && cd.isManuallyTyped)
      CAST.unsupported(s"${cd.id} cannot be both a generic type and manually defined")

    if (!cd.isManuallyTyped) {
      if (cd.isCaseObject)       CAST.unsupported("Case Objects")
      if (cd.methods.length > 0) CAST.unsupported("Methods") // TODO is it?
    }

    if (cd.isDropped) Some(CAST.NoType)
    else if (!cd.isGeneric) getTypedef(cd)
    else None
  }

  // Convert a given class into a C structure; make some additional checks to
  // restrict the input class to the supported set of features.
  // NOTE return NoType when given a generic class definition.
  def convertClass(cd: ClassDef)(implicit funCtx: FunCtx): CAST.Type = convertClassCore(cd) getOrElse {
    if (cd.isGeneric) {
      debug(s"${cd.id} is generic => cannot convert it now, only when instantiated with concreate type parameters")
      CAST.NoType
    } else {
      // Handle inheritance
      if (cd.isCandidateForInheritance) registerClassHierarchy(cd.typed)
      else registerClass(cd.typed)
    }
  }

  // Relatively similar to convertClass but not suggering from generics
  def convertClass(ct: ClassType)(implicit funCtx: FunCtx): CAST.Type = convertClassCore(ct.classDef) getOrElse {
    // Handle inheritance
    if (ct.classDef.isCandidateForInheritance) registerClassHierarchy(ct)
    else registerClass(ct)
  }

  // Instantiate a given case class, taking into account the inheritance model
  def instantiateCaseClass(cct: CaseClassType, args1: Seq[Expr])(implicit funCtx: FunCtx): CAST.Stmt = {
    def details(struct: CAST.Struct): (Seq[CAST.Stmt], CAST.StructInit) = {
      val types = struct.fields map { _.typ }
      val argsFs = convertAndNormaliseExecution(args1, types)
      val fieldsIds = convertFields(cct) map { _.id }
      val args = fieldsIds zip argsFs.values

      (argsFs.bodies, CAST.StructInit(args, struct))
    }

    def normalInstantiation: CAST.Stmt = {
      val struct = convertToStruct(cct)
      val (pre, act) = details(struct)

      pre ~~ act
    }

    def abstractInstantiation(top: CAST.Struct): CAST.Stmt = {
      // Here is an example of how such init might look like:
      // struct T t = (struct T){ .tag = INT, .value.t1 = (struct TINT){ .x = 42 } };
      //
      // We need to identify the tag and the value name first,
      // then how to init the value properly.

      debug(s"Instantiating ${cct.id} with arguments $args1.")

      val dataStruct = getStruct(generateClassId(cct)).get // if None, then internalError anyway
      val tag = CAST.Enum.tagForType(dataStruct)
      val value = CAST.Union.valuePathForType(dataStruct)

      debug(s"Concreate struct: $dataStruct")
      debug(s"Tag: $tag, value: $value")

      val (pre, dataInit) = details(dataStruct)
      val args = (CAST.Id("tag") -> tag) :: (value -> dataInit) :: Nil

      debug(s"dataInit: $dataInit")

      pre ~~ CAST.StructInit(args, top)
    }

    getTopStruct(cct) match {
      case None => normalInstantiation
      case Some(top) => abstractInstantiation(top)
    }
  }

  // Convert the expr.isInstanceOf[ct] for types involving inheritance into the proper check
  // of the tag value.
  def convertIsInstanceOf(expr: Expr, ct: ClassType)(implicit pos: Position, funCtx: FunCtx): CAST.Stmt = {
    checksForInstanceOf(ct.classDef)

    val exprF = convertAndFlatten(expr)

    val dataStruct = getStruct(generateClassId(ct)).get // if None, then internalError anyway
    val tag = CAST.Enum.tagForType(dataStruct)

    val tagField = CAST.AccessField(exprF.value, CAST.Id("tag"))

    exprF.body ~~ buildBinOp(tagField, "==", tag)
  }

  // The conversion of expr.asInstanceOf[ct] is rather straighforward: we simply access the proper value
  // from the instance's union.
  def convertAsInstanceOf(expr: Expr, ct: ClassType)(implicit pos: Position, funCtx: FunCtx): CAST.Stmt = {
    checksForInstanceOf(ct.classDef)

    val exprF = convertAndFlatten(expr)

    val dataStruct = getStruct(generateClassId(ct)).get // if None, then internalError anyway
    val valuePath = CAST.Union.valuePathForType(dataStruct)

    val valueField = CAST.AccessField(exprF.value, valuePath)

    exprF.body ~~ valueField
  }

  private def checksForInstanceOf(cd: ClassDef)(implicit pos: Position) = {
    if (!cd.isCandidateForInheritance)
      CAST.unsupported(s"IsInstanceOf w/ ${cd.id} doesn't involve inheritance")

    if (cd.isAbstract)
      CAST.unsupported(s"IsInstanceOf w/ ${cd.id} doesn't work on abstract types")
  }

}

