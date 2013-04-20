/*
 * Copyright (c) 2012-13 Miles Sabin 
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless

import scala.language.experimental.macros

import scala.collection.breakOut
import scala.reflect.macros.Context

/**
 * Representation of an isomorphism between a type (typically a case class) and an `HList`.
 */
trait Iso[T, U] { self =>
  def to(t : T) : U
  def from(u : U) : T

  def reverse : Iso[U, T] = new Iso[U, T] {
    def to(u : U) : T = self.from(u)
    def from(t : T) : U = self.to(t)

    override def reverse = self
  }
}

object Iso {
  import Functions._
  import Tuples._

  def apply[T, U](implicit iso: Iso[T, U]) = iso

  implicit def materialize[T, U]: Iso[T, U] = macro IsoMacros.materializeImpl[T, U]
  
  implicit def identityIso[T]: Iso[T, T] = new Iso[T, T] {
    def to(t : T) : T = t
    def from(t : T) : T = t
  }

  implicit def tupleHListIso[T <: Product, L <: HList](implicit hl : HListerAux[T, L], uhl : TuplerAux[L, T]): Iso[T, L] =
    new Iso[T, L] {
      val ctor = uhl.apply _
      val dtor = hl.apply _
      def to(t : T) : L = dtor(t)
      def from(l : L) : T = ctor(l)
    }


  implicit def fnHListFnIso[F, L <: HList, R](implicit hl : FnHListerAux[F, L => R], unhl : FnUnHListerAux[L => R, F]): Iso[F, L => R] =
    new Iso[F, L => R] {
      def to(f : F) : L => R = hl(f)
      def from(l : L => R) = unhl(l)
    }
}

object IsoMacros {
  def materializeImpl[T: c.WeakTypeTag, U: c.WeakTypeTag](c : Context): c.Expr[Iso[T, U]] = {
    import c.universe._
    import definitions._
    import Flag._

    val isoSym = c.mirror.staticClass("shapeless.Iso")
    
    val shapelessNme = newTermName("shapeless")
    val inlSel = Select(Ident(shapelessNme), newTermName("Inl"))
    val inrSel = Select(Ident(shapelessNme), newTermName("Inr"))
      
    val pendingSuperCall = Apply(Select(Super(This(tpnme.EMPTY), tpnme.EMPTY), nme.CONSTRUCTOR), List())
  
    def mkProductIso(tpe: Type, sym: ClassSymbol): ClassDef = {
      val fields = tpe.declarations.toList.collect {
        case x: TermSymbol if x.isVal && x.isCaseAccessor => x
      }
  
      val HNilTypeTree   = Select(Ident(newTermName("shapeless")), newTypeName("HNil"))
      val HNilValueTree  = Select(Ident(newTermName("shapeless")), newTermName("HNil"))
  
      val HConsTypeTree  = Select(Ident(newTermName("shapeless")), newTypeName("$colon$colon"))
      val HConsValueTree = Select(Ident(newTermName("shapeless")), newTermName("$colon$colon"))
  
      def mkHListType: Tree = {
        fields.map { f => TypeTree(f.typeSignatureIn(tpe)) }.foldRight(HNilTypeTree : Tree) {
          case (t, acc) => AppliedTypeTree(HConsTypeTree, List(t, acc))
        }
      }
  
      def mkHListValue: Tree = {
        fields.map(_.name.toString.trim).foldRight(HNilValueTree : Tree) {
          case (v, acc) => Apply(HConsValueTree, List(Select(Ident(newTermName("t")), newTermName(v)), acc))
        }
      }
  
      def mkNth(n: Int): Tree =
        Select(
          (0 until n).foldRight(Ident(newTermName("u")) : Tree) {
            case (_, acc) => Select(acc, newTermName("tail"))
          },
          newTermName("head")
        )
  
      def mkCaseClassValue: Tree =
        Apply(
          Select(Ident(sym.companionSymbol), newTermName("apply")),
          (0 until fields.length).map(mkNth(_)).toList
        )
  
      ClassDef(Modifiers(FINAL), newTypeName("$anon"), List(),
        Template(
          List(AppliedTypeTree(Ident(isoSym), List(TypeTree(tpe), mkHListType))),
          emptyValDef,
          List(
            DefDef(
              Modifiers(), nme.CONSTRUCTOR, List(),
              List(List()),
              TypeTree(),
              Block(List(pendingSuperCall), Literal(Constant(())))),

            DefDef(
              Modifiers(), newTermName("to"), List(),
              List(List(ValDef(Modifiers(PARAM), newTermName("t"), TypeTree(tpe), EmptyTree))),
              TypeTree(),
              mkHListValue),

            DefDef(
              Modifiers(), newTermName("from"), List(),
              List(List(ValDef(Modifiers(PARAM), newTermName("u"), mkHListType, EmptyTree))),
              TypeTree(),
              mkCaseClassValue)
          )
        )
      )
    }
    
    def mkCoproductIso(base: TypeRef, sym: ClassSymbol): ClassDef = {
      def normalize(elem: Symbol): Option[TypeTree] = {
        val elemTpe = elem.asType.toType
        elem.asClass.typeParams match {
          case Nil => if (elemTpe <:< base) Some(TypeTree(elemTpe)) else None
          case tpes =>
            val appliedTpe = appliedType(elemTpe, base.args) 
            if (appliedTpe <:< base) Some(TypeTree(appliedTpe)) else None
        }
      }

      val elems = sym.knownDirectSubclasses.toList.flatMap(normalize(_))
      
      val CoproductTypeTree  = Select(Ident(newTermName("shapeless")), newTypeName("$colon$plus$colon"))
  
      def mkCoproductType: Tree =
        elems.reduceRight(
          (a: TypeTree, b: Tree) => AppliedTypeTree(CoproductTypeTree, List(a, b))
        )
      
      def mkCoproductValue(i: Int): Tree = {
        val last = i == elems.length-1
        def loop(j: Int): Tree =
          if(j == 0) {
            if(last)
              Ident(newTermName("x"))
            else
              Apply(
                Select(inlSel, newTermName("apply")),
                List(Ident(newTermName("x")))
              )
          } else {
            Apply(
              Select(inrSel, newTermName("apply")),
              List(loop(j-1))
            )
          }
        loop(i)
      }
      
      def mkToCase(i: Int): CaseDef = 
        CaseDef(Bind(newTermName("x"), Typed(Ident(nme.WILDCARD), elems(i))), EmptyTree, mkCoproductValue(i))
      
      def mkCoproductPattern(i: Int): Tree = {
        val last = i == elems.length-1
        def loop(j: Int): Tree =
          if(j == 0) {
            if(last)
              Bind(newTermName("x"), Ident(nme.WILDCARD))
            else
              Apply(inlSel,
                List(
                  Bind(newTermName("x"), Ident(nme.WILDCARD))))
          } else {
            Apply(inrSel, List(loop(j-1)))
          }
        loop(i)
      }

      def mkFromCase(i: Int): CaseDef =
        CaseDef(mkCoproductPattern(i), EmptyTree, Ident(newTermName("x")))
      
      ClassDef(
        Modifiers(FINAL), newTypeName("$anon"), List(),
        Template(
          List(AppliedTypeTree(Ident(isoSym), List(TypeTree(base), mkCoproductType))),
          emptyValDef,
          List(
            DefDef(Modifiers(), nme.CONSTRUCTOR, List(),
              List(List()),
              TypeTree(),
              Block(List(pendingSuperCall), Literal(Constant(())))),
            DefDef(Modifiers(), newTermName("to"), List(),
              List(List(ValDef(Modifiers(PARAM), newTermName("t"), TypeTree(base), EmptyTree))),
              mkCoproductType,
              Match(
                Ident(newTermName("t")),
                (0 until elems.length).map(mkToCase(_))(breakOut)
              )
            ),
            DefDef(Modifiers(), newTermName("from"), List(),
              List(List(ValDef(Modifiers(PARAM), newTermName("u"), mkCoproductType, EmptyTree))),
              TypeTree(base),
              Match(
                Ident(newTermName("u")),
                (0 until elems.length).map(mkFromCase(_))(breakOut)
              )
            )
          )
        )
      )
    }

    val tpe = c.weakTypeOf[T]
    val sym = tpe.typeSymbol
    
    def badType() = 
      c.abort(c.enclosingPosition, s"$sym is not a case class or a sealed trait or abstract class")

    if (!sym.isClass) badType()
    val classSym = sym.asClass 
      
    val isoClass =
      if (classSym.isCaseClass)
        mkProductIso(tpe, classSym)
      else if (classSym.isSealed)
        tpe match {
          case base: TypeRef => mkCoproductIso(base, classSym)
          case _ => badType()
        }
      else
        badType()
      
    c.Expr[Iso[T, U]](
      Block(
        List(isoClass),
        Apply(Select(New(Ident(newTypeName("$anon"))), nme.CONSTRUCTOR), List())
      )
    )
  }
}

// vim: expandtab:ts=2:sw=2
