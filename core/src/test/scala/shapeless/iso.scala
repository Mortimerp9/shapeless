/*
 * Copyright (c) 2013 Miles Sabin 
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

import org.junit.Test
import org.junit.Assert._

class IsoTests {
  def typed[T](t : => T) {}

  sealed trait Fruit
  case class Apple() extends Fruit
  case class Pear() extends Fruit
  case class Banana() extends Fruit
  case class Orange() extends Fruit

  type APBO = Apple :+: Pear :+: Banana :+: Orange
  
  object showFruit extends Poly1 {
    implicit def caseApple  = at[Apple](_ => "Pomme")
    implicit def casePear   = at[Pear](_ => "Poire")
    implicit def caseBanana = at[Banana](_ => "Banane")
    implicit def caseOrange = at[Orange](_ => "Orange")
  }
  
  sealed trait AbstractSingle
  case class Single() extends AbstractSingle
    
  sealed trait Tree[T]
  case class Node[T](left: Tree[T], right: Tree[T]) extends Tree[T]
  case class Leaf[T](t: T) extends Tree[T]
  
  sealed trait Enum
  case object A extends Enum
  case object B extends Enum
  case object C extends Enum
  
  type ABC = A.type :+: B.type :+: C.type
  
  object pickFruit extends Poly1 {
    implicit def caseA = at[A.type](_ => Apple())
    implicit def caseB = at[B.type](_ => Banana())
    implicit def caseC = at[C.type](_ => Pear())
  }
  
  type ABP = Apple :+: Banana :+: Pear

  case class Company(depts : List[Dept])
  sealed trait Subunit
  case class Dept(name : Name, manager : Manager, subunits : List[Subunit]) extends Subunit
  case class Employee(person : Person, salary : Salary) extends Subunit
  case class Person(name : Name, address : Address)
  
  case class Salary(salary : Double)

  type Manager = Employee
  type Name = String
  type Address = String

  trait starLP extends Poly1 {
    implicit def default[T] = at[T](identity)
  }
  
  object star extends starLP {
    implicit def caseString = at[String](_+"*")
    implicit def caseIso[T, L <: HList](implicit iso: Iso[T, L], mapper: MapperAux[this.type, L, L]) = at[T](t => iso.from(iso.to(t).map(star))) 
  }
  
  import scala.collection.immutable.{ :: => Cons }
    
  trait incLLp extends Poly1 {
    implicit def default[T]: Pullback1[T, T] = at[T](identity)
  }
  
  trait incLp extends incLLp {
    implicit def caseProduct[T, L <: HList](implicit iso: Iso[T, L], mapper: MapperAux[inc.type, L, L]): Pullback1[T, T] = at[T](t => iso.from(iso.to(t).map(inc))) 
  }
  
  object inc extends incLp {
    implicit def caseInt: Pullback1[Int, Int] = at[Int](_+1)
    implicit def caseCoproduct[T, C1, C2](implicit iso: Iso[T, C1 :+: C2], mapper: CPMapperAux[inc.type, C1 :+: C2, C1 :+: C2]): Pullback1[T, T] = at[T](t => iso.from(iso.to(t).map(inc))) 
  }

  @Test
  def testProductBasics {
    val p = Person("Joe Soap", "Brighton")
    type SS = String :: String :: HNil
    val iso = Iso[Person, SS]
    
    val p0 = iso.to(p)
    typed[SS](p0)
    assertEquals("Joe Soap" :: "Brighton" :: HNil, p0)
    
    val p1 = iso.from(p0)
    typed[Person](p1)
    assertEquals(p, p1)
  }
  
  @Test
  def testProductMapBasics {
    val p = Person("Joe Soap", "Brighton")
    
    val p0 = star(p)
    typed[Person](p0)
    assertEquals(Person("Joe Soap*", "Brighton*"), p0)
  }
  
  @Test
  def testProductNestedMap {
    val p = Person("Joe Soap", "Brighton")
    val e = Employee(p, Salary(2000))
    
    val e0 = star(e)
    typed[Employee](e0)
    assertEquals(Employee(Person("Joe Soap*", "Brighton*"), Salary(2000)), e0)
  }
  
  @Test
  def testCoproductBasics {
    val a: Fruit = Apple()
    val p: Fruit = Pear()
    val b: Fruit = Banana()
    val o: Fruit = Orange()
    
    val iso = Iso[Fruit, APBO]
    
    val a0 = iso.to(a)
    typed[APBO](a0)
    
    val p0 = iso.to(p)
    typed[APBO](p0)
    
    val b0 = iso.to(b)
    typed[APBO](b0)
    
    val o0 = iso.to(o)
    typed[APBO](o0)
    
    val a1 = iso.from(a0)
    typed[Fruit](a1)
    
    val p1 = iso.from(p0)
    typed[Fruit](p1)
    
    val b1 = iso.from(b0)
    typed[Fruit](b1)
    
    val o1 = iso.from(o0)
    typed[Fruit](o1)
  }
  
  @Test
  def testCoproductMapBasics {
    val a: Fruit = Apple()
    val p: Fruit = Pear()
    val b: Fruit = Banana()
    val o: Fruit = Orange()
    
    val iso = Iso[Fruit, APBO]
    
    val a0 = iso.to(a)
    typed[APBO](a0)
    val a1 = a0.map(showFruit).unify
    assertEquals("Pomme", a1)
    
    val p0 = iso.to(p)
    typed[APBO](p0)
    val p1 = p0.map(showFruit).unify
    assertEquals("Poire", p1)
    
    val b0 = iso.to(b)
    typed[APBO](b0)
    val b1 = b0.map(showFruit).unify
    assertEquals("Banane", b1)
    
    val o0 = iso.to(o)
    typed[APBO](o0)
    val o1 = o0.map(showFruit).unify
    assertEquals("Orange", o1)
  }
  
  @Test
  def testSingletonCoproducts {
    val iso = Iso[AbstractSingle, Single]
    
    val s: AbstractSingle = Single()
    
    val s0 = iso.to(s)
    typed[Single](s0)
    
    val s1 = iso.from(s0)
    typed[AbstractSingle](s1)
  }
  
  @Test
  def testCaseObjects {
    val a: Enum = A
    val b: Enum = B
    val c: Enum = C
    
    val iso = Iso[Enum, ABC]
    
    val a0 = iso.to(a)
    typed[ABC](a0)
    
    val b0 = iso.to(b)
    typed[ABC](b0)
    
    val c0 = iso.to(c)
    typed[ABC](c0)
    
    val a1 = iso.from(a0)
    typed[Enum](a1)
    
    val b1 = iso.from(b0)
    typed[Enum](b1)
    
    val c1 = iso.from(c0)
    typed[Enum](c1)
  }
  
  @Test
  def testCaseObjectMap {
    val a: Enum = A
    val b: Enum = B
    val c: Enum = C
    
    val iso = Iso[Enum, ABC]
    
    val a0 = iso.to(a)
    typed[ABC](a0)
    val a1 = a0.map(pickFruit)
    typed[ABP](a1)
    typed[Fruit](a1.unify)
    assertEquals(Apple(), a1.unify)
    
    val b0 = iso.to(b)
    typed[ABC](b0)
    val b1 = b0.map(pickFruit)
    typed[ABP](b1)
    typed[Fruit](b1.unify)
    assertEquals(Banana(), b1.unify)
    
    val c0 = iso.to(c)
    typed[ABC](c0)
    val c1 = c0.map(pickFruit)
    typed[ABP](c1)
    typed[Fruit](c1.unify)
    assertEquals(Pear(), c1.unify)
  }
  
  @Test
  def testParametrized {
    val t: Tree[Int] = Node(Node(Leaf(23), Leaf(13)), Leaf(11))
    type NI = Node[Int] :+: Leaf[Int]
    
    val iso = Iso[Tree[Int], NI]
    
    val t0 = iso.to(t)
    typed[NI](t0)
    
    val t1 = iso.from(t0)
    typed[Tree[Int]](t1)
  }
  
  @Test
  def testParametrizedWithVarianceOption {
    val o: Option[Int] = Option(23)
    type SN = None.type :+: Some[Int] 
    
    val iso = Iso[Option[Int], SN]
    
    val o0 = iso.to(o)
    typed[SN](o0)
    
    val o1 = iso.from(o0)
    typed[Option[Int]](o1)
  }
  
//  @Test
//  def testMapOption {
//    val o: Option[Int] = Option(23)
//    type SN = None.type :+: Some[Int] 
//    
//    val o0 = inc(o)
//    typed[Option[Int]](o0)
//    assertEquals(Some(24), o0)
//
//    val oo: Option[Option[Int]] = Option(Option(23))
//    val oo0 = inc(oo)
//    typed[Option[Option[Int]]](oo0)
//    assertEquals(Some(Some(24)), oo0)
//  }
  
  @Test
  def testParametrizedWithVarianceList {
    import scala.collection.immutable.{ :: => Cons }
    
    val l: List[Int] = List(1, 2, 3)
    type CN = Cons[Int] :+: Nil.type 
    
    val iso = Iso[List[Int], CN]
    
    val l0 = iso.to(l)
    typed[CN](l0)
    
    val l1 = iso.from(l0)
    typed[List[Int]](l1)
  }
  
  @Test
  def testMapList {
    val l: List[Int] = List(1, 2, 3)

    type CN[T] = Cons[T] :+: Nil.type 

    implicit val nilIso: Iso[Nil.type, HNil] = new Iso[Nil.type, HNil] {
      def to(t: Nil.type) = HNil
      def from(u: HNil) = Nil
    }

    implicit val consIso: Iso[Cons[Int], Int :: List[Int] :: HNil] = new Iso[Cons[Int], Int :: List[Int] :: HNil] {
      def to(t: Cons[Int]) = t.head :: t.tail :: HNil
      def from(u: Int :: List[Int] :: HNil) = Cons(u.head, u.tail.head)
    }
    
    val l0 = inc(l)
    typed[List[Int]](l0)
    println("l0: "+l0)
//    assertEquals(List(2, 3, 4), l0)
  }
}
