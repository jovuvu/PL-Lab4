import org.scalatest._
import jsy.lab4.ast._
import Lab4._

class Lab4Spec extends FlatSpec {
  
  "compressRec/compressFold" should "compress List(1, 2, 2, 3, 3, 3)" in {
    val l1 = List(1, 2, 2, 3, 3, 3)
    val gold1 = List(1, 2, 3)
    assertResult(gold1) { compressRec(l1) }
    assertResult(gold1) { compressFold(l1) }
  } 
  
  "mapFirst" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     assertResult(gold1) {
       mapFirst { (i: Int) => if (i < 0) Some(-i) else None } (l1)
     }
  }
  
  "foldLeft" should "enable implementing treeFromList and sum" in {
    assertResult(6){
      sum(treeFromList(List(1, 2, 3)))
    }
  }
  
  "foldLeft (unordered input)" should "enable implementing treeFromList and sum" in {
    assertResult(15){
      sum(treeFromList(List(4,5,1, 2, 3)))
    }
  }
  
  "strictlyOrdered" should "check strict ordering of a binary search tree" in {
    assert(!strictlyOrdered(treeFromList(List(1,1,2))))
    assert(strictlyOrdered(treeFromList(List(1,2))))
  } 
  "strictlyOrdered (unordered input)" should "check strict ordering of a binary search tree" in {
    assert(!strictlyOrdered(treeFromList(List(3, 4,1,1,2))))
    assert(strictlyOrdered(treeFromList(List(3, 4, 1,2))))
  } 
  
  "typeInfer Function" should "check return type of function" in {
    val a = Function(None, List.empty, Some(TNumber), Binary(Plus, N(3),N(3)))
    assert(typeInfer(Map.empty, a) == TNumber)
    val b = ConstDecl("X", N(3), Function(None, List.empty, Some(TNumber), Binary(Plus, Var("X"),N(3))))
    assert(typeInfer(Map.empty, b) == TNumber)
    val c = Function(None, List.empty, Some(TString), Binary(Plus, S("Doo"),S("Poo")))
    assert(typeInfer(Map.empty, c) == TString)
  }
  // Probably want to write some tests for typeInfer, substitute, and step.
  
  "typeInfer Object" should "check return type of Object" in {
    val a = Map(("poo" -> N(3)), ("pee" -> Binary(Plus, S("Doo"),S("Poo"))), ("doo" -> B(true)))
    val b = Obj(a)
    typeInfer(Map.empty, b)
  }
}
