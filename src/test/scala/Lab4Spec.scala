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

//  "typeInfer" should "check for static type errors" in {
//    val x = true
//    val e1 = Unary(Not, B(x))
//    assert(step(e1) === B(false))
//    val y = 10
//    val e2 = Unary(Not, N(y))
//    assert(step(e2) === B(false))
//  }
  // Probably want to write some tests for typeInfer, substitute, and step.
}
