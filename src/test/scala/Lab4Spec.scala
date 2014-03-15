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
    assert(typeInfer(Map.empty, a) == TFunction(List(), TNumber))
    val b = ConstDecl("X", N(3), Function(None, List.empty, Some(TNumber), Binary(Plus, Var("X"),N(3))))
    assert(typeInfer(Map.empty, b) == TFunction(List(), TNumber))
    val c = Function(None, List.empty, Some(TString), Binary(Plus, S("Doo"),S("Poo")))
    assert(typeInfer(Map.empty, c) == TFunction(List(), TString))
  }
  // Probably want to write some tests for typeInfer, substitute, and step.
  
  "typeInfer Object" should "check return type of Object" in {
    val a = Map(("poo" -> N(3)), ("pee" -> Binary(Plus, S("Doo"),S("Poo"))), ("doo" -> B(true)))
    val b = Obj(a)
    typeInfer(Map.empty, b)
  }
  
  "typeInfer Binary Eq" should "check return type of Binary Eq with var" in {
    val a = ConstDecl("n", N(0.0), Binary(Eq, Var("n"), N(0.0)))
    assert(typeInfer(Map.empty, a) == TNumber)
  }
  val w = "w"
  val y = "y"
  val x = Function(Some(w),List((y,TNumber)),Some(TNumber),If(Binary(Eq,Var(y),N(0.0)),N(0.1),Binary(Plus,Var(y),Call(Var(w),List(Binary(Minus,Var(y),N(1.0)))))))
  val a = If(Binary(Eq,N(0.0),N(0.0)),N(0.1),Binary(Plus,N(0.0),Call(N(0.0),List(Binary(Minus,N(0.0),N(1.0))))))
  val b = Binary(Plus,N(0.0),Call(N(0.0),List(Binary(Minus,N(0.0),N(1.0)))))
  val c = Call(N(0.0),List(Binary(Minus,N(0.0),N(1.0))))
  val d = List(Binary(Minus,N(0.0),N(1.0)))
  val e = Function(Some("myF"), List(("poo", TNumber), ("doo", TNumber)), None, Binary(Plus, Var("poo"), Var("doo")))
  val f = Call(e, List(N(1),N(2)))
  val g = iterateStep(f)
  println("Output: " + f)
  assert(iterateStep(f)==N(3))
  //val z = ConstDecl(w,Function(Some(w),List((y,TNumber)),Some(TNumber),If(Binary(Eq,Var(y),N(0.0)),N(0.1),Binary(Plus,Var(y),Call(Var(w),List(Binary(Minus,Var(y),N(1.0))))))),Call(Var(w),List(N(3.0))))
  //println(typeInfer(Map.empty, x))
}
