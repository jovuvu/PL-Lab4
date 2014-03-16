object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  
  def compressRec[A](l: List[A]): List[A] = l match {
    // matches singleton
    case Nil | _ :: Nil => l

    //matches all lists with multiple items, h1 = first element, h2 = 2nd element, t1 = rest of list INCLUDING 2nd element
    //if (h1==h2), we have consecutive duplicate => call compress rec without first element
    //if (h1!=h2), we do not have duplication => return compressRec(t1) appended to first element
    case h1 :: (t1 @ (h2 :: _)) =>  if (h1==h2) compressRec(t1) else h1 :: compressRec(t1)

  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => {
      acc match {
        case h1 :: _ => if (h==h1) acc else h :: acc
        case Nil => h :: acc
      }
    }
  }
  
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case Some(x) => x :: t
      case None => h :: mapFirst(f)(t)
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 
    
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        case Empty => acc
        case Node(l, d, r) => 
        	(l, d, r) match {
        	  case (Empty, d, r) => loop(f(acc, d), r)
        	  case (l, d, Empty) => f(acc, d)
        	  case (l, d, r) => loop(f(loop(z, l),d), r)
        	}
      }
      loop(z, this)
    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = t.foldLeft((true, None: Option[Int])){
      (acc:(Boolean,Option[Int]),v:Int) => acc match {
        case (b,None) => (b, Some(v))
        case (b,Some(nv)) => (b && v > nv, Some(v))
      } 
    }
    b
  }
  

  /* Type Inference */
  
  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeInfer(env: Map[String,Typ], e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)
    //println("typeInfer with e: " + e + " || env: " + env)
    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => typeInfer(env + (x -> typ(e1)), e2)
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) =>
        val inferredTyp = typ(e1)
        if (inferredTyp == TBool) TBool else err(inferredTyp, e1)
        
      case Binary(Plus, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (te1, te2) => err(te1, e1)
      }
        
      case Binary(Minus|Times|Div, e1, e2) => (typ(e1),typ(e2)) match {
        case (TNumber, TNumber) => TNumber
        case (te1, te2) => if (te1!=TNumber) err(te1, e1) else err(te2, e2)
      }
        
      case Binary(Eq|Ne, e1, e2) => (typ(e1)) match {
        case te1 if (!hasFunctionTyp(te1)) => typ(e2) match {
          case te2 if (!hasFunctionTyp(te2)) => if (te2==te1) TBool else err(te2, e2)
          case tgot => err (tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
        
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (te1, te2) => err(te1, e1)
      }
      
      case Binary(And|Or, e1, e2) => (typ(e1), typ(e2)) match {
        case (TBool, TBool) => TBool
        case (te1, te2) => err(te1, e1)
      }
        
      case Binary(Seq, e1, e2) => (typ(e1), typ(e2)) match {
        case (te1, te2) => te2
      }
      
      case If(e1, e2, e3) => typ(e1) match {
        case TBool => (typ(e2),typ(e3)) match {
          case (te2,te3) if (te2 == te3) => te2
          case (_,te3) => err(te3,e3)
        }
        case tgot => err(tgot,e1)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            env + (f -> tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1: Map[String, Typ])((env1, h) => env1 + h)
        tann match {
          case None => TFunction(params, typeInfer(env2, e1))
          case Some(tret) => 
            val e1Typ = typeInfer(env2, e1)
            if (e1Typ == tret) TFunction(params, tret) else err(e1Typ, e1)
        }
      }
      
      
      case Call(e1, args) => typ(e1) match {
        case TFunction(params, tret) if (params.length == args.length) => {
          (params, args).zipped.foreach {
            case ((key, value), args) => 
              val argTyp = typ(args)
              if (value == argTyp) value else err(argTyp, args)
          };
          tret
        }
        case tgot => err(tgot, e1)
      }
      case Obj(fields) =>TObj(fields.mapValues(e => typ(e)))
      case GetField(e1, f) => typ(e1) match {
        case TObj(fields) => fields(f)
        case tgot => err(tgot, e1)
      }
    }
  }
  
  
  /* Small-Step Interpreter */
  /* Helpers */
    
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) if (n compare 0.0) == 0 || (n compare -0.0) == 0 || n.isNaN => false
      case N(_) => true
      case B(b) => b
      case Undefined => false
      case S("") => false
      case S(_) => true
      case Function(_,_,_,_) => true
    }
  }
  
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    //println("Substituting with: -> e: " + e + " || v: " + v + " || x: " + x)
    def subst(e: Expr): Expr = substitute(e, v, x)
    
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) v else e
      case ConstDecl(y, e1, e2) => ConstDecl(y, subst(e1), if (x == y) e2 else subst(e2))
      case Function(Some(p),params, tann, e1) => 
        val blah = params.foldLeft(true){
          (acc, h) => if (x != h._1 && x != p) acc && true else acc && false
        }
        if (blah == true) Function(Some(p), params, tann, subst(e1)) else e
      case Function(None,params, tann, e1) => 
        val blah = params.foldLeft(true){
          (acc, h) => if (x != h._1) acc && true else acc && false
        }
        if (blah == true) Function(None, params, tann, subst(e1)) else e
      case Call(e1, args) =>
        Call(subst(e1), args.foldRight(Nil: List[Expr]){(h, acc) => subst(h) :: acc})
      case Obj(fields) =>
        val subbedFields = fields.foldLeft(Map.empty: Map[String, Expr]){(acc, h) => h match {case (key, ei) => acc + (key -> subst(ei))}}
        Obj(subbedFields)
      case GetField(e1, f) => GetField(subst(e1), f)
    }
  }
  
  def step(e: Expr): Expr = {
    //println("Stepping with e: " + e)
    require(!isValue(e))
    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))
    
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, N(n1)) => N(- n1)
      case Unary(Not, B(b1)) => B(! b1)
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      case Binary(And, B(b1), e2) => if (b1) e2 else B(false)
      case Binary(Or, B(b1), e2) => if (b1) B(true) else e2
      case If(e1,e2,e3) if (isValue(e1)) => if (toBoolean(e1)) e2 else e3
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)
      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, tann, e1) => {
            //println("Stepping function call.")
            p match {
              //substitute arguments into our function body
              case None => (params, args).zipped.foldRight(e1){(h,acc) => substitute(acc, h._2,h._1._1)}
              case Some(x1) => (params, args).zipped.foldRight(substitute(e1, v1, x1)){(h,acc) => substitute(acc, h._2,h._1._1)}
            }
          }
          case _ => throw new StuckError(e)
        }
        
      /*** Fill-in more cases here. ***/
      
      /* Inductive Cases: Search Rules */
      case Call(v1, args) => if(!isValue(v1)) Call(step(v1), args) else Call(v1, args.foldRight(Nil: List[Expr]){(h,acc) => if(!isValue(h)) step(h) :: acc else h :: acc})
      case Print(e1) => Print(step(e1))
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      case Obj(fields) => 
        //println("Stepping fields")
        val steppedFields = fields.foldLeft(Map.empty: Map[String, Expr]) {(acc,h) => h match { case (key, ei) => if (!isValue(ei)) acc + (key -> step(ei)) else acc + (key -> ei) }}
        Obj(steppedFields)
        
      //search and do rule for GetField
      case GetField(egf, f) =>
        egf match {
          case Obj(fields) => 
            val ef = fields(f)
            if (!isValue(ef)) step(ef) else ef
          case _ => throw StuckError(egf)
        }
      /*** Fill-in more cases here. ***/
      
      /* Everything else is a stuck error. Should not happen if e is well-typed. */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  this.debug = true // comment this out or set to false if you don't want print debugging information
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val t = inferType(expr)
    }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }

}