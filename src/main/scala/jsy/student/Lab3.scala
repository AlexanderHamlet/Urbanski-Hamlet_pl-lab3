package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Alexander Hamlet
   * 
   * Partner: Alex Urbanski
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def isFunction(e: Expr): Boolean = e match {
    case Function(_, _, _) => true
    case _ => false
  }

  def isArith(b: Bop): Boolean = b match {
    case Plus | Minus | Times | Div | Lt | Le | Gt | Ge => true
    case _ => false
  }
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => if(s=="") 0 else try{
          s.toDouble
        } catch {
          case e: NumberFormatException =>
            Double.NaN
        }
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case N(n) => if(n == Double.NaN) false else n != 0
      case S(s) => s.length > 0
      case Undefined => false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
      case N(n) => n.toString
      case B(b) => b.toString
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case _ => ??? // delete this line when done
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env, x)
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

        // ****** Your cases here
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eval(env, e1)), e2)

      case Call(e1, e2) => eval(env, e1) match {
        case Function(None, param, ebody) => eval(extend(env, param, eval(env, e2)), ebody)
        case v1 @ Function(Some(name), param, ebody) => {
          val env2 = extend(env, name, eval(env, v1))
          eval(extend(env2, param, eval(env2, e2)), ebody)
        }
        case _ => throw DynamicTypeError(e)
      }

      case If(e1, e2,e3) => if(toBoolean(eval(env, e1))) eval(env,e2) else eval(env, e3)

      case Unary(uop, e1) => uop match {
        case Neg => N(-toNumber(eval(env, e1)))
        case Not => B(!toBoolean(eval(env, e1)))
      }

      case Binary(bop, e1, e2) => bop match {
        case Plus => {
          val v1 = eval(env, e1)
          val v2 = eval(env, e2)
          v1 match {
            case S(_) => S(toStr((v1)) + toStr(v2))
            case _ => v2 match {
              case S(_) => S(toStr(v1) + toStr(v2))
              case _ => N(toNumber(v1) + toNumber(v2))
            }
          }
        }
        case Minus => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
        case Times => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
        case Div => {
          val v1 = toNumber(eval(env, e1))
          val v2 = toNumber(eval(env, e2))
          if(v2==0 && v1>0) N(Double.PositiveInfinity)
          else if(v2==0 && v1<0) N(Double.NegativeInfinity)
          else N(v1/v2)
        }

        case Eq => if(toStr(eval(env, e1)) == toStr(eval(env, e2))) B(true) else B(false)
        case Ne => if(toStr(eval(env, e1)) != toStr(eval(env, e2))) B(true) else B(false)
        case Lt => if(toNumber(eval(env, e1)) < toNumber(eval(env, e2))) B(true) else B(false)
        case Le => if(toNumber(eval(env, e1)) <= toNumber(eval(env, e2))) B(true) else B(false)
        case Gt => if(toNumber(eval(env, e1)) > toNumber(eval(env, e2))) B(true) else B(false)
        case Ge => if(toNumber(eval(env, e1)) >= toNumber(eval(env, e2))) B(true) else B(false)

        case And => {
          if(!toBoolean(eval(env, e1))) eval(env, e1)
          else eval(env, e2)
        }
        case Or => {
          if(toBoolean(eval(env, e1))) eval(env, e1)
          else eval(env, e2)
        }

        case Seq => eval(env, e1); eval(env, e2)
      }
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(expr) => loop(expr, n+1)
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, v, x), substitute(e2, v, x))
      case If(e1, e2, e3) => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case Call(e1, e2) => ???
      case Var(y) => if(x == y) { v } else { e }
      case Function(None, y, e1) => ???
      case Function(Some(y1), y2, e1) => ???
      case ConstDecl(y, e1, e2) => ???
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, v) if(isValue(v)) => {
        N(-toNumber(v))
      }
      case Unary(Not, v) if(isValue(v)) => {
        B(!toBoolean(v))
      }
      case Binary(Seq, e1, e2) if(isValue(e1)) => {
        e2
      }
      case Binary(Plus, v1, v2) if(isValue(v1) && isValue(v2)) => {
        (v1, v2) match {
          case (N(n1), N(n2)) => N(n1 + n2)
          case (S(s1), S(s2)) => S(s1 + s2)
          case (S(s), v) => S(s + toStr(v))
          case (v, S(s)) => S(toStr(v) + s)
        }
      }
      case Binary(Minus, v1, v2) if(isValue(v1) && isValue(v2)) => {
        N(toNumber(v1) - toNumber(v2))
      }
      case Binary(Times, v1, v2) if(isValue(v1) && isValue(v2)) => {
        N(toNumber(v1) * toNumber(v2))
      }
      case Binary(Div, v1, v2) if(isValue(v1) && isValue(v2)) => {
        N(toNumber(v1) / toNumber(v2))
      }
      case Binary(Eq, v1, v2) if(isValue(v1) && isValue(v2)) => {
        if(!isFunction(v1)){
          if(toStr(v1) == toStr(v2)) B(true) else B(false)
        } else {
          throw DynamicTypeError(e)
        }
      }
      case Binary(Ne, v1, v2) if(isValue(v1) && isValue(v2)) => {
        if(!isFunction(v1)){
          if(toStr(v1) != toStr(v2)) B(true) else B(false)
        } else {
          throw DynamicTypeError(e)
        }

      }
      case Binary(Lt, v1, v2) if(isValue(v1) && isValue(v2)) => {
        if(toStr(v1) < toStr(v2)) B(true) else B(false)
      }
      case Binary(Le, v1, v2) if(isValue(v1) && isValue(v2)) => {
        if(toStr(v1) <= toStr(v2)) B(true) else B(false)
      }
      case Binary(Gt, v1, v2) if(isValue(v1) && isValue(v2)) => {
        if(toStr(v1) > toStr(v2)) B(true) else B(false)
      }
      case Binary(Ge, v1, v2) if(isValue(v1) && isValue(v2)) => {
        if(toStr(v1) >= toStr(v2)) B(true) else B(false)
      }
      case Binary(And, B(true), e) => {
        e
      }
      case Binary(And, B(false), e) => {
        B(false)
      }
      case Binary(And, B(true), e) => {
        B(true)
      }
      case Binary(And, B(false), e) => {
        e
      }
      case If(B(true), e1, e2) => {
        e1
      }
      case If(B(false), e1, e2) =>{
        e2
      }
      case Call(v1, v2) if (isFunction(v1) && isValue(v2)) => {
        v1 match {
          case Function(None, param, ebody) => {
            substitute(ebody, v2, param)
          }
          case Function(Some(name), param, ebody) => {
            substitute(ebody, v2, param)
          }
        }
      }
        // ****** Your cases here
      
      /* Inductive Cases: Search Rules */
        // You generate e1 prime and then just pass that in to step again
      case Print(e1) => Print(step(e1))
      
        // ****** Your cases here
      case Unary(uop, e) => {
        Unary(uop, step(e))
      }
      case Binary(bop, e1, e2) => {
        Binary(bop, step(e1), e2)
      }
      case Binary(bop, v, e) if(isArith(bop)) => {
        Binary(bop, v, step(e))
      }
      case Binary(bop, v, e) if(!isArith(bop)) => {
        if(!isFunction(e)) {
          Binary(bop, v, step(e))
        } else {
          throw DynamicTypeError(e)
        }
      }
      case If(e1, e2, e3) => {
        If(step(e1), e2, e3)
      }
      case ConstDecl(x, e1, e2) => {
        ConstDecl(x, step(e1), e2)
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
