import scala.language.implicitConversions
import scala.language.reflectiveCalls

abstract class Rexp
case object NULL extends Rexp
case object EMPTY extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp
case class RANGE(s: List[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPT(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
abstract class Val
case object EmptyVal extends Val
case class ChrVal(c: Char) extends Val
case class SeqVal(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class RecVal(x: String, v: Val) extends Val
case class RangeVal(vs: List[Char]) extends Val
case class PlusVal(vs: List[Val]) extends Val
case class OptVal(v: Val) extends Val
case class NtimesVal(vs: List[Val]) extends Val

// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => EMPTY
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = charlist2rexp(s.toList)
implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}
implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable (r: Rexp) : Boolean = r match {
  case NULL => false
  case EMPTY => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)

  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPT(_) => true
  case NTIMES(r, n) => if(n==0) true else nullable(r)
}

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
  case NULL => NULL
  case EMPTY => NULL
  case CHAR(d) => if (c == d) EMPTY else NULL
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)

  case RANGE(s) => if(s.contains(c)) EMPTY else NULL
  case PLUS(r) => SEQ(der(c,r), STAR(r))
  case OPT(r) => der(c,r)
  case NTIMES(r, n) => if(n==0) NULL else der(c, SEQ(r, NTIMES(r, n-1)));
}

// derivative w.r.t. a string (iterates der)
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// extracts a string from value
def flatten(v: Val) : String = v match {
  case EmptyVal => ""
  case ChrVal(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case SeqVal(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case RecVal(_, v) => flatten(v)

  case RangeVal(vs) => vs.mkString
  case PlusVal(vs) => vs.map(flatten).mkString
  case OptVal(v) => flatten(v)
  case NtimesVal(vs) => vs.map(flatten).mkString
}

// extracts an environment from a value
def env(v: Val) : List[(String, String)] = v match {
  case EmptyVal => Nil
  case ChrVal(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case SeqVal(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case RecVal(x, v) => (x, flatten(v))::env(v)

  case RangeVal(_) => Nil
  case PlusVal(vs) => vs.flatMap(env)
  case OptVal(v) => env(v)
  case NtimesVal(vs) => vs.flatMap((env))
}

// injection part
def mkeps(r: Rexp) : Val = r match {
  case EMPTY => EmptyVal
  case ALT(r1, r2) =>
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => SeqVal(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => RecVal(x, mkeps(r))

  case PLUS(r) => PlusVal(Nil)
  case OPT(_) => Left(EmptyVal)
  case NTIMES(r, n) => if (n==0) Stars(Nil) else Stars(Nil.padTo(n, mkeps(r)))
}
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), SeqVal(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), SeqVal(v1, v2)) => SeqVal(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(SeqVal(v1, v2))) => SeqVal(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => SeqVal(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), EmptyVal) => ChrVal(c)
  case (RECD(x, r1), _) => RecVal(x, inj(r1, c, v))

  case (PLUS(r), SeqVal(v1, Stars(vs))) => PlusVal(inj(r, c, v1) :: vs)
  case (OPT(r), v) => OptVal(inj(r,c, v))
  case (NTIMES(r, n), SeqVal(v1, Stars(vs))) => NtimesVal(inj(r, c, v1) :: vs)
  case (NTIMES(r, n), Left(SeqVal(v1, Stars(vs)))) => NtimesVal(inj(r, c, v1) :: vs)
  case (NTIMES(r, n), Right(Stars(v::vs))) => Stars(mkeps(r)::inj(r, c, v)::vs)
}

// main lexing function (produces a value)
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}
def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case SeqVal(v1, v2) => SeqVal(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) =
  (v:Val) => SeqVal(f1(EmptyVal), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) =
  (v:Val) => SeqVal(f1(v), f2(EmptyVal))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case RecVal(x, v) => RecVal(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification of regular expressions returning also an
// rectification function; no simplification under STAR
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (NULL, _) => (r2s, F_RIGHT(f2s))
      case (_, NULL) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
      else (ALT (r1s, r2s), F_ALT(f1s, f2s))
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (NULL, _) => (NULL, F_ERROR)
      case (_, NULL) => (NULL, F_ERROR)
      case (EMPTY, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, EMPTY) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}
def lexing_simp(r: Rexp, s: String) : Val = lex_simp(r, s.toList)

// Lexing Rules for a Small While Language
def PLUSS(r: Rexp) = r ~ r.%
val SYM = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" | "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT | "_" ).%
val NUM = PLUSS(DIGIT)
val KEYWORD : Rexp = "while" | "if" | "then" | "else" |"do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" | "upto"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/" | "&&" | "||" | ":=" | "="
val WHITESPACE = PLUSS(" " | "\n" | "\t")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"
val STRING: Rexp = "\"" ~ SYM.% ~ "\""
val WHILE_REGS = (("k" $ KEYWORD) |
  ("i" $ ID) |
  ("o" $ OP) |
  ("n" $ NUM) |
  ("s" $ SEMI) |
  ("str" $ STRING) |
  ("p" $ (LPAREN | RPAREN)) |
  ("b" $ (BEGIN | END)) |
  ("w" $ WHITESPACE)).%

abstract class Parser[I <% Seq[_], T] {
  def parse(ts: I): Set[(T, I)]
  def parse_all(ts: I) : Set[T] =
    for ((head, tail) <- parse(ts); if (tail.isEmpty)) yield head
}

class SeqParser[I <% Seq[_], T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, (T, S)] {
  def parse(sb: I) =
    for ((head1, tail1) <- p.parse(sb);
         (head2, tail2) <- q.parse(tail1)) yield ((head1, head2), tail2)
}

class AltParser[I <% Seq[_], T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)
}

class FunParser[I <% Seq[_], T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
  def parse(sb: I) =
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

case class StringParser(s: String) extends Parser[String, String] {
  def parse(sb: String) = {
    val (prefix, suffix) = sb.splitAt(s.length)
    if (prefix == s) Set((prefix, suffix)) else Set()
  }
}

case class TokenParser(s: (String,String)) extends Parser[List[(String, String)], List[(String, String)]] {
  def parse(sb: List[(String, String)]) = {
    if(sb.length > 0 && s._1 == sb.head._1 && s._2 == sb.head._2) Set((List[(String, String)](s), sb.drop(1))) else Set()
  }
}

case object NumParser extends Parser[List[(String, String)], Int] {
  def parse(sb: List[(String, String)]) = sb.head match {
    case ("n", _) => Set((sb.head._2.toInt, sb.drop(1)))
    case _ => Set()
  }
}

implicit def string2parser(s : String) = StringParser(s)

implicit def token2parser(s : (String, String)) = TokenParser(s)

implicit def ParserOps[I<% Seq[_], T](p: Parser[I, T]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

implicit def StringOps(s: String) = new {
  def || (q : => Parser[String, String]) = new AltParser[String, String](s, q)
  def || (r: String) = new AltParser[String, String](s, r)
  def ==>[S] (f: => String => S) = new FunParser[String, String, S](s, f)
  def ~[S](q : => Parser[String, S]) =
    new SeqParser[String, String, S](s, q)
  def ~ (r: String) =
    new SeqParser[String, String, String](s, r)
}

implicit def TokenOps(s: (String, String)) = new {
  def ==>[S] (f: => List[(String, String)] => S) = new FunParser[List[(String, String)], List[(String, String)], S](s, f)
  def ~ (r: (String, String)) = new SeqParser[List[(String, String)], List[(String, String)], List[(String, String)]](s, r)
}

// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp
type Block = List[Stmt]
case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(o: String) extends Stmt
case class WriteVar(o: String) extends Stmt
case class Read(o: String) extends Stmt
case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp
case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case object IdParser extends Parser[List[(String, String)], List[(String, String)]] {
  def parse(sb: List[(String, String)]) = sb.head match {
    case ("i", _) => Set((List[(String, String)](sb.head), sb.drop(1)))
    case _ => Set()
  }
}
case object StrTokenParser extends Parser[List[(String, String)], List[(String, String)]] {
  def parse(sb: List[(String, String)]) = sb.head match {
    case("str", _) => Set((List[(String, String)](sb.head), sb.drop(1)))
    case _ => Set()
  }
}

lazy val AExp: Parser[List[(String, String)], AExp] =
  ((Te ~ ("o", "+") ~ AExp) ==> { case ((x, y), z) => Aop("+", x, z):AExp } ||
    (Te ~ ("o", "-") ~ AExp) ==> { case ((x, y), z) => Aop("-", x, z):AExp } || Te)
lazy val Te: Parser[List[(String, String)], AExp] =
  (Fa ~ ("o", "*") ~ Te) ==> { case ((x, y), z) => Aop("*", x, z):AExp } || Fa
lazy val Fa: Parser[List[(String, String)], AExp] =
  (((token2parser(("p", "(")) ~ AExp ~ token2parser(("p", ")"))) ==> { case ((x, y), z) => y }) ||
    (IdParser ==> {case(x) => Var(x.head._2)}) ||
    (StrTokenParser ==> {case(x) => Var(x.head._2)}) ||
    NumParser ==> Num)

// boolean expressions
lazy val BExp: Parser[List[(String, String)], BExp] =
  ((AExp ~ ("o", "=") ~ AExp) ==> { case ((x, y), z) => Bop("=", x, z): BExp } ||
    (AExp ~ ("o", "!=") ~ AExp) ==> { case ((x, y), z) => Bop("!=", x, z): BExp } ||
    (AExp ~ ("o", "<") ~ AExp) ==> { case ((x, y), z) => Bop("<", x, z): BExp } ||
    (AExp ~ ("o", ">") ~ AExp) ==> { case ((x, y), z) => Bop(">", x, z): BExp } ||
    (("k", "true") ==> ((_) => True: BExp)) ||
    (("k", "false") ==> ((_) => False: BExp)) ||
    (token2parser("p", "(") ~ BExp ~ token2parser("p", ")")) ==> { case ((x, y), z) => y})

lazy val Stmt: Parser[List[(String, String)], Stmt] =
  (("k", "skip") ==> ((_) => Skip: Stmt)) ||
    (IdParser ~("o", ":=") ~ AExp) ==> { case ((x, y), z) => Assign(x.head._2, z): Stmt } ||
    (token2parser(("k", "if")) ~ BExp ~("k", "then") ~ Block ~("k", "else") ~ Block) ==> { case (((((x, y), z), u), v), w) => If(y, u, w): Stmt } ||
    (token2parser(("k", "while")) ~ BExp ~("k", "do") ~ Block) ==> { case (((x, y), z), w) => While(y, w) } ||
    (token2parser("k", "write") ~ StrTokenParser ==> { case (x, y) => Write(y.head._2): Stmt }) ||
    (token2parser("k", "write") ~ IdParser ==> { case (x, y) => WriteVar(y.head._2): Stmt }) ||
    (token2parser("k", "read") ~ IdParser ==> { case (x, y) => Read(y.head._2): Stmt })

lazy val Stmts: Parser[List[(String, String)], Block] =
  (Stmt ~ ("s", ";") ~ Stmts) ==> { case ((x, y), z) => x :: z : Block } ||
    (Stmt ==> ((s) => List(s): Block))
lazy val Block: Parser[List[(String, String)], Block] =
  (token2parser(("b", "{")) ~ Stmts ~ ("b", "}")) ==> { case ((x, y), z) => y} ||
    (token2parser("k", "for") ~ IdParser ~("o", ":=") ~ AExp ~("k", "upto") ~ AExp ~("k", "do") ~ Block) ==> { case (((((((_, x), _), y), _), z), _), w) =>
      List(Assign(x.head._2, y), While(Bop("<", Var(x.head._2), z), w :+ Assign(x.head._2, Aop("+", Var(x.head._2), Num(1)))))
    } ||
    (Stmt ==> ((s) => List(s)) || Stmts ==> {case(x) => x})
val figure2 = """read n;
                minus1 := 0;
                minus2 := 1;
                while n > 0 do {
                temp := minus2;
                minus2 := minus1 + minus2;
                minus1 := temp;
                n := n - 1
                };
                write minus2"""
val figure3 = """read n;
                fact := 1;
                while n > 0 do {
                fact := fact * n;
                n := n - 1
                };
                write fact"""
// compiler headers needed for the JVM
// (contains an init method, as well as methods for read and write)
val beginning = """
.class public XXX.XXX
.super java/lang/Object
.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method
.method public static write(I)V
    .limit locals 1
    .limit stack 2
    getstatic java/lang/System/out Ljava/io/PrintStream;
    iload 0
    invokevirtual java/io/PrintStream/println(I)V
    return
.end method
.method public static read()I
    .limit locals 10
    .limit stack 10
    ldc 0
    istore 1  ; this will hold our final integer
Label1:
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I
    istore 2
    iload 2
    ldc 10   ; the newline delimiter
    isub
    ifeq Label2
    iload 2
    ldc 32   ; the space delimiter
    isub
    ifeq Label2
    iload 2
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48
    isub
    ldc 10
    iload 1
    imul
    iadd
    istore 1
    goto Label1
Label2:
    ;when we come here we have our integer computed in local variable 1
    iload 1
    ireturn
.end method
.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200
                """
val ending = """
   return
.end method
             """
// for generating new labels
var counter = -1
def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}
// environments and instructions
type Env = Map[String, String]
type Instrs = List[String]
// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : Instrs = a match {
  case Num(i) => List("ldc " + i.toString + "\n")
  case Var(s) => List("iload " + env(s) + "\n")
  case Aop("+", a1, a2) =>
    compile_aexp(a1, env) ++
      compile_aexp(a2, env) ++ List("iadd\n")
  case Aop("-", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ List("isub\n")
  case Aop("*", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ List("imul\n")
}
// boolean expression compilation
def compile_bexp(b: BExp, env : Env, jmp: String) : Instrs = b match {
  case True => Nil
  case False => List("goto " + jmp + "\n")
  case Bop("=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++
      List("if_icmpne " + jmp + "\n")
  case Bop("!=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++
      List("if_icmpeq " + jmp + "\n")
  case Bop(">", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++
      List("if_icmpge " + jmp + "\n")
}
// statement compilation
def compile_stmt(s: Stmt, env: Env) : (Instrs, Env) = s match {
  case Skip => (Nil, env)
  case Assign(x, a) => {
    val index = if (env.isDefinedAt(x)) env(x) else
      env.keys.size.toString
    (compile_aexp(a, env) ++
      List("istore " + index + "\n"), env + (x -> index))
  }
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
      instrs1 ++
      List("goto " + if_end + "\n") ++
      List("\n" + if_else + ":\n\n") ++
      instrs2 ++
      List("\n" + if_end + ":\n\n"), env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (List("\n" + loop_begin + ":\n\n") ++
      compile_bexp(b, env, loop_end) ++
      instrs1 ++
      List("goto " + loop_begin + "\n") ++
      List("\n" + loop_end + ":\n\n"), env1)
  }
  case WriteVar(x) =>
    (List("iload " + env(x) + "\n" +
      "invokestatic XXX/XXX/write(I)V\n"), env)
  case Read(x) => {
    val index = if (env.isDefinedAt(x)) env(x) else
      env.keys.size.toString
    (List("invokestatic XXX/XXX/read()I\n" +
      "istore " + index + "\n"), env + (x -> index))
  }
}
// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (Instrs, Env) = bl match {
  case Nil => (Nil, env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}
// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions.mkString ++ ending).replaceAllLiterally("XXX", class_name)
}
println(compile(Block.parse_all(env(lexing_simp(WHILE_REGS, figure2)).filter(f => f._1 != "w")).head, "fib"))


val f2 = """for i := 2 upto 10 do {
                write i
                }"""
//println(compile(Block.parse_all(env(lexing_simp(WHILE_REGS, f2)).filter(f => f._1 != "w")).head, "fib"))
