// A Small Compiler for the WHILE Language
//
// the abstract syntax trees
abstract class Stmt
abstract class AExp
abstract class BExp
type Block = List[Stmt]
// statements
case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class Read(s: String) extends Stmt
// arithmetic expressions
case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp
// boolean expressions
case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
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
  case Bop("<", a1, a2) =>
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
  case Write(x) =>
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


// Fibonacci numbers as a test-case
val fib_test =
  List(Read("n"),                       //  read n;
    Assign("minus1",Num(0)),         //  minus1 := 0;
    Assign("minus2",Num(1)),         //  minus2 := 1;
    Assign("temp",Num(0)),           //  temp := 0;
    While(Bop("<",Num(0),Var("n")),  //  while n > 0 do  {
      List(Assign("temp",Var("minus2")),    //  temp := minus2;
        Assign("minus2",Aop("+",Var("minus1"),Var("minus2"))),
        //  minus2 := minus1 + minus2;
        Assign("minus1",Var("temp")), //  minus1 := temp;
        Assign("n",Aop("-",Var("n"),Num(1))))), //  n := n - 1 };
    Write("minus1"))                 //  write minus1



// prints out the JVM-assembly program

println(compile(fib_test, "fib"))

// can be assembled with
//
//    java -jar jvm/jasmin-2.4/jasmin.jar fib.j
//
// and started with
//
//    java fib/fib


