import Std.Data.RBMap
import EociaLean.Basic
import EociaLean.Compiler.CVar

namespace x86Var

inductive Arg : Type
| imm : Int → Arg
| reg : Reg → Arg
| var : Var → Arg
| deref : Arg → Reg → Arg
deriving Repr

namespace Arg

protected def toString' : Arg → String
| imm i => s!"${toString i}"
| reg r => s!"%{toString r}"
| var v => v
| deref a b => match a with
  | imm i => s!"{i}(%{b})"
  | other => other.toString'

instance : ToString Arg where
  toString := Arg.toString'

end Arg

inductive Instr : Type
| addq : Arg → Arg → Instr
| subq : Arg → Arg → Instr
| negq : Arg → Instr
| movq : Arg → Arg → Instr
| pushq : Arg → Instr
| popq : Arg → Instr
| callq : Label → Int → Instr
| retq : Instr
| jmp : Label → Instr
deriving Repr

namespace Instr
open Reg Arg

instance : ToString Instr where
  toString
  | addq s d => s!"addq {s}, {d}"
  | subq s d => s!"subq {s}, {d}"
  | negq d => s!"negq {d}"
  | movq s d => s!"movq {s}, {d}"
  | pushq d => s!"pushq {d}"
  | popq d => s!"popq {d}"
  | callq lbl d => s!"callq {lbl}, {d}"
  | retq => "retq"
  | jmp lbl => s!"jmp {lbl}"

def fromCVarAtom : CVar.Atom → Arg
| CVar.Atom.int i => imm i
| CVar.Atom.var v => var v

def fromCVarOp (dest : Arg) : CVar.Op → List Instr
| CVar.Op.read =>
  [ callq "read_int" 0
  , movq (reg rax) dest
  ]
| CVar.Op.add lhs rhs =>
  [ movq (fromCVarAtom lhs) (reg rax)
  , addq (fromCVarAtom rhs) (reg rax)
  , movq (reg rax) dest
  ]
| CVar.Op.sub lhs rhs =>
  [ movq (fromCVarAtom lhs) (reg rax)
  , subq (fromCVarAtom rhs) (reg rax)
  , movq (reg rax) dest
  ]
| CVar.Op.neg a =>
  [ movq (fromCVarAtom a) (reg rax)
  , negq (reg rax)
  , movq (reg rax) dest
  ]

def fromCVarStmt : CVar.Stmt → List Instr
| CVar.Stmt.assign name exp => match exp with
  | CVar.Exp.atm a => [movq (fromCVarAtom a) (var name)]
  | CVar.Exp.op o => fromCVarOp (var name) o

def fromCVarTail : CVar.Tail → List Instr
| CVar.Tail.ret e => match e with
  | CVar.Exp.atm a => [movq (fromCVarAtom a) (reg rax)]
  | CVar.Exp.op o => fromCVarOp (reg rax) o
| CVar.Tail.seq s t => fromCVarStmt s ++ fromCVarTail t

abbrev selectInstructions := fromCVarTail

end Instr

abbrev Env : Type := Std.RBMap Var Int compare

structure Block : Type where
  mk :: (env : Env) (instructions : List Instr)

instance : ToString Block where
  toString b := b.instructions.foldl (λ acc i => s!"{acc}\t{i}\n") default

structure x86Var : Type where
  mk :: (env : Env) (globl : Label) (blocks : Std.RBMap Label Block compare)

instance : ToString x86Var where
  toString p := s!".globl {p.globl}\n{p.blocks.foldl build default}"
  where
  build acc lbl block := s!"{acc}{lbl}:\n{block}"

end x86Var
