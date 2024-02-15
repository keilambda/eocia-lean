import Std.Data.RBMap
import EociaLean.Basic
import EociaLean.IR.x86
import EociaLean.IR.x86Var

namespace x86Int
open x86.Reg

inductive Arg : Type
| imm : Int → Arg
| reg : x86.Reg → Arg
| deref : Arg → x86.Reg → Arg
deriving Repr

namespace Arg

protected def toString' : Arg → String
| imm i => s!"${toString i}"
| reg r => s!"%{toString r}"
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
| syscall : Instr
deriving Repr

structure Frame : Type where
  mk :: (env : Std.RBMap Var Arg compare) (offset : Int)
deriving Repr, Inhabited

@[inline] def Frame.frameSize (h : Frame) : Int :=
  let n := h.offset.neg
  (n % 16) + n -- align to be a multiple of 16

namespace Instr
open Arg

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
  | syscall => "syscall"

end Instr

structure Block : Type where
  mk :: (instructions : List Instr)

instance : ToString Block where
  toString b := b.instructions.foldl (λ acc i => s!"{acc}\t{i}\n") default

structure Program : Type where
  mk :: (globl : Label) (blocks : Std.RBMap Label Block compare)

instance : ToString Program where
  toString p := s!".globl {p.globl}\n{p.blocks.foldl build default}"
  where
  build acc lbl block := s!"{acc}{lbl}:\n{block}"

end x86Int
