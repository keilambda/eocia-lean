import Batteries.Data.RBMap
import EociaLean.Basic
import EociaLean.IR.x86

namespace x86Var

inductive Arg : Type
| imm : Int → Arg
| reg : x86.Reg → Arg
| var : Var → Arg
| deref : Arg → x86.Reg → Arg
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

abbrev Instr : Type := x86.Instr Arg

abbrev Env : Type := Batteries.RBMap Var Int compare

structure Block : Type where
  mk :: (env : Env) (instructions : List Instr)

instance : ToString Block where
  toString b := b.instructions.foldl (λ acc i => s!"{acc}\t{i}\n") default

structure x86Var : Type where
  mk :: (env : Env) (globl : Label) (blocks : Batteries.RBMap Label Block compare)

instance : ToString x86Var where
  toString p := s!".globl {p.globl}\n{p.blocks.foldl build default}"
  where
  build acc lbl block := s!"{acc}{lbl}:\n{block}"

end x86Var
