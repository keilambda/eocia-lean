import Std.Data.RBMap
import EociaLean.Basic

namespace x86Int

inductive Reg : Type
| rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
deriving Repr

namespace Reg

instance : ToString Reg where
  toString
  | rsp => "%rsp"
  | rbp => "%rbp"
  | rax => "%rax"
  | rbx => "%rbx"
  | rcx => "%rcx"
  | rdx => "%rdx"
  | rsi => "%rsi"
  | rdi => "%rdi"
  | r8 => "%r8"
  | r9 => "%r9"
  | r10 => "%r10"
  | r11 => "%r11"
  | r12 => "%r12"
  | r13 => "%r13"
  | r14 => "%r14"
  | r15 => "%r15"

end Reg

inductive Arg : Type
| imm : Int → Arg
| reg : Reg → Arg
| deref : Arg → Reg → Arg
deriving Repr

namespace Arg

protected def toString' : Arg → String
| imm i => toString i
| reg r => toString r
| deref a b => s!"{a.toString'}({b})"

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

end Instr

abbrev Env : Type := Std.RBMap Var Int compare

structure Block : Type where
  mk :: (env : Env) (instructions : List Instr)

instance : ToString Block where
  toString b := b.instructions.foldl (λ acc i => s!"{acc}\t{i}\n") default

structure x86Int : Type where
  mk :: (env : Env) (globl : Label) (blocks : Std.RBMap Label Block compare)

instance : ToString x86Int where
  toString p := s!".globl {p.globl}\n{p.blocks.foldl labelWithBlock default}"
  where
  labelWithBlock (acc : String) (lbl : Label) (block : Block) : String :=
    s!"{acc}{lbl}:\n{block}"

end x86Int
