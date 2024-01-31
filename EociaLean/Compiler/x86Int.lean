import Lean.Data.HashMap

inductive Reg : Type
| rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
deriving Repr

inductive Arg : Type
| imm : Int → Arg
| reg : Reg → Arg
| deref : Reg → Int → Arg
deriving Repr

inductive Instr : Type
| addq : Arg → Arg → Instr
| subq : Arg → Arg → Instr
| negq : Arg → Instr
| movq : Arg → Arg → Instr
| pushq : Arg → Instr
| popq : Arg → Instr
| callq : String → Int → Instr
| retq : Instr
| jmp : String → Instr
deriving Repr

abbrev Env : Type := Lean.HashMap String Int

structure Block : Type where
  mk :: (env : Env) (instructions : List Instr)

structure x86Int : Type where
  mk :: (env : Env) (globl : String) (blocks : Lean.HashMap String Block)
