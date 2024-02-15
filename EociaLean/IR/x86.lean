import EociaLean.Basic

namespace x86

inductive Reg : Type
| rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
deriving Repr

namespace Reg

instance : ToString Reg where
  toString
  | rsp => "rsp"
  | rbp => "rbp"
  | rax => "rax"
  | rbx => "rbx"
  | rcx => "rcx"
  | rdx => "rdx"
  | rsi => "rsi"
  | rdi => "rdi"
  | r8 => "r8"
  | r9 => "r9"
  | r10 => "r10"
  | r11 => "r11"
  | r12 => "r12"
  | r13 => "r13"
  | r14 => "r14"
  | r15 => "r15"

end Reg

inductive Instr arg
| addq (src : arg) (dst : arg)
| subq (src : arg) (dst : arg)
| negq (dst : arg)
| movq (src : arg)  (dst : arg)
| pushq (dst : arg)
| popq (dst : arg)
| callq (lbl : Label) (n : Int)
| jmp (lbl : Label)
| syscall
| retq

namespace Instr

instance [ToString arg] : ToString (Instr arg) where
  toString
  | addq src dst => s!"addq {src}, {dst}"
  | subq src dst => s!"subq {src}, {dst}"
  | negq dst => s!"negq {dst}"
  | movq src dst => s!"movq {src}, {dst}"
  | pushq dst => s!"pushq {dst}"
  | popq dst => s!"popq {dst}"
  | callq lbl n => s!"callq {lbl}, {n}"
  | jmp lbl => s!"jmp {lbl}"
  | syscall => "syscall"
  | retq => "retq"

end Instr

namespace SysV

def sys_exit := 60

end SysV
end x86
