import Std.Data.RBMap
import EociaLean.Basic
import EociaLean.IR.x86
import EociaLean.IR.x86Var

namespace x86Int

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

namespace Instr
open x86.Reg Arg

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

structure Frame : Type where
  mk :: (env : Std.RBMap Var Arg compare) (offset : Int)
deriving Repr, Inhabited

@[inline] def Frame.frameSize (h : Frame) : Int :=
  let n := h.offset.neg
  (n % 16) + n -- align to be a multiple of 16

def fromx86Arg : x86Var.Arg → StateM Frame Arg
| x86Var.Arg.var name => do
  let ⟨env, offset⟩ ← get
  match env.find? name with
  | some arg => pure arg
  | none => do
    let offset' := offset - 8
    modify λ ⟨env, _⟩ => ⟨env.insert name (deref (imm offset') rbp), offset'⟩
    pure $ deref (imm offset') rbp
| x86Var.Arg.imm i => pure (imm i)
| x86Var.Arg.reg r => pure (reg r)
| x86Var.Arg.deref a b => (deref · b) <$> fromx86Arg a

def assignHomes (xs : List x86Var.Instr) : StateM Frame (List Instr) := xs.traverse λ
| x86Var.Instr.addq s d => addq <$> fromx86Arg s <*> fromx86Arg d
| x86Var.Instr.subq s d => subq <$> fromx86Arg s <*> fromx86Arg d
| x86Var.Instr.negq d => negq <$> fromx86Arg d
| x86Var.Instr.movq s d => movq <$> fromx86Arg s <*> fromx86Arg d
| x86Var.Instr.pushq d => pushq <$> fromx86Arg d
| x86Var.Instr.popq d => popq <$> fromx86Arg d
| x86Var.Instr.callq lbl d => pure $ callq lbl d
| x86Var.Instr.retq => pure retq
| x86Var.Instr.jmp lbl => pure $ jmp lbl
| x86Var.Instr.syscall => pure syscall

def patchInstructions (xs : List Instr) : List Instr := concatMap xs λ
| i@(addq s d) => match (s, d) with
  | (deref la lb, deref ra rb) =>
    [ movq (deref la lb) (reg rax)
    , addq (reg rax) (deref ra rb)
    ]
  | _ => [i]
| i@(subq s d) => match (s, d) with
  | (deref la lb, deref ra rb) =>
    [ movq (deref la lb) (reg rax)
    , subq (reg rax) (deref ra rb)
    ]
  | _ => [i]
| i@(movq s d) => match (s, d) with
  | (deref la lb, deref ra rb) =>
    [ movq (deref la lb) (reg rax)
    , movq (reg rax) (deref ra rb)
    ]
  | _ => [i]
| i@(negq _) | i@(pushq _) | i@(popq _) | i@(callq _ _) | i@(retq) | i@(jmp _) | i@(syscall) => [i]

end Instr

structure Block : Type where
  mk :: (instructions : List Instr)

instance : ToString Block where
  toString b := b.instructions.foldl (λ acc i => s!"{acc}\t{i}\n") default

structure x86Int : Type where
  mk :: (globl : Label) (blocks : Std.RBMap Label Block compare)

instance : ToString x86Int where
  toString p := s!".globl {p.globl}\n{p.blocks.foldl build default}"
  where
  build acc lbl block := s!"{acc}{lbl}:\n{block}"

open Instr Arg x86.Reg in
@[inline] def allocate (size : Int) : List Instr :=
  [ pushq (reg rbp)
  , movq (reg rsp) (reg rbp)
  , subq (imm size) (reg rsp)
  ]

open Instr Arg x86.Reg in
@[inline] def deallocate (size : Int) : List Instr :=
  [ addq (imm size) (reg rsp)
  , popq (reg rbp)
  ]

open Instr Arg x86.Reg in
@[inline] def exit : List Instr :=
  [ movq (imm 60) (reg rax)
  , movq (imm 0) (reg rdi)
  , syscall
  ]

open Instr in
@[inline] def generatePreludeAndConclusion (frameSize : Int) (xs : List Instr) : x86Int :=
  ⟨ Labels.prelude
  , Std.RBMap.ofList
    [ (Labels.prelude, ⟨allocate frameSize |>.concat (jmp Labels.main)⟩)
    , (Labels.main, ⟨xs.concat (jmp Labels.conclusion)⟩)
    , (Labels.conclusion, ⟨deallocate frameSize ++ exit ++ [retq]⟩)
    ]
    compare
  ⟩

end x86Int