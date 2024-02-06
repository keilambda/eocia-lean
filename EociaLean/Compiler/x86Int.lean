import Std.Data.RBMap
import EociaLean.Basic
import EociaLean.Interpreter.LVar

namespace x86Int

inductive Reg : Type
| rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
deriving Repr

open Reg

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

inductive Arg : Type
| imm : Int → Arg
| reg : Reg → Arg
| deref : Arg → Arg → Arg
deriving Repr

open Arg

def Arg.toString' : Arg → String
| imm i => toString i
| reg r => toString r
| deref a b => s!"{toString' a}({toString' b})"

instance : ToString Arg where
  toString := Arg.toString'

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

open Instr

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

inductive Error : Type
| unboundVar : Var → Error
deriving Repr

instance : ToString Error where
  toString
  | (Error.unboundVar v) => s!"Unbound variable: '{v}'"

section

open LVar Exp Op

abbrev ExpEnv : Type := Std.RBMap Var Exp compare

def rebind (old new : Var) : Exp → Exp
| v@(var name) => if name == old then var new else v
| let_ name val body => let_ (if name == old then new else name) (rebind old new val) (rebind old new body)
| i@(int _) => i
| o@(op Op.read) => o
| op (add a b) => op (add (rebind old new a) (rebind old new b))
| op (sub a b) => op (sub (rebind old new a) (rebind old new b))
| op (neg a) => op (neg (rebind old new a))

partial def uniquifyExp : Exp → StateM (ExpEnv × Nat) Exp
| e@(int _) => pure e
| v@(var _) => pure v
| let_ name val body => do
  let name' ← (λ (_, n) => s!"{name}.{n}") <$> getModify (·.map id Nat.succ) -- poor man's `gensym`
  let val' ← uniquifyExp ∘ rebind name name' $ val
  let body' ← uniquifyExp ∘ rebind name name' $ body
  modify (·.map (λ env => env.insert name' val' |>.erase name) id)
  pure (let_ name' val' body')
| e@(op Op.read) => pure e
| op (add a b) => op <$> (add <$> uniquifyExp a <*> uniquifyExp b)
| op (sub a b) => op <$> (sub <$> uniquifyExp a <*> uniquifyExp b)
| op (neg a) => op <$> (neg <$> uniquifyExp a)

#eval uniquifyExp (let_ "x" (int 1) (let_ "y" (int 2) (op (add (var "x") (var "y"))))) |>.run default

def uniquify : Program → Program
| ⟨env, exp⟩ => let (exp', env', _) := uniquifyExp exp |>.run (env, 0) |>.run; ⟨env', exp'⟩

end
