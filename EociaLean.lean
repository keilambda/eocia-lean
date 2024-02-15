import EociaLean.Basic
import EociaLean.IR.LInt
import EociaLean.IR.LVar
import EociaLean.IR.LVarMon
import EociaLean.IR.CVar
import EociaLean.IR.x86
import EociaLean.IR.x86Int
import EociaLean.IR.x86Var

namespace Pass
open x86.Instr x86.Reg

abbrev LVarMonState : Type := LVarMon.Env × Nat

open LVarMon.Exp LVarMon.Op LVarMon.Atom in
def removeComplexOperands : LVar.Exp → StateM LVarMonState LVarMon.Exp
| LVar.Exp.int i => pure $ atm (int i)
| LVar.Exp.var v => pure $ atm (var v)
| LVar.Exp.let_ name val body => let_ name <$> removeComplexOperands val <*> removeComplexOperands body
| LVar.Exp.op o => match o with
  | LVar.Op.read => pure $ op read
  | LVar.Op.add lhs rhs => do
    let lname ← gensym
    let rname ← gensym
    let lval ← removeComplexOperands lhs
    let rval ← removeComplexOperands rhs
    addvar lname lval
    addvar rname rval
    pure ∘ let_ lname lval ∘ let_ rname rval ∘ op $ add (var lname) (var rname)
  | LVar.Op.sub lhs rhs => do
    let lname ← gensym
    let rname ← gensym
    let lval ← removeComplexOperands lhs
    let rval ← removeComplexOperands rhs
    addvar lname lval
    addvar rname rval
    pure ∘ let_ lname lval ∘ let_ rname rval ∘ op $ sub (var lname) (var rname)
  | LVar.Op.neg e => do
    let name ← gensym
    let val ← removeComplexOperands e
    addvar name val
    pure ∘ let_ name val ∘ op ∘ neg ∘ var $ name
where
@[inline] gensym : StateM LVarMonState Var := getModify (·.map id Nat.succ) <&> (s!"%{·.2}")
@[inline] addvar k v : StateM LVarMonState Unit := modify (·.map (·.insert k v) id)

open CVar.Atom in
@[inline] def fromLVarMonAtom : LVarMon.Atom → CVar.Atom
| LVarMon.Atom.int i => int i
| LVarMon.Atom.var v => var v

open CVar.Op in
def fromLVarMonOp : LVarMon.Op → CVar.Op
| LVarMon.Op.read => read
| LVarMon.Op.add lhs rhs => add (fromLVarMonAtom lhs) (fromLVarMonAtom rhs)
| LVarMon.Op.sub lhs rhs => sub (fromLVarMonAtom lhs) (fromLVarMonAtom rhs)
| LVarMon.Op.neg e => neg (fromLVarMonAtom e)

open CVar.Tail CVar.Stmt CVar.Exp in
def explicateAssign (name : Var) (exp : LVarMon.Exp) (acc : CVar.Tail) : CVar.Tail := match exp with
| LVarMon.Exp.let_ name' val body => explicateAssign name' val (explicateAssign name body acc)
| LVarMon.Exp.atm a => seq (assign name (atm ∘ fromLVarMonAtom $ a)) acc
| LVarMon.Exp.op o => seq (assign name (op ∘ fromLVarMonOp $ o)) acc

open CVar.Tail CVar.Exp in
def explicateControl : LVarMon.Exp → CVar.Tail
| LVarMon.Exp.let_ name val body => explicateAssign name val (explicateControl body)
| LVarMon.Exp.atm a => ret ∘ atm ∘ fromLVarMonAtom $ a
| LVarMon.Exp.op o => ret ∘ op ∘ fromLVarMonOp $ o

open x86Var.Arg in
@[inline] def fromCVarAtom : CVar.Atom → x86Var.Arg
| CVar.Atom.int i => imm i
| CVar.Atom.var v => var v

open CVar.Op x86Var.Arg in
def fromCVarOp (dest : x86Var.Arg) : CVar.Op → List x86Var.Instr
| CVar.Op.read =>
  [ callq "read_int" 0
  , movq (reg rax) dest
  ]
| add lhs rhs =>
  [ movq (fromCVarAtom lhs) (reg rax)
  , addq (fromCVarAtom rhs) (reg rax)
  , movq (reg rax) dest
  ]
| sub lhs rhs =>
  [ movq (fromCVarAtom lhs) (reg rax)
  , subq (fromCVarAtom rhs) (reg rax)
  , movq (reg rax) dest
  ]
| neg a =>
  [ movq (fromCVarAtom a) (reg rax)
  , negq (reg rax)
  , movq (reg rax) dest
  ]

open CVar.Stmt CVar.Exp x86Var.Arg in
@[inline] def fromCVarStmt : CVar.Stmt → List x86Var.Instr
| assign name exp => match exp with
  | atm a => [movq (fromCVarAtom a) (var name)]
  | op o => fromCVarOp (var name) o

open CVar.Tail CVar.Exp x86Var.Arg in
def selectInstructions : CVar.Tail → List x86Var.Instr
| ret e => match e with
  | atm a => [movq (fromCVarAtom a) (reg rax)]
  | op o => fromCVarOp (reg rax) o
| seq s t => fromCVarStmt s ++ selectInstructions t

open x86Int.Arg in
def fromx86Arg : x86Var.Arg → StateM x86Int.Frame x86Int.Arg
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

def assignHomes (xs : List x86Var.Instr) : StateM x86Int.Frame (List x86Int.Instr) := xs.traverse λ
| addq s d => addq <$> fromx86Arg s <*> fromx86Arg d
| subq s d => subq <$> fromx86Arg s <*> fromx86Arg d
| negq d => negq <$> fromx86Arg d
| movq s d => movq <$> fromx86Arg s <*> fromx86Arg d
| pushq d => pushq <$> fromx86Arg d
| popq d => popq <$> fromx86Arg d
| callq lbl d => pure $ callq lbl d
| retq => pure retq
| jmp lbl => pure $ jmp lbl
| syscall => pure syscall

open x86Int.Arg in
def patchInstructions (xs : List x86Int.Instr) : List x86Int.Instr := concatMap xs λ
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

open x86Int.Arg in
@[inline] def allocate (size : Int) : List x86Int.Instr :=
  [ pushq (reg rbp)
  , movq (reg rsp) (reg rbp)
  , subq (imm size) (reg rsp)
  ]

open x86Int.Arg in
@[inline] def deallocate (size : Int) : List x86Int.Instr :=
  [ addq (imm size) (reg rsp)
  , popq (reg rbp)
  ]

open x86Int.Arg in
@[inline] def exit : List x86Int.Instr :=
  [ movq (imm x86.SysV.sys_exit) (reg rax)
  , movq (imm 0) (reg rdi)
  , syscall
  ]

namespace Labels

def main : Label := "main"
def prelude : Label := "_start"
def conclusion : Label := "conclusion"

end Labels

@[inline] def preludeAndConclusion (frameSize : Int) (xs : List x86Int.Instr) : x86Int.Program :=
  ⟨ Labels.prelude
  , Std.RBMap.ofList
    [ (Labels.prelude, ⟨allocate frameSize |>.concat (jmp Labels.main)⟩)
    , (Labels.main, ⟨xs.concat (jmp Labels.conclusion)⟩)
    , (Labels.conclusion, ⟨deallocate frameSize ++ exit ++ [retq]⟩)
    ]
    compare
  ⟩

def compile (p : LVar.Program) : x86Int.Program :=
  p.exp
  |>.uniquify |>.run' (∅, 0) |>.run
  |> removeComplexOperands |>.run' (∅, 0) |>.run
  |> explicateControl
  |> selectInstructions
  |> assignHomes |>.run ⟨∅, 0⟩ |>.run
  |> λ (xs, f) => patchInstructions xs
  |> preludeAndConclusion f.frameSize

end Pass
