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
@[inline]
instance : Into LVarMon.Atom CVar.Atom where
  into
  | LVarMon.Atom.int i => int i
  | LVarMon.Atom.var v => var v

open CVar.Op in
@[inline]
instance : Into LVarMon.Op CVar.Op where
  into
  | LVarMon.Op.read => read
  | LVarMon.Op.add lhs rhs => add (into lhs) (into rhs)
  | LVarMon.Op.sub lhs rhs => sub (into lhs) (into rhs)
  | LVarMon.Op.neg e => neg (into e)

open CVar.Tail CVar.Stmt CVar.Exp in
def explicateAssign (name : Var) (exp : LVarMon.Exp) (acc : CVar.Tail) : CVar.Tail := match exp with
| LVarMon.Exp.let_ name' val body => explicateAssign name' val (explicateAssign name body acc)
| LVarMon.Exp.atm a => seq (assign name (atm ∘ into $ a)) acc
| LVarMon.Exp.op o => seq (assign name (op ∘ into $ o)) acc

open CVar.Tail CVar.Exp in
def explicateControl : LVarMon.Exp → CVar.Tail
| LVarMon.Exp.let_ name val body => explicateAssign name val (explicateControl body)
| LVarMon.Exp.atm a => ret ∘ atm ∘ into $ a
| LVarMon.Exp.op o => ret ∘ op ∘ into $ o

open x86Var.Arg in
@[inline]
instance : Into CVar.Atom x86Var.Arg where
  into
  | CVar.Atom.int i => imm i
  | CVar.Atom.var v => var v

open CVar.Op x86Var.Arg in
def x86VarFromCVarOp (dest : x86Var.Arg) : CVar.Op → List x86Var.Instr
| CVar.Op.read =>
  [ callq "read_int" 0
  , movq (reg rax) dest
  ]
| add lhs rhs =>
  [ movq (into lhs) (reg rax)
  , addq (into rhs) (reg rax)
  , movq (reg rax) dest
  ]
| sub lhs rhs =>
  [ movq (into lhs) (reg rax)
  , subq (into rhs) (reg rax)
  , movq (reg rax) dest
  ]
| neg a =>
  [ movq (into a) (reg rax)
  , negq (reg rax)
  , movq (reg rax) dest
  ]

open CVar.Stmt CVar.Exp x86Var.Arg in
@[inline]
instance : Into CVar.Stmt (List x86Var.Instr) where
  into
  | assign name exp => match exp with
    | atm a => [movq (into a) (var name)]
    | op o => x86VarFromCVarOp (var name) o

open CVar.Tail CVar.Exp x86Var.Arg in
def selectInstructions : CVar.Tail → List x86Var.Instr
| ret e => match e with
  | atm a => [movq (into a) (reg rax)]
  | op o => x86VarFromCVarOp (reg rax) o
| seq s t => into s ++ selectInstructions t

open x86Int.Arg in
def x86VarEliminateVar : x86Var.Arg → StateM x86Int.Frame x86Int.Arg
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
| x86Var.Arg.deref a b => (deref · b) <$> x86VarEliminateVar a

def assignHomes (xs : List x86Var.Instr) : StateM x86Int.Frame (List x86Int.Instr) := xs.traverse λ
| addq s d => addq <$> x86VarEliminateVar s <*> x86VarEliminateVar d
| subq s d => subq <$> x86VarEliminateVar s <*> x86VarEliminateVar d
| negq d => negq <$> x86VarEliminateVar d
| movq s d => movq <$> x86VarEliminateVar s <*> x86VarEliminateVar d
| pushq d => pushq <$> x86VarEliminateVar d
| popq d => popq <$> x86VarEliminateVar d
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
  let prelude := if frameSize = 0 then ∅ else allocate frameSize
  let conclusion := if frameSize = 0 then ∅ else deallocate frameSize
  ⟨ Labels.prelude
  , Std.RBMap.ofList
    [ (Labels.prelude, ⟨prelude.concat (jmp Labels.main)⟩)
    , (Labels.main, ⟨xs.concat (jmp Labels.conclusion)⟩)
    , (Labels.conclusion, ⟨conclusion ++ exit ++ [retq]⟩)
    ]
    compare
  ⟩

def compile (p : LVar.Program) : x86Int.Program :=
  p.exp
  |>.uniquify |>.run (∅, 0) |>.run
  |> λ (exp, (_, n)) => removeComplexOperands exp |>.run' (∅, n) |>.run
  |> explicateControl
  |> selectInstructions
  |> assignHomes |>.run ⟨∅, 0⟩ |>.run
  |> λ (xs, f) => patchInstructions xs
  |> preludeAndConclusion f.frameSize

end Pass
