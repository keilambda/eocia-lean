import EociaLean.Basic
import EociaLean.IR.LInt
import EociaLean.IR.LVar
import EociaLean.IR.LVarMon
import EociaLean.IR.CVar
import EociaLean.IR.x86
import EociaLean.IR.x86Int
import EociaLean.IR.x86Var

namespace Pass

abbrev LVarMonState : Type := LVarMon.Env × Nat

def removeComplexOperands : LVar.Exp → StateM LVarMonState LVarMon.Exp
| .int i => pure $ .atm (.int i)
| .var v => pure $ .atm (.var v)
| .let_ name val body => .let_ name <$> removeComplexOperands val <*> removeComplexOperands body
| .op o => match o with
  | .read => pure $ .op .read
  | .add lhs rhs => do
    let lname ← gensym
    let rname ← gensym
    let lval ← removeComplexOperands lhs
    let rval ← removeComplexOperands rhs
    addvar lname lval
    addvar rname rval
    pure ∘ .let_ lname lval ∘ .let_ rname rval ∘ .op $ .add (.var lname) (.var rname)
  | .sub lhs rhs => do
    let lname ← gensym
    let rname ← gensym
    let lval ← removeComplexOperands lhs
    let rval ← removeComplexOperands rhs
    addvar lname lval
    addvar rname rval
    pure ∘ .let_ lname lval ∘ .let_ rname rval ∘ .op $ .sub (.var lname) (.var rname)
  | .neg e => do
    let name ← gensym
    let val ← removeComplexOperands e
    addvar name val
    pure ∘ .let_ name val ∘ .op ∘ .neg ∘ .var $ name
where
@[inline] gensym : StateM LVarMonState Var := getModify (·.map id Nat.succ) <&> (s!"%{·.2}")
@[inline] addvar k v : StateM LVarMonState Unit := modify (·.map (·.insert k v) id)

instance : Coe LVarMon.Atom CVar.Atom where
  coe
  | .int i => .int i
  | .var v => .var v

instance : Coe LVarMon.Op CVar.Op where
  coe
  | .read => .read
  | .add lhs rhs => .add lhs rhs
  | .sub lhs rhs => .sub lhs rhs
  | .neg e => .neg e

def explicateAssign (name : Var) (exp : LVarMon.Exp) (acc : CVar.Tail) : CVar.Tail := match exp with
| .let_ name' val body => explicateAssign name' val (explicateAssign name body acc)
| .atm a => .seq (.assign name (.atm a)) acc
| .op o => .seq (.assign name (.op o)) acc

def explicateControl : LVarMon.Exp → CVar.Tail
| .let_ name val body => explicateAssign name val (explicateControl body)
| .atm a => .ret (.atm a)
| .op o => .ret (.op o)

instance : Coe CVar.Atom x86Var.Arg where
  coe
  | .int i => .imm i
  | .var v => .var v

instance : Coe CVar.Op (List x86Var.Instr) where
  coe
  | .read => [.callq "read_int" 0]
  | .add lhs rhs =>
    [ .movq lhs (.reg .rax)
    , .addq rhs (.reg .rax)
    ]
  | .sub lhs rhs =>
    [ .movq lhs (.reg .rax)
    , .subq rhs (.reg .rax)
    ]
  | .neg a =>
    [ .movq a (.reg .rax)
    , .negq (.reg .rax)
    ]

instance : Coe CVar.Stmt (List x86Var.Instr) where
  coe
  | .assign name exp => match exp with
    | .atm a => [.movq a (.var name)]
    | .op o => ↑o ++ [.movq (.reg .rax) (.var name)]

def selectInstructions : CVar.Tail → List x86Var.Instr
| .ret e => match e with
  | .atm a => [.movq a (.reg .rax)]
  | .op o => o
| .seq s t => s ++ selectInstructions t

def x86VarEliminateVar : x86Var.Arg → StateM x86Int.Frame x86Int.Arg
| .var name => do
  let ⟨env, offset⟩ ← get
  match env.find? name with
  | some arg => pure arg
  | none => do
    let offset' := offset - 8
    modify λ ⟨env, _⟩ => ⟨env.insert name (.deref (.imm offset') .rbp), offset'⟩
    pure $ .deref (.imm offset') .rbp
| .imm i => pure (.imm i)
| .reg r => pure (.reg r)
| .deref a b => (.deref · b) <$> x86VarEliminateVar a

def assignHomes (xs : List x86Var.Instr) : StateM x86Int.Frame (List x86Int.Instr) := xs.traverse λ
| .addq s d => .addq <$> x86VarEliminateVar s <*> x86VarEliminateVar d
| .subq s d => .subq <$> x86VarEliminateVar s <*> x86VarEliminateVar d
| .negq d => .negq <$> x86VarEliminateVar d
| .movq s d => .movq <$> x86VarEliminateVar s <*> x86VarEliminateVar d
| .pushq d => .pushq <$> x86VarEliminateVar d
| .popq d => .popq <$> x86VarEliminateVar d
| .callq lbl d => pure $ .callq lbl d
| .retq => pure .retq
| .jmp lbl => pure $ .jmp lbl
| .syscall => pure .syscall

def patchInstructions (xs : List x86Int.Instr) : List x86Int.Instr := concatMap xs λ
| i@(.addq s d) => match (s, d) with
  | (.deref la lb, .deref ra rb) =>
    [ .movq (.deref la lb) (.reg .rax)
    , .addq (.reg .rax) (.deref ra rb)
    ]
  | _ => [i]
| i@(.subq s d) => match (s, d) with
  | (.deref la lb, .deref ra rb) =>
    [ .movq (.deref la lb) (.reg .rax)
    , .subq (.reg .rax) (.deref ra rb)
    ]
  | _ => [i]
| i@(.movq s d) => match (s, d) with
  | (.deref la lb, .deref ra rb) =>
    [ .movq (.deref la lb) (.reg .rax)
    , .movq (.reg .rax) (.deref ra rb)
    ]
  | _ => [i]
| i@(.negq _) | i@(.pushq _) | i@(.popq _) | i@(.callq _ _) | i@(.retq) | i@(.jmp _) | i@(.syscall) => [i]

@[inline] def allocate (size : Int) : List x86Int.Instr :=
  [ .pushq (.reg .rbp)
  , .movq (.reg .rsp) (.reg .rbp)
  , .subq (.imm size) (.reg .rsp)
  ]

@[inline] def deallocate (size : Int) : List x86Int.Instr :=
  [ .addq (.imm size) (.reg .rsp)
  , .popq (.reg .rbp)
  ]

@[inline] def exit : List x86Int.Instr :=
  [ .movq (.imm x86.SysV.sys_exit) (.reg .rax)
  , .movq (.imm 0) (.reg .rdi)
  , .syscall
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
    [ (Labels.prelude, ⟨prelude.concat (.jmp Labels.main)⟩)
    , (Labels.main, ⟨xs.concat (.jmp Labels.conclusion)⟩)
    , (Labels.conclusion, ⟨conclusion ++ exit⟩)
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
