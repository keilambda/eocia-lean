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

end Pass
