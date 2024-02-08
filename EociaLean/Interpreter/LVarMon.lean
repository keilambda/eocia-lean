import Std.Data.RBMap
import EociaLean.Basic
import EociaLean.Interpreter.LVar

namespace LVarMon

inductive Atom : Type
| int : Int → Atom
| var : Var → Atom
deriving Repr

namespace Atom

instance : ToString Atom where
  toString
  | int i => toString i
  | var name => name

end Atom

inductive Op : Type
| read : Op
| add : Atom → Atom → Op
| sub : Atom → Atom → Op
| neg : Atom → Op
deriving Repr

namespace Op

instance : ToString Op where
  toString
  | read => "(read)"
  | add a b => s!"(+ {a} {b})"
  | sub a b => s!"(- {a} {b})"
  | neg a => s!"(- {a})"

end Op

inductive Exp : Type
| atm : Atom → Exp
| let_ : Var → Exp → Exp → Exp
| op : Op → Exp
deriving Repr

abbrev Env : Type := Std.RBMap Var Exp compare

namespace Exp
open Atom Op

protected def toString' : Exp → String
| atm a => toString a
| let_ name val body => s!"(let ([{name} {val.toString'}]) {body.toString'})"
| op o => toString o

instance : ToString Exp where
  toString := Exp.toString'

def gensym : StateM (Env × Nat) String := getModify (·.map id Nat.succ) <&> (s!"%{·.2}")
def addvar (k : Var) (v : Exp) : StateM (Env × Nat) PUnit := modify (·.map (·.insert k v) id)

def removeComplexOperands : LVar.Exp → StateM (Env × Nat) Exp
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

partial def interpret (exp : Exp) : StateT Env IO Int := match exp with
| atm a => match a with
  | int i => pure i
  | var v => do
    match (← get).find? v with
    | some e => e.interpret
    | none => throw $ IO.userError s!"unbound variable: '{v}'"
| let_ name val body => do
  modify (·.insert name val)
  body.interpret
| op o => match o with
  | Op.read => String.toInt! <$> (IO.getStdin >>= (·.getLine))
  | add lhs rhs => Int.add <$> (atm lhs).interpret <*> (atm rhs).interpret
  | sub lhs rhs => Int.sub <$> (atm lhs).interpret <*> (atm rhs).interpret
  | neg e => Int.neg <$> (atm e).interpret

end Exp

structure Program where
  mk :: (env : Env) (exp : Exp)

end LVarMon
