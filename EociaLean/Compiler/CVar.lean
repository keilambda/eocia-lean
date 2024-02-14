import Std.Data.RBMap
import EociaLean.Basic
import EociaLean.Interpreter.LVarMon

namespace CVar

inductive Atom : Type
| int : Int → Atom
| var : Var → Atom
deriving Repr

namespace Atom

instance : ToString Atom where
  toString
  | int i => toString i
  | var v => v

@[inline] def fromLVarMonAtom : LVarMon.Atom → Atom
| LVarMon.Atom.int i => int i
| LVarMon.Atom.var v => var v

end Atom

inductive Op : Type
| read : Op
| add : Atom → Atom → Op
| sub : Atom → Atom → Op
| neg : Atom → Op
deriving Repr

namespace Op
open Atom

instance : ToString Op where
  toString
  | read => "(read)"
  | add lhs rhs => s!"(+ {lhs} {rhs})"
  | sub lhs rhs => s!"(- {lhs} {rhs})"
  | neg e => s!"(- {e})"

def fromLVarMonOp : LVarMon.Op → Op
| LVarMon.Op.read => read
| LVarMon.Op.add lhs rhs => add (fromLVarMonAtom lhs) (fromLVarMonAtom rhs)
| LVarMon.Op.sub lhs rhs => sub (fromLVarMonAtom lhs) (fromLVarMonAtom rhs)
| LVarMon.Op.neg e => neg (fromLVarMonAtom e)

end Op

inductive Exp : Type
| atm : Atom → Exp
| op : Op → Exp
deriving Repr

namespace Exp

instance : ToString Exp where
  toString
  | atm a => toString a
  | op o => toString o

end Exp

inductive Stmt : Type
| assign : Var → Exp → Stmt
deriving Repr

namespace Stmt

instance : ToString Stmt where
  toString
  | assign name exp => s!"{name} = {exp};"

end Stmt

inductive Tail : Type
| ret : Exp → Tail
| seq : Stmt → Tail → Tail
deriving Repr

abbrev Env : Type := Std.RBMap Var Exp compare

namespace Tail
open Stmt Exp Op Atom

protected def toString' : Tail → String
| ret e => s!"return {e};"
| seq s t => s!"{s}\n{t.toString'}"

instance : ToString Tail where
  toString := Tail.toString'

mutual
def explicateTail : LVarMon.Exp → Tail
| LVarMon.Exp.let_ name val body => explicateAssign name val (explicateTail body)
| LVarMon.Exp.atm a => ret ∘ atm ∘ fromLVarMonAtom $ a
| LVarMon.Exp.op o => ret ∘ op ∘ fromLVarMonOp $ o

def explicateAssign (name : Var) (exp : LVarMon.Exp) (acc : Tail) : Tail := match exp with
| LVarMon.Exp.let_ name' val body => explicateAssign name' val (explicateAssign name body acc)
| LVarMon.Exp.atm a => seq (assign name (atm ∘ fromLVarMonAtom $ a)) acc
| LVarMon.Exp.op o => seq (assign name (op ∘ fromLVarMonOp $ o)) acc
end

end Tail

structure CVar : Type where
  mk :: (env : Env) (blocks : Std.RBMap Label Tail compare)

end CVar
