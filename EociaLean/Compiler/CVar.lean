import Lean.Data.HashMap

namespace CVar

inductive Atom : Type
| int : Int → Atom
| var : String → Atom
deriving Repr

inductive Op : Type
| read : Op
| add : Atom → Atom → Op
| sub : Atom → Atom → Op
| neg : Atom → Op
deriving Repr

inductive Exp : Type
| atm : Atom → Exp
| op : Op → Exp
deriving Repr

inductive Stmt : Type
| assign : String → Exp → Stmt
deriving Repr

inductive Tail : Type
| ret : Exp → Tail
| seq : Stmt → Tail → Tail
deriving Repr

abbrev Env : Type := Lean.HashMap String Int

structure CVar : Type where
  mk :: (env : Env) (blocks : Lean.HashMap String Tail)

end CVar
