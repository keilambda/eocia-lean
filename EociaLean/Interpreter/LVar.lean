import Std.Data.RBMap
import EociaLean.Basic

namespace LVar

abbrev Env := Std.RBMap Var Int compare

-- AST
mutual
inductive Exp : Type
| int : Int → Exp
| var : Var → Exp
| let_ : Var → Exp → Exp → Exp
| op : Op → Exp
deriving Repr

inductive Op : Type
| read : Op
| add : Exp → Exp → Op
| sub : Exp → Exp → Op
| neg : Exp → Op
deriving Repr
end

structure Program where
  mk :: (info : α) (exp : Exp)

open Exp Op

def leaf? : Exp → Prop
| int _ => True
| var _ => True
| let_ _ _ _ => False
| op Op.read => True
| op (add _ _) => False
| op (sub _ _) => False
| op (neg _) => False

def exp? : Exp → Prop
| int _ => True
| var _ => True
| let_ _ a b => leaf? a ∧ exp? b
| op Op.read => True
| op (add a b) => exp? a ∧ exp? b
| op (sub a b) => exp? a ∧ exp? b
| op (neg a) => exp? a

def Lint? : Program → Prop
| ⟨_, exp⟩ => exp? exp

def interpExp (env : Env) : Exp → IO Int
| int i => pure i
| var name => match env.find? name with
  | some i => pure i
  | none => throw ∘ IO.userError $ "unbound variable: " ++ name
| let_ name lhs body => (interpExp env lhs) >>= λ val => interpExp (env.insert name val) body
| op Op.read => String.toInt! <$> (IO.getStdin >>= IO.FS.Stream.getLine)
| op (add a b) => Int.add <$> (interpExp env a) <*> (interpExp env b)
| op (sub a b) => Int.sub <$> (interpExp env a) <*> (interpExp env b)
| op (neg i) => Int.neg <$> interpExp env i

def interpLint : Program → IO Int
| ⟨env, exp⟩ => interpExp env exp

def peAdd : Exp → Exp → Exp
| int a, int b => int (a + b)
| a, b => op $ add a b

def peSub : Exp → Exp → Exp
| int a, int b => int (a - b)
| a, b => op $ sub a b

def peNeg : Exp → Exp
| int i => int (Int.neg i)
| other => op $ neg other

def peExp (env : Env) : Exp → Exp
| exp@(int _) => exp
| var name => match env.find? name with
  | some i => int i
  | none => var name
| exp@(let_ _ _ _) => exp
| exp@(op Op.read) => exp
| op (add a b) => peAdd a b
| op (sub a b) => peSub a b
| op (neg a) => peNeg a

def peLint : Program → Program
| ⟨env, exp⟩ => ⟨env, peExp env exp⟩

end LVar
