namespace LInt

-- AST
mutual
inductive Exp : Type
| int : Int → Exp
| op : Op → Exp
deriving Repr

inductive Op : Type
| read : Op
| add : Exp → Exp → Op
| sub : Exp → Exp → Op
| neg : Exp → Op
deriving Repr
end

namespace Exp
open Op

def leaf? : Exp → Prop
| int _ => True
| op Op.read => True
| op (add _ _) => False
| op (sub _ _) => False
| op (neg _) => False

def exp? : Exp → Prop
| int _ => True
| op Op.read => True
| op (add lhs rhs) => lhs.exp? ∧ rhs.exp?
| op (sub lhs rhs) => lhs.exp? ∧ rhs.exp?
| op (neg e) => e.exp?

def interpret : Exp → IO Int
| int i => pure i
| op Op.read => String.toInt! <$> (IO.getStdin >>= (·.getLine))
| op (add lhs rhs) => Int.add <$> lhs.interpret <*> rhs.interpret
| op (sub lhs rhs) => Int.sub <$> lhs.interpret <*> rhs.interpret
| op (neg e) => Int.neg <$> e.interpret

@[inline] private def peAdd : Exp → Exp → Exp
| int a, int b => int (a + b)
| a, b => op $ add a b

@[inline] private def peSub : Exp → Exp → Exp
| int a, int b => int (a - b)
| a, b => op $ sub a b

@[inline] private def peNeg : Exp → Exp
| int i => int (Int.neg i)
| other => op $ neg other

def evaluate : Exp → Exp
| i@(int _) | i@(op Op.read) => i
| op (add a b) => peAdd a b
| op (sub a b) => peSub a b
| op (neg a) => peNeg a

end Exp

structure Program where
  mk :: (exp : Exp)

namespace Program

def LInt? : Program → Prop
| ⟨exp⟩ => exp.exp?

def interpret : Program → IO Int
| ⟨exp⟩ => exp.interpret

def evaluate : Program → Program
| ⟨exp⟩ => ⟨exp.evaluate⟩

end Program
end LInt
