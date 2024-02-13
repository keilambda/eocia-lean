abbrev Var : Type := String
abbrev Label : Type := String

def gensym : StateM Nat Var := getModify Nat.succ <&> (s!"%{·}")

def concatMap {α : Type u} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (λ x acc => f x ++ acc) []

inductive Reg : Type
| rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
deriving Repr

namespace Reg

instance : ToString Reg where
  toString
  | rsp => "rsp"
  | rbp => "rbp"
  | rax => "rax"
  | rbx => "rbx"
  | rcx => "rcx"
  | rdx => "rdx"
  | rsi => "rsi"
  | rdi => "rdi"
  | r8 => "r8"
  | r9 => "r9"
  | r10 => "r10"
  | r11 => "r11"
  | r12 => "r12"
  | r13 => "r13"
  | r14 => "r14"
  | r15 => "r15"

end Reg

namespace Labels

def main : String := "main"
def prelude : String := "_start"
def conclusion : String := "conclusion"

end Labels
