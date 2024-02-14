abbrev Var : Type := String
abbrev Label : Type := String

def gensym : StateM Nat Var := getModify Nat.succ <&> (s!"%{·}")

def concatMap {α : Type u} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (λ x acc => f x ++ acc) []
namespace Labels

def main : String := "main"
def prelude : String := "_start"
def conclusion : String := "conclusion"

end Labels
