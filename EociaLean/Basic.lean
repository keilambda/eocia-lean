abbrev Var : Type := String
abbrev Label : Type := String

def gensym : StateM Nat Var := getModify Nat.succ <&> (s!"%{·}")
