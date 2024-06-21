inductive Member : α -> List α -> Type
  | head {a as}   : Member a (a::as)
  | tail {a b bs} : Member a bs -> Member a (b::bs)
deriving DecidableEq, BEq, Ord, Repr open Member

infix:68 " ∈ₗ " => Member

namespace Member

def toNat : Member i is → Nat
  | .head => 0
  | .tail h => toNat h + 1

@[simp]
theorem list_app_nil (l: List α) : l ++ [] = l := by simp

@[simp]
theorem no_member_empty (h: a ∈ₗ []) : False := by cases h

end Member
