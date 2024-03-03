
section Member

inductive Member : α -> List α -> Type
  | head {a as}   : Member a (a::as)
  | tail {a b bs} : Member a bs -> Member a (b::bs)
deriving DecidableEq, BEq, Ord, Repr open Member

@[simp]
theorem list_app_nil (l: List α): l ++ [] = l := by simp

end Member
