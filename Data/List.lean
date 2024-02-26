
section Member

inductive Member : List α -> α -> Type
  | head : Member (a::as) a
  | tail : Member bs a -> Member (b::bs) a
deriving DecidableEq, BEq, Ord, Repr open Member

@[simp]
theorem app_nil (l: List α): l ++ [] = l := by simp

end Member
