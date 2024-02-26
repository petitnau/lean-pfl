
section Member

inductive Member : List α -> α -> Type
  | head : Member (a::as) a
  | tail : Member bs a -> Member (b::bs) a
deriving DecidableEq, BEq, Ord, Repr open Member

end Member
