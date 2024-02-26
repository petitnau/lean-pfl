import Data.List

inductive HList {α : Type v} (β : α -> Type u) : List α -> Type (max u v)
  | nil  : HList β []
  | cons : β i -> HList β is -> HList β (i::is)
open HList

def map {α : Type v} {β : α -> Type u} {γ : α -> Type u} {is : List α}  (f: ∀i, β i -> γ i) (h: HList β is) : HList γ is :=
  match is, h with
  | [], nil => nil
  | i::_, cons a as => cons (f i a) (map f as)

def HList.get : HList β is → Member is i → β i
  | cons a _, Member.head => a
  | cons _ as, Member.tail h => as.get h
