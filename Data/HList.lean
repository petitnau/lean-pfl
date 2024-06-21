import Data.List
import Mathlib.Data.Set.Basic
import Aesop

---------------------
-- LIST EXTENSIONS --
---------------------

namespace List

notation "[" l "]'" => List l

----------
-- Snoc --

def snoc : List α -> α -> List α
  | .nil, a => .cons a .nil
  | .cons x xs, a => .cons x (snoc xs a)

@[simp]
theorem snoc_nil : snoc (@nil α) x  = cons x nil :=
  by unfold snoc; simp

@[simp]
theorem snoc_app : snoc xs x ++ ys = xs ++ cons x ys :=
  by
    induction xs with
    | nil => unfold snoc; simp
    | cons x xs ih =>
      unfold snoc; simp
      exact ih

-------------
-- Reverse --

def sreverse : List α -> List α
  | .nil => .nil
  | .cons x xs => List.snoc (sreverse xs) x

@[simp]
theorem sreverse_nil : sreverse (@nil α)  = nil :=
  by unfold sreverse; simp

theorem sreverse_cons_app
  : List.sreverse (i::is) ++ is'
  = List.sreverse is ++ (i::is')
  := by unfold sreverse; (conv => lhs; unfold sreverse; rfl); simp

end List

-------------------------
-- HETEROGENEOUS LISTS --
-------------------------

inductive HList {α : Type v} (β : α -> Type u) : List α -> Type (max u v)
  | nil  : HList β []
  | cons : β i -> HList β is -> HList β (i::is)
notation τ "[" l "]ₕ " => HList τ l
infixr:67 " ::ₕ " => HList.cons
notation " [""]ₕ " => HList.nil

namespace HList

infixr:67 " :: " => cons
notation "[" "]" => nil

----------
-- Cast --

def cast (l: HList β is) (h: is = is') : HList β is' :=
  h ▸ l

@[simp]
theorem cast_eq (l: HList β a) (h: a = a)
  : HList.cast l h = l
  := by aesop

@[simp]
theorem cast_trans (l: HList β a) (h1: a = b) (h2: b = c)
  : HList.cast (HList.cast l h1) h2 = HList.cast l (by simp_all)
  := by aesop

@[simp]
theorem cast_cons (x: β i) (l: HList β is)
  (h1: List.cons i is = List.cons a as) (h2: is = as) (h3: i = a)
  : HList.cast (@cons _ _ i is x l) h1 = @cons _ _ a as (h3 ▸ x) (HList.cast l h2) :=
  by aesop

----------
-- Snoc --

def snoc : HList β is -> β i -> HList β (List.snoc is i)
  | .nil, y => cons y .nil
  | .cons x xs, y => .cons x (snoc xs y)


@[simp]
theorem snoc_nil : snoc nil x  = cons x nil :=
  by unfold snoc; simp

---------
-- Get --

def get : HList β is → Member i is → β i
  | .cons a _, Member.head => a
  | .cons _ as, Member.tail h => as.get h

@[simp]
theorem get_head : (x ::ₕ xs).get Member.head = x := by aesop
@[simp]
theorem get_tail : (x ::ₕ xs).get (Member.tail t) = xs.get t := by aesop

def get' : HList β is → Member i (is++is') → Option (β i)
  | .cons a _, Member.head => some <| a
  | .cons _ as, Member.tail h => as.get' h
  | .nil, _ => none

def head : HList β (i::is) → β i
  | .cons a _ => a

def tail : HList β (i::is) → HList β is
  | .cons _ as => as

theorem get_head_head : HList.get x Member.head = HList.head x := by cases x; aesop
theorem get_tail_tail : HList.get x (.tail a) = HList.get (HList.tail x) a := by cases x; aesop

@[simp]
theorem head_cons : HList.head (x ::ₕ xs) = x := by aesop

@[simp]
theorem tail_cons : HList.tail (x ::ₕ xs) = xs := by aesop

@[simp]
theorem member_head (a: β α) (as: HList β γ) (s: Set (HList β (α::γ))) (h: a ::ₕ as ∈ s)
  : a ∈ {head e | e ∈ s} := by aesop

@[simp]
theorem member_tail (a: β α) (as: HList β γ) (s: Set (HList β (α::γ))) (h: a ::ₕ as ∈ s)
  : as ∈ {tail e | e ∈ s} := by aesop

---------
-- Map --

def map {α : Type v} {β : α -> Type u} {γ : α -> Type u} {is : List α} (f: ∀{i}, β i -> γ i) (h: HList β is) : HList γ is :=
  match is, h with
  | [], nil => nil
  | i::_, cons a as => cons (@f i a) (map f as)

def map' {α γ: Type v} {β : α -> Type u} {is : List α}  (f: ∀{i}, β i -> γ) (h: HList β is) : List γ :=
  match is, h with
  | [], nil => []
  | i::_, cons a as => (@f i a)::(map' f as)

def map'' {α : Type v} {β : α -> Type u} {γ : α -> Type u} {is : List α} (f: ∀{i}, β i -> Option (γ i)) (h: HList β is) : Option (HList γ is) :=
  match is, h with
  | [], nil => some nil
  | i::_, cons a as => do
    let as' <- (map'' f as)
    let a' := @f i a
    match a' with
    | none => none
    | some a' =>
      return cons a' as'

theorem map_id : map id h = h := by
  induction h <;> (unfold map; simp_all)

----------
-- Fold --

def fold {α : Type v} {β : α -> Type u} {γ : Type u} {is : List α} (f: ∀{i}, β i -> γ -> γ) (g: γ) (h: HList β is) : γ :=
  match h with
  | nil => g
  | cons a as => fold f (f a g) as

------------
-- Append --

def app : HList β is -> HList β is' -> HList β (is ++ is')
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (app xs ys)

@[simp]
theorem cast_app (l1: HList β is1) (l2: HList β is2)
  (h: is1 ++ is2 = as1 ++ as2) (h1: is1 = as1) (h2: is2 = as2)
  : cast (app l1 l2) h = app (HList.cast l1 h1) (HList.cast l2 h2) :=
  by aesop

@[simp]
theorem nil_app: HList.app HList.nil a = a := by
  aesop

@[simp]
theorem app_nil {a: HList β is}: a.app HList.nil = a.cast (by simp) := by
  induction a with
  | nil => aesop;
  | cons b as ih => rename_i i is'; unfold app; simp_all

theorem app_cons
  : HList.app (HList.cons i is) is'
  = HList.cons i (HList.app is is')
  := by induction is <;> unfold app; simp; rfl

@[simp]
theorem snoc_app
  : HList.app (snoc xs x) ys
  = (HList.app xs (cons x ys)).cast (by simp)
  := by
    induction xs with
    | nil => unfold snoc app; simp
    | cons x xs ih => unfold snoc app; simp_all

-------------
-- Reverse --

def reverse : HList β is -> HList β (is.sreverse)
  | .nil => .nil
  | .cons x xs => .snoc (HList.reverse xs) x

@[simp]
theorem reverse_id: HList.reverse HList.nil = (@HList.nil α β) := by
  aesop

theorem app_rev
  : (HList.app (HList.reverse (HList.cons i is)) is')
  = (HList.app (HList.reverse is) (HList.cons i is')).cast List.sreverse_cons_app.symm
  := by (conv => lhs; unfold reverse; rfl); simp

end HList
