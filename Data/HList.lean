import Data.List
import Aesop

namespace List

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

---

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

-----

inductive HList {α : Type v} (β : α -> Type u) : List α -> Type (max u v)
  | nil  : HList β []
  | cons : β i -> HList β is -> HList β (i::is)

namespace HList

infix:67 " :: " => cons
notation "[" "]" => nil

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
  sorry

---

def snoc : HList β is -> β i -> HList β (List.snoc is i)
  | .nil, y => cons y .nil
  | .cons x xs, y => .cons x (snoc xs y)


@[simp]
theorem snoc_nil : snoc nil x  = cons x nil :=
  by unfold snoc; simp

---

def get : HList β is → Member i is → β i
  | .cons a _, Member.head => a
  | .cons _ as, Member.tail h => as.get h

---

def map {α : Type v} {β : α -> Type u} {γ : α -> Type u} {is : List α}  (f: ∀i, β i -> γ i) (h: HList β is) : HList γ is :=
  match is, h with
  | [], nil => nil
  | i::_, cons a as => cons (f i a) (map f as)

theorem map_id : map (fun _ x => x) h = h := by
  induction h <;> (unfold map; simp_all)

---

def app : HList β is -> HList β is' -> HList β (is ++ is')
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (app xs ys)

@[simp]
theorem cast_app (l1: HList β is1) (l2: HList β is2)
  (h: is1 ++ is2 = as1 ++ as2) (h1: is1 = as1) (h2: is2 = as2)
  : cast (app l1 l2) h = app (HList.cast l1 h1) (HList.cast l2 h2) :=
  sorry

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

---

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

---

end HList
