/-
import Std.Data.Int.Order
import Mathlib.Tactic

inductive A where
  | a1 : A

inductive B : A -> Type where
  | b1 : B x

inductive C : List (List A × A) -> Type where
  | c1 : B y -> C x
  | c2 : C x -> C x

def count : C ((xs,x)::rest) -> Int
  | C.c1 _ => 0
  | C.c2 c' => 1 + count c'

-/
import Std.Data.Int.Order

inductive A where
  | a1 : A

inductive B : A -> Type where
  | b1 : B x

inductive C1 : List ( A) -> Type where
  | c1  {x y} : B y -> C1 x
  | c1'       : C1 x -> C1 (a::x)

-- C1.rec.{u} {a✝ : List (List A × A)} {motive : C1 a✝ → Sort u}
--  (c1 : {y : A} → (a : B y) → motive (C1.c1 a))
--  (t : C1 a✝) : motive t

inductive C2 : List (A) -> Type where
  | c2  {y x} : B y -> C2 x
  | c2'       : C2 x -> C2 (a::x)

-- C2.rec.{u} {motive : (a : List (List A × A)) → C2 a → Sort u}
--  (c2 : {y : A} → {x : List (List A × A)} → (a : B y) → motive x (C2.c2 a))
--  {a✝ : List (List A × A)} (t : C2 a✝) : motive a✝ t

#check C1.rec
#check C2.rec

/-
def count : C ((xs,x)::rest) -> Int
  | C.c1 _ => 0
  | C.c2 c' => 1 + count c'

theorem foo (c: C ((xs,x)::rest)) : @count xs x rest c ≥ 0 :=
  by
    -- generalize (xs, x) = X at c
    induction c with
    | c1 b => unfold count; simp
    | c2 c ih => unfold count; simp at ih; simp_all [Int.add_nonneg _ ih]

theorem foo' : ∀ {xs : List A} {x : A} {rest : List (List A × A)} (c : C ((xs, x) :: rest)), count c ≥ 0 :=
fun {xs} {x} {rest} c =>
  @C.rec ((xs, x) :: rest)
    (fun c => by sorry)
    (fun {y} b => by unfold count; simp)
    (fun c ih => by unfold count; simp at ih; simp_all [Int.add_nonneg _ ih])
    c

theorem foo'' (c: C ((xs, x)::rest)) : @count xs x rest c ≥ 0 :=
  have proof := @C.recOn
    ((xs, x)::rest)
    (fun full c => ∀xs x rest (h: (xs,x)::rest = full), @count xs x rest (by rw [h]; exact c) ≥ 0)
    c
    (by intro a full b xs' x' rest' h; aesop_subst h; unfold count; simp_all)
    (by intro full c ih xs x rest h; have ih' := ih xs x rest h; aesop_subst h; unfold count; simp_all; simp [Int.add_nonneg _ ih'])
  proof xs x rest rfl

/-
theorem foo : ∀ {xs : List A} {x : A} (c : C (xs, x)), count c ≥ 0 :=
fun {xs} {x} c =>
  C.rec
    (fun {y} b =>
      Eq.mpr (id (congrArg (fun x => x ≥ 0) (count._unfold (C.c1 b))))
        (of_eq_true (Eq.trans Std.Classes.Order._auxLemma.3 (Std.Data.Int.Init.Order._auxLemma.5 0))))
    (fun c ih =>
      Eq.mpr (id (congrArg (fun x => x ≥ 0) (count._unfold (C.c2 c))))
        (of_eq_true
          (Eq.trans Std.Classes.Order._auxLemma.3
            ((fun x_0 x_1 =>
                eq_true ((fun x_0 x_1 => Int.add_nonneg x_1 (Eq.mp Std.Classes.Order._auxLemma.3 ih)) x_0 x_1))
              1 (of_eq_true (eq_true_of_decide (Eq.refl true)))))))
    c
-/
#print foo
-/
