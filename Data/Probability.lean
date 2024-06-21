import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Order.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Data.DReal
import Data.RealExtra
open BigOperators Pointwise

@[simp]
theorem min_three_sum (a b c l: ℝ) (c0: 0 ≤ c)
  : min l ((min l (a + b)) + c) = min l (a + b + c) := by
  by_cases (a + b) ≤ l
  case pos _ => aesop
  case neg h =>
    have h : l < a + b := by aesop
    have : min l ((min l (a + b)) + c) = min l (l + c) := by simp [LT.lt.le h]
    rw [this]
    have : l ≤ l + c := by aesop
    rw [min_eq_left this]
    simp [le_add_of_nonneg_of_le c0 (LT.lt.le h), add_comm]

def Probability : Type := {r : DReal // r ≤ 1}
notation "ℙ" => Probability

namespace Probability

def fromRealPos (x: ℝ) (h: 0 < x ∧ x ≤ 1): Probability :=
  ⟨DReal.fromRealPos x h.left, h.right⟩

noncomputable def fromDReal (x: DReal) (h: x ≤ 1) : Probability := ⟨x, h⟩

@[coe] def toDReal : Probability → DReal := Subtype.val
instance : Coe Probability DReal := ⟨toDReal⟩

@[simp]
theorem fromReal_ext : (fromDReal a h).toDReal = a := by
  unfold fromDReal; aesop

theorem eq_ext : ∀(a b: Probability), a = b ↔ a.toDReal = b.toDReal := by
  intro a b; unfold toDReal;
  apply Iff.intro
  . intro h; rw [h]
  . exact Subtype.eq

--------------------
-- SIMPLE NUMBERS --
--------------------

instance instZero : Zero (Probability) :=
  ⟨ ⟨0, DReal.zero_le_one⟩ ⟩

@[simp]
theorem zero_ext : (0 : Probability).toDReal = 0 := by rfl

instance instOne : One (Probability) :=
  ⟨ ⟨1, by simp⟩ ⟩

@[simp]
theorem one_ext : (1 : Probability).toDReal = 1 := by rfl

instance instInhabited : Inhabited DReal :=
  ⟨ 0 ⟩

----------------
-- INEQUALITY --
----------------

instance instLE : LE (Probability) := ⟨fun x y => x.toDReal ≤ y.toDReal⟩

theorem le_ext : ∀(a b: Probability), a ≤ b ↔ a.toDReal ≤ b.toDReal := by
  intro a b; (conv => lhs; unfold_projs); rfl

theorem zero_le : ∀(a: Probability), 0 ≤ a := by
  intro a; rw [le_ext]; simp [DReal.zero_le];

theorem le_one : ∀(a: Probability), a ≤ 1 := by
  intro a; cases' a with v p; aesop

@[simp]
theorem zero_le_real : ∀(a: Probability), 0 ≤ a.toDReal := by
  intro a; exact zero_le a

theorem zero_le_one : (0 : Probability) ≤ 1 := by
  rw [le_ext]; simp

theorem le_total : ∀ (a b: Probability), a ≤ b ∨ b ≤ a := by
  intro a b; rw [le_ext, le_ext]; simp  [@LinearOrder.le_total DReal _ _ _]

-----------------------
-- STRICT INEQUALITY --
-----------------------

instance instLT : LT (Probability) := ⟨fun x y => x.toDReal < y.toDReal⟩

@[simp]
theorem lt_ext : ∀(a b: Probability), a < b ↔ a.toDReal < b.toDReal := by
  intro a b; (conv => lhs; unfold_projs); rfl

theorem zero_lt_one : (0: Probability) < 1 := by
  rw [lt_ext]; simp

--------------
-- ADDITION --
--------------

instance instAdd : Add (Probability) := ⟨ fun a b => ⟨DReal.minc' 1 (a.val + b.val), by simp⟩ ⟩

@[simp]
theorem add_ext : ∀(a b: Probability), (a + b).toDReal = DReal.minc' 1 (a.toDReal + b.toDReal) := by
  intro a b; (conv => lhs; unfold HAdd.hAdd instHAdd Add.add instAdd); rfl

@[simp]
lemma zero_add' : ∀(a: Probability), 0 + a = a := by
  intro a; rw [eq_ext, add_ext]; simp; exact a.prop

@[simp]
lemma add_zero' : ∀(a: Probability), a + 0 = a := by
  intro a; rw [eq_ext, add_ext]; simp; exact a.prop

lemma add_comm' : ∀(a b: Probability), a + b = b + a := by
  intro a b; rw [eq_ext]; simp [add_comm]

lemma add_assoc' : ∀(a b c: Probability), (a + b) + c = a + (b + c) := by
  intro a b c; rw [eq_ext, DReal.eq_ext]; simp
  conv => rhs; rhs; rw [add_comm]
  simp; simp [add_comm, add_assoc]

def add_inv (a: Probability) (_: a < 1): Probability :=
  match a with
  | ⟨⟨_, .inl _⟩, _⟩ => ⟨1, by rfl⟩
  | ⟨⟨x, .inr h'⟩, h''⟩ =>
    { val := DReal.fromRealPos (1 - x) (by simp; rwa [DReal.le_ext] at h'')
    , property := by unfold DReal.fromRealPos; rw [DReal.le_ext]; simp; exact LT.lt.le h' }

--------------------
-- MULTIPLICATION --
--------------------

instance instMul : Mul (Probability) := ⟨ fun a b =>
  ⟨(a.val * b.val), by
    rw [DReal.le_ext];
    have h1 : a.toDReal.toReal ≤ 1 := by rw [←DReal.one_ext, ←DReal.le_ext]; exact a.prop
    have h2 : 0 ≤ b.toDReal.toReal := by rw [←DReal.zero_ext, ←DReal.le_ext]; exact DReal.zero_le _
    have h3 : b.val.toReal ≤ 1 := by rw [←DReal.one_ext, ←DReal.le_ext]; exact b.prop
    simp; exact mul_le_one h1 h2 h3⟩ ⟩

@[simp]
theorem mul_ext : ∀(a b: Probability), (a * b).toDReal = a.toDReal * b.toDReal := by
  intro a b; (conv => lhs; unfold HMul.hMul instHMul Mul.mul instMul); rfl

@[simp]
lemma mul_zero' : ∀(a: Probability), a * 0 = 0 := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma zero_mul' : ∀(a: Probability), 0 * a = 0 := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma mul_one' : ∀(a: Probability), a * 1 = a := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma one_mul' : ∀(a: Probability), 1 * a = a := by
  intro a; rw [eq_ext]; simp

lemma mul_comm' : ∀(a b: Probability), a * b = b * a := by
  intro a b; rw [eq_ext]; simp [mul_comm]

lemma mul_assoc' : ∀(a b c: Probability), (a * b) * c = a * (b * c) := by
  intro a b c; rw [eq_ext]; simp [mul_assoc]

--------------
-- DIVISION --
--------------

instance instDiv : Div Probability := ⟨ fun a b => ⟨DReal.minc' 1 (a.val * b.val⁻¹), by simp⟩⟩

def divD (a: Probability) (b: DReal): Probability :=
  ⟨DReal.minc' 1 (a.val * b⁻¹), by simp⟩

  ---------------
-- MIN & MAX --
---------------

def minc' : Probability -> Probability -> Probability
  | x, y => ⟨DReal.minc' x.val y.val, by simp; left; exact x.prop⟩
instance : Min Probability := ⟨ minc' ⟩

@[simp]
theorem min_ext : ∀(a b: Probability), (min a b).toDReal = Min.min a.toDReal b.toDReal := by
  intro a b; (conv => lhs; unfold min instMin minc'); simp; norm_cast

def maxc' : Probability -> Probability -> Probability
  | x, y => ⟨DReal.maxc' x.val y.val, by simp; constructor; exact x.prop; exact y.prop⟩
instance : Max Probability := ⟨ maxc' ⟩

@[simp]
theorem max_ext : ∀(a b: Probability), (max a b).toDReal = Max.max a.toDReal b.toDReal := by
  intro a b; (conv => lhs; unfold min instMax maxc'); simp; norm_cast

---------------------
-- SUPSET & INFSET --
---------------------

open Classical in noncomputable
instance instSupSetProbability : SupSet Probability := ⟨ fun S => fromDReal (sSup {toDReal x | x ∈ S}) (by
  have : ∀x ∈ {toDReal x | x ∈ S}, x ≤ 1 := by rintro x ⟨xX, _, xXh2⟩; rw [← xXh2, ← one_ext, ← le_ext]; exact le_one xX
  rcases {toDReal x | x ∈ S}.eq_empty_or_nonempty with (x | ne)
  . rw [x]; simp; unfold sSup DReal.instSupSet; rw [DReal.le_ext]; simp
  . exact csSup_le ne this)⟩

@[simp]
lemma supSet_ext : ∀(s: Set Probability), (sSup s).toDReal = sSup {toDReal x | x ∈ s} := by
  intro s; unfold sSup instSupSetProbability DReal.instSupSet; simp

open Classical in noncomputable
instance instInfSetProbability: InfSet Probability := ⟨ fun S =>
    if S.Nonempty then fromDReal (sInf {toDReal x | x ∈ S}) (by
  have : ∀x ∈ {toDReal x | x ∈ S}, x ≤ 1 := by rintro x ⟨xX, _, xXh2⟩; rw [← xXh2, ← one_ext, ← le_ext]; exact le_one xX
  rcases {toDReal x | x ∈ S}.eq_empty_or_nonempty with (x | ne)
  . rw [x]; simp; unfold sInf DReal.instInfSet; rw [DReal.le_ext]; simp
  . have this1 : BddBelow {toDReal x | x ∈ S} := by
      unfold BddBelow lowerBounds Set.Nonempty; simp_all
      existsi 0; intro a; simp
    have ⟨e, eh⟩ := ne
    have ⟨ehv, ⟨_, ehh2⟩⟩ := eh
    have :  e ≤ 1 := by simp_all; rw [← ehh2, ← one_ext, ← le_ext]; exact le_one ehv
    exact csInf_le_of_le this1 eh this) else 1⟩

@[simp]
lemma infSet_ext : ∀{s: Set Probability}, Set.Nonempty s → (sInf s).toDReal = sInf {toDReal x | x ∈ s} := by
  intro s h; unfold sInf instInfSetProbability DReal.instInfSet; aesop

@[simp]
lemma infSet_ext_empty : sInf (∅: Set Probability) = 1 := by
  unfold sInf instInfSetProbability; simp

-----------------------------------
-- SEMIFIELD AND OTHER INSTANCES --
-----------------------------------

def nsmul : ℕ -> Probability -> Probability
  | 0, _            => ⟨0, by aesop⟩
  | .succ a, ⟨x, _⟩ => ⟨DReal.minc' 1 (a.succ * x), (by simp_all [← Nat.add_one, Nat.cast_add, DReal.le_ext] ) ⟩

@[simp]
theorem nsmul_ext : ∀(x: Probability), (nsmul n x).toDReal = DReal.minc' 1 (DReal.nsmul n (x.toDReal)) := by
  induction n with
  | zero =>
    intro x; unfold nsmul DReal.nsmul; rw [DReal.eq_ext]; aesop
  | succ n _ =>
    intro x; unfold nsmul DReal.nsmul toDReal; cases' x with v p
    cases' v with vv vp;
    cases' vp with pp pp;
    . simp; rw [DReal.eq_ext]; simp; rw [← pp]; simp
    . rw [DReal.eq_ext]; simp_all

instance instAddCommMonoid : AddCommMonoid  (Probability) :=
  { nsmul := nsmul
  , nsmul_zero := by intro x; unfold nsmul; unfold_projs; simp
  , nsmul_succ := by
      intro n x; rw [eq_ext]; simp_all; rw [Nat.add_one]; unfold DReal.nsmul
      cases' x with v p
      cases' v with vv vp
      cases' vp with vp vp
      . unfold toDReal; simp_all; rw [DReal.eq_ext];
        unfold DReal.toReal; aesop
      . rw [DReal.eq_ext]; simp_all; split <;> aesop;
        rw [DReal.eq_ext] at heq_1; simp_all
        unfold DReal.toReal toDReal at heq_1; simp_all
        rw [DReal.le_ext] at p; simp_all
        simp_all
        by_cases 1 ≤ (↑a + 1) * vv
        . conv_rhs => rhs; rw [min_def]
          by_cases 1 ≤ 1 + vv
          . simp_all; nlinarith
          . simp_all; nlinarith
        . conv_rhs => rhs; rw [min_def]
          aesop;
          . nlinarith;
          . congr; nlinarith
  , add_assoc := add_assoc'
  , zero_add := zero_add'
  , add_zero := add_zero'
  , add_comm := add_comm' }

instance instCommMonoid : CommMonoid  (Probability) :=
  { mul_assoc := mul_assoc'
  , one_mul := one_mul'
  , mul_one := mul_one'
  , mul_comm := mul_comm' }

instance instPartialOrder : PartialOrder Probability where
  lt_iff_le_not_le a b := by
    rw [lt_ext, le_ext, le_ext]; exact lt_iff_le_not_le
  le_refl a := by
    rw [le_ext]
  le_trans a b c := by
    rw [le_ext, le_ext, le_ext]; exact le_trans
  le_antisymm a b := by
    rw [le_ext, le_ext, eq_ext]; exact le_antisymm

instance : OrderedAddCommMonoid Probability :=
  { add_le_add_left := by
      intro a b; rw [le_ext]; intro h c; rw [le_ext]; simp_all }

lemma all_bddabove (S: Set Probability): BddAbove S := by
  unfold BddAbove upperBounds Set.Nonempty; simp
  existsi 1; intro a _; exact le_one a

lemma all_bddbelow (S: Set Probability): BddBelow S := by
  unfold BddBelow lowerBounds Set.Nonempty; simp
  existsi 0; intro a _; exact zero_le a

noncomputable instance instCompleteLattice : CompleteLattice Probability :=
  { sup := fun a b => max a b
  , le_sup_left := by intro a b; rw [le_ext]; aesop
  , le_sup_right := by intro a b; rw [le_ext]; aesop
  , sup_le := by intro a b c h1 h2 ; rw [le_ext]; aesop
  , inf := fun a b => min a b
  , inf_le_left := by intro a b; rw [le_ext]; aesop
  , inf_le_right := by intro a b; rw [le_ext]; aesop
  , le_inf :=  by intro a b c h1 h2 ; rw [le_ext]; aesop
  , le_sSup := by
      intro s a h;
      have uhs : toDReal a ∈ {toDReal x | x ∈ s} := by aesop
      have uha : BddAbove {toDReal x | x ∈ s} := by
        unfold BddAbove upperBounds Set.Nonempty at *; simp_all
        existsi 1; intro a _; rw [← one_ext, ← le_ext]; exact le_one a
      unfold sSup instSupSetProbability; simp; rw [le_ext]; simp
      exact le_csSup uha uhs
  , sSup_le := by
      intro s a h;
      rcases {toDReal x | x ∈ s}.eq_empty_or_nonempty with (h1 | h1)
      . unfold sSup instSupSetProbability; simp_all [DReal.sSup_empty];
        rw [le_ext]; simp
      . have uha : ∀ b ∈ {toDReal x | x ∈ s}, b ≤ a := by
          simp_all; intro a1 as; rw [← le_ext]; exact h a1 as
        rw [le_ext, supSet_ext]; exact csSup_le h1 uha
  , sInf_le := by
      intro s a h;
      have uhs : toDReal a ∈ {toDReal x | x ∈ s} := by aesop
      have uha : BddBelow {toDReal x | x ∈ s} := by
        unfold BddBelow lowerBounds Set.Nonempty at *; simp_all
        existsi 0; intro a _; rw [← zero_ext, ← le_ext]; exact zero_le a
      rcases s.eq_empty_or_nonempty with (h1 | h1)
      . simp_all
      . rw [le_ext, infSet_ext h1]; exact csInf_le uha uhs
  , le_sInf := by
      intro s a h;
      rcases s.eq_empty_or_nonempty with (h1 | h1)
      . simp_all; exact le_one a
      . rw [le_ext, infSet_ext h1];
        have ne : Set.Nonempty {toDReal x | x ∈ s} := by
          unfold Set.Nonempty at *; simp_all
          have ⟨x, p⟩ := h1
          existsi x; existsi x; exact ⟨p, rfl⟩
        have : ∀b ∈ {toDReal x | x ∈ s}, ↑a ≤ b := by aesop
        exact le_csInf ne this
  , top := 1
  , bot := 0
  , le_top := by simp [le_one]
  , bot_le := by simp [zero_le]
  }
/-
noncomputable instance : CompleteLattice Probability := by
  have y := Set.Icc.completeLattice DReal.zero_le_one
  have : Probability = ↑(Set.Icc (0: DReal) 1) := by
    unfold Set.Icc;
    rw [Probability]; congr; funext x; simp [DReal.zero_le]
  simpa [this]
-/
theorem mul_le_mul' {a b c d: Probability} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := by
  rw [le_ext, DReal.le_ext] at *; simp_all [mul_le_mul]

noncomputable
instance instSub : Sub (Probability) := ⟨ fun a b => ⟨a.val - b.val, by
  have b0 : 0 ≤ b.toDReal.toReal := by aesop
  have a1 : a.toDReal.toReal ≤ 1 := by rw [← DReal.one_ext, ← DReal.le_ext, ← one_ext, ← le_ext]; exact le_one a
  have : a.toDReal.toReal - b.toDReal.toReal ≤ 1 - 0 := sub_le_sub a1 b0
  have : a.toDReal.toReal - b.toDReal.toReal ≤ 1 := by aesop
  have : a.toDReal - b.toDReal ≤ 1 := by rw [DReal.le_ext]; simp; linarith
  exact this ⟩ ⟩

@[simp]
theorem sub_ext : ∀(a b: Probability), (a - b).toDReal = a.toDReal - b.toDReal := by
  intro a b; (conv => lhs; unfold HSub.hSub instHSub Sub.sub instSub); aesop

@[simp]
theorem sub_self : ∀(a: Probability), a - a = 0 := by
  intro a; rw [eq_ext]; simp_all

@[simp]
theorem sub_zero : ∀(a: Probability), a - 0 = a := by
  intro a; rw [eq_ext]; simp_all

----------------
-- CONTINUITY --
----------------

theorem sSup_mul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> ℙ) (mf: Monotone f) (g: α -> ℙ) (mg: Monotone g)
  : sSup ((f * g) '' X) = sSup (f '' X) * sSup (g '' X) := by
  rw [eq_ext, DReal.eq_ext]; simp_all
  apply Real.sSup_mul''; all_goals aesop

theorem sSup_add'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> ℙ) (mf: Monotone f) (g: α -> ℙ) (mg: Monotone g)
  : sSup ((f + g) '' X) = sSup (f '' X) + sSup (g '' X) := by
  rw [eq_ext, DReal.eq_ext]; simp_all
  let f1 := λx => (f x).toDReal.toReal
  let g1 := λx => (g x).toDReal.toReal
  have := Real.sSup_add'' X neX cX f1 ?_ g1 ?_
  have fe : {x | ∃ a ∈ X, (f a).toDReal.toReal = x} = f1 '' X := by aesop
  have ge : {x | ∃ a ∈ X, (g a).toDReal.toReal = x} = g1 '' X := by aesop
  conv_rhs => rhs; rw [fe, ge, ← this]
  have : {x | ∃ a ∈ X, min 1 ((f a).toDReal.toReal + (g a).toDReal.toReal) = x} = {min 1 x | x ∈ (f1 + g1) '' X} := by aesop
  rw [this]; apply Real.sSup_mina'; apply Monotone.map_bddAbove; apply Monotone.add; all_goals aesop;

open Classical in
theorem sSup_summation [Preorder β] [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: β → α → ℙ) (mf: ∀b x y, x ≤ y → f b x ≤ f b y) (B: Finset β)
  : ∑b ∈ B, (sSup {f b x | x ∈ X}) = sSup {∑b ∈ B, f b x | x ∈ X} := by
  have : Nonempty X := by aesop
  apply @Finset.induction_on _ _ _ B _ _
  . aesop
  . intro a s ans ih
    rw [Finset.sum_insert ans, ih];
    (conv_rhs => congr; ext; congr; ext; congr; ext; rw [Finset.sum_insert ans]);
    symm; apply sSup_add''; all_goals aesop;
    . intro x y xy; simp_all;apply Finset.sum_le_sum; intro i _; apply mf i; assumption


end Probability
