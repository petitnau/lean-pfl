import Dice.Ast
import Data.HList
import Data.Distribution
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLatticeIntervals
import Data.Probability
import Aesop
open BigOperators

def PDistribution (π: [Ty]') (τ: Ty): Type :=
  Value[π]ₕ -> 𝔻(τ)
notation "𝔻[" π "](" τ ")" => PDistribution π τ

namespace PDistribution

theorem eq_ext : ∀(a b: 𝔻[π](τ)), a = b ↔ ∀v, a v = b v := by
  intro a b; apply Iff.intro;
  intro h; rw [Function.funext_iff] at h; assumption
  intro h; funext v; exact h v

--------------------------
-- SIMPLE DISTRIBUTIONS --
--------------------------

instance instZero : Zero 𝔻[π](τ) := ⟨ fun _ => 0 ⟩
instance instOne : One 𝔻[π](τ) := ⟨ fun _ => 1 ⟩

------------------
-- INEQUALITIES --
------------------

instance instLE {τ: Ty}: LE 𝔻[π](τ) :=
  ⟨fun d1 d2 => ∀(v: Value[π]ₕ), d1 v ≤ d2 v⟩

theorem le_ext : ∀(a b: 𝔻[π](τ)), a ≤ b ↔ ∀v, a v ≤ b v := by
  intro a b; apply Iff.intro; all_goals (intro h; assumption)

instance instLT {τ: Ty}: LT 𝔻[π](τ) :=
  ⟨fun d1 d2 => d1 ≤ d2 ∧ ∃(v: Value[π]ₕ), d1 v < d2 v⟩

theorem lt_ext : ∀(a b: 𝔻[π](τ)), a < b ↔ a ≤ b ∧ ∃(v: Value[π]ₕ), a v < b v := by
  intro a b; apply Iff.intro; all_goals (intro h; assumption)

@[simp]
theorem zero_le : ∀(a: 𝔻[π](τ)), 0 ≤ a := by intro a v; exact Distribution.zero_le (a v)

@[simp]
theorem le_one : ∀(a: 𝔻[π](τ)), a ≤ 1 := by intro a v; exact Distribution.le_one (a v)

---------------
-- ADDITION  --
---------------

instance instAdd (τ: Ty): Add (𝔻[π](τ)) := ⟨fun a b => λv => (a v) + (b v)⟩
theorem add_ext (a: 𝔻[π](τ)) (b: 𝔻[π](τ)) : a + b = (λ v => (a v) + (b v)) := rfl

@[simp]
theorem zero_add_p : ∀(a: 𝔻[π](τ)), 0 + a = a := by
  intro a; unfold HAdd.hAdd instHAdd Add.add instAdd
  unfold OfNat.ofNat Zero.toOfNat0 Zero.zero instZero; simp_all

@[simp]
theorem add_zero_p : ∀(a: 𝔻[π](τ)), a + 0 = a := by
  intro a; unfold HAdd.hAdd instHAdd Add.add instAdd
  unfold OfNat.ofNat Zero.toOfNat0 Zero.zero instZero; simp_all

--------------------
-- MULTIPLICATION --
--------------------

instance instMul (τ: Ty): Mul (𝔻[π](τ)) := ⟨fun a b => λv => (a v) * (b v)⟩
theorem mul_ext (a: 𝔻[π](τ)) (b: 𝔻[π](τ)) : a * b = (λ v => (a v) * (b v)) := rfl

@[simp]
theorem zero_mul_p : ∀(a: 𝔻[π](τ)), 0 * a = 0 := by aesop

@[simp]
theorem one_mul_p : ∀(a: 𝔻[π](τ)), 1 * a = a := by
  intro a; unfold HMul.hMul instHMul Mul.mul instMul
  unfold OfNat.ofNat One.toOfNat1 One.one instOne; simp_all

instance instHMul' (τ: Ty): HMul ℙ (𝔻[π](τ)) (𝔻[π](τ)) := ⟨λp d => λ v => p * (d v)⟩
theorem pmul_ext (a: ℙ) (b: 𝔻[π](τ)) : a * b = (λ v => a * (b v)) := rfl

--------------
-- DIVISION --
--------------

instance instDiv (τ: Ty): Div (𝔻[π](τ)) := ⟨fun a b => λv => (a v) / (b v)⟩
theorem div_ext (a: 𝔻[π](τ)) (b: 𝔻[π](τ)) : a / b = (λ v => (a v) / (b v)) := rfl

-----------------
-- SUBTRACTION --
-----------------

noncomputable
instance instSub (τ: Ty): Sub (𝔻[π](τ)) := ⟨fun a b => λv => (a v) - (b v)⟩
theorem sub_ext (a: 𝔻[π](τ)) (b: 𝔻[π](τ)) : a - b = (λ v => (a v) - (b v)) := rfl

@[simp]
theorem sub_self_d : ∀(a: 𝔻[π](τ)), a - a = 0 := by
  intro a; unfold HSub.hSub instHSub Sub.sub instSub; funext; simp_all;
  conv_rhs => unfold OfNat.ofNat Zero.toOfNat0 Zero.zero instZero;

@[simp]
theorem sub_zero_p : ∀(a: 𝔻[π](τ)), a - 0 = a := by
  intro a; unfold HSub.hSub instHSub Sub.sub instSub
  unfold OfNat.ofNat Zero.toOfNat0 Zero.zero instZero; simp_all

-------------
-- SUP INF --
-------------

noncomputable instance instSup {τ: Ty}: Sup 𝔻[π](τ) :=
  ⟨ fun d1 d2 v => (d1 v) ⊔ (d2 v) ⟩

noncomputable instance instInf {τ: Ty}: Inf 𝔻[π](τ) :=
  ⟨ fun d1 d2 v => (d1 v) ⊓ (d2 v) ⟩

noncomputable instance instSupSet {τ: Ty}: SupSet 𝔻[π](τ) :=
  ⟨ fun s => fun v => sSup {d v | d ∈ s} ⟩
theorem sSup_ext (D: Set 𝔻[π](τ)) : sSup D = (λv => sSup {d v | d ∈ D}) := by aesop

noncomputable instance instInfSet {τ: Ty}: InfSet 𝔻[π](τ) :=
  ⟨ fun s => fun v => sInf {d v | d ∈ s} ⟩
theorem sInf_ext (D: Set 𝔻[π](τ)) : sInf D = (λv => sInf {d v | d ∈ D}) := by aesop

instance bot: Bot 𝔻[π](τ) := ⟨0⟩
instance top: Top 𝔻[π](τ) := ⟨1⟩

lemma sSup_apply (T: Set (𝔻[π](τ))) : sSup {t i | t ∈ T} = (sSup T) i := by aesop


---------------
-- INSTANCES --
---------------

instance instCommMonoid (τ: Ty): CommMonoid (𝔻[π](τ)) :=
  { mul_assoc := by
      intro a b c; rw [eq_ext]; intro v; simp [mul_ext];
      exact mul_assoc (a v) (b v) (c v)
  , mul_comm := by
      intro a b; rw [eq_ext]; intro v; simp [mul_ext];
      exact mul_comm (a v) (b v)
  , one_mul := by
      intro a; rw [eq_ext]; intro v; simp [mul_ext]
      exact one_mul (a v)
  , mul_one := by
      intro a; rw [eq_ext]; intro v; simp [mul_ext]
      exact mul_one (a v) }

instance instAddCommMonoid (τ: Ty): AddCommMonoid (𝔻[π](τ)) :=
  { add_assoc := by
      intro a b c; rw [eq_ext]; intro v; simp [add_ext];
      exact add_assoc (a v) (b v) (c v)
  , add_comm := by
      intro a b; rw [eq_ext]; intro v; simp [add_ext];
      exact add_comm (a v) (b v)
  , zero_add := by
      intro a; rw [eq_ext]; intro v; simp [add_ext];
      exact zero_add (a v)
  , add_zero := by
      intro a; rw [eq_ext]; intro v; simp [add_ext];
      exact add_zero (a v)
  , nsmul := λn a v => AddMonoid.nsmul n (a v)
  , nsmul_zero := by
      intro a; rw [eq_ext]; intro v; simp [add_ext];
      exact AddMonoid.nsmul_zero 0
  , nsmul_succ := by
      intro n a; rw [eq_ext]; intro v; simp [add_ext];
      exact AddMonoid.nsmul_succ n (a v) }

instance instPartialOrder {τ: Ty}: PartialOrder 𝔻[π](τ) :=
  { le_refl := by unfold LE.le instLE; simp
  , le_trans := by
      unfold LE.le instLE; simp
      intro a b c h1 h2 v
      apply le_trans
      exact h1 v
      exact h2 v
  , lt_iff_le_not_le := by
      intro a b;
      apply Iff.intro
      . rintro ⟨h1,h2⟩; constructor; exact h1;
        have ⟨w, wh⟩ := h2; intro h;
        apply (lt_iff_le_not_le.mp wh).right
        exact h w
      . intro ⟨h1,h2⟩; constructor; exact h1
        rw [le_ext] at h2; simp at h2; have ⟨w, wh⟩ := h2
        existsi w; apply (lt_iff_le_not_le.mpr ⟨h1 w,wh⟩)
  , le_antisymm := by
      intro d1 d2 h1 h2; funext v;
      unfold LE.le Preorder.toLE at h1 h2
      simp_all; exact (LE.le.le_iff_eq (h2 v)).mp (h1 v)
  }

noncomputable instance instCompleteLattice {τ: Ty}: CompleteLattice 𝔻[π](τ) :=
  { le_sup_left := λd1 d2 v => le_sup_left
  , le_sup_right := λd1 d2 v => le_sup_right
  , sup_le := λd1 d2 d3 h1 h2 v => sup_le (h1 v) (h2 v)
  , inf_le_left := λd1 d2 v => inf_le_left
  , inf_le_right := λd1 d2 v => inf_le_right
  , le_inf := λd1 d2 d3 h1 h2 v => le_inf (h1 v) (h2 v)
  , le_sSup := λs a h v => le_sSup (by aesop)
  , sSup_le := λs a h v => sSup_le (by aesop)
  , sInf_le := λs a h v => sInf_le (by aesop)
  , le_sInf := λs a h v => le_sInf (by aesop)
  , le_top := le_one
  , bot_le := zero_le }

-----------
-- OTHER --
-----------

open Classical in
@[simp]
theorem summation_ext (X: Finset α): ∀(f: α -> 𝔻[π](τ)), (∑x ∈ X, f x) y = ∑x ∈ X, f x y := by
  induction X using Finset.induction_on with
  | empty =>
    intro f; simp_all
    conv_lhs =>
      unfold OfNat.ofNat Zero.toOfNat0 Zero.zero AddMonoid.toZero
      unfold AddCommMonoid.toAddMonoid instAddCommMonoid instZero
  | insert h ih =>
    intro f; simp_all; rw [← ih f]; simp_all
    conv_lhs =>
      unfold HAdd.hAdd instHAdd Add.add AddZeroClass.toAdd
      unfold AddMonoid.toAddZeroClass AddSemigroup.toAdd
      unfold AddMonoid.toAddSemigroup AddCommMonoid.toAddMonoid
      unfold instAddCommMonoid instAdd
    simp_all

theorem sSup_add'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> 𝔻[π](τ)) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sSup ((f + g) '' X) = sSup (f '' X) + sSup (g '' X) := by
  rw [eq_ext, add_ext]; simp_all;
  intro v;
  rw [← sSup_apply]
  rw [← sSup_apply]
  rw [← sSup_apply]
  let f1 := λx => (f x v)
  let g1 := λx => (g x v)
  have : {x | ∃ t ∈ f '' X, t v = x} = f1 '' X := by aesop
  rw [this]
  have : {x | ∃ t ∈ g '' X, t v = x} = g1 '' X := by aesop
  rw [this]
  rw [← Distribution.sSup_add'']
  aesop; aesop; aesop;
  intro a b ab; (have : f a ≤ f b := by aesop); simp_all; apply ((le_ext (f a) (f b)).mp this);
  intro a b ab; (have : g a ≤ g b := by aesop); simp_all; apply ((le_ext (g a) (g b)).mp this);

theorem sSup_mul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> 𝔻[π](τ)) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sSup ((f * g) '' X) = sSup (f '' X) * sSup (g '' X) := by
  rw [eq_ext, mul_ext]; simp_all;
  intro v;
  rw [← sSup_apply]
  rw [← sSup_apply]
  rw [← sSup_apply]
  let f1 := λx => (f x v)
  let g1 := λx => (g x v)
  have : {x | ∃ t ∈ f '' X, t v = x} = f1 '' X := by aesop
  rw [this]
  have : {x | ∃ t ∈ g '' X, t v = x} = g1 '' X := by aesop
  rw [this]
  rw [← Distribution.sSup_mul'']
  aesop; aesop; aesop;
  intro a b ab; (have : f a ≤ f b := by aesop); simp_all; apply ((le_ext (f a) (f b)).mp this);
  intro a b ab; (have : g a ≤ g b := by aesop); simp_all; apply ((le_ext (g a) (g b)).mp this);

theorem sSup_cmul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> ℙ) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sSup ((λx => f x * g x) '' X) = sSup (f '' X) * sSup (g '' X) := by
  rw [eq_ext, pmul_ext]; simp_all;
  intro v;
  rw [← sSup_apply]
  rw [← sSup_apply]
  let g1 := λx => (g x v)
  have : {x | ∃ t ∈ g '' X, t v = x} = g1 '' X := by aesop
  rw [this]
  rw [← Distribution.sSup_cmul'']
  aesop; aesop; aesop;
  intro a b ab; (have : f a ≤ f b := by aesop); apply ((Probability.le_ext (f a) (f b)).mp this);
  intro a b ab; (have : g a ≤ g b := by aesop); simp_all; apply ((le_ext (g a) (g b)).mp this);

open Classical in
theorem sSup_summation [Preorder β] [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: β → α → 𝔻[π](τ)) (mf: ∀b x y, x ≤ y → f b x ≤ f b y) (B: Finset β)
  : ∑b ∈ B, (sSup {f b x | x ∈ X}) = sSup {∑b ∈ B, f b x | x ∈ X} := by
  rw [eq_ext]; intro v;
  let f1 := λa b => (f a b v)
  rw [summation_ext]
  rw [← sSup_apply]
  have : ∀x, {x_1 | ∃ t ∈ {x_2 | ∃ x_3 ∈ X, f x x_3 = x_2}, t v = x_1} = {f1 x y | y ∈ X} := by aesop
  conv_lhs => enter[2,x]; rw [← sSup_apply]; rw [this]; rfl;
  have : {x | ∃ t ∈ {x | ∃ x_1 ∈ X, ∑ b ∈ B, f b x_1 = x}, t v = x} = {∑b ∈ B, f1 b x | x ∈ X} := by aesop
  rw [this]
  rw [← Distribution.sSup_summation];
  aesop; aesop; aesop

end PDistribution
