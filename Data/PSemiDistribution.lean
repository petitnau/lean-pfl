import Dice.Ast
import Data.HList
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.Pointwise
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Data.SemiDistribution
import Aesop
open BigOperators

abbrev PSemiDistribution (π: [Ty]') (τ: Ty): Type :=
  Value[π]ₕ -> 𝔻(τ)
notation "𝔻[" π "](" τ ")" => PSemiDistribution π τ

namespace PSemiDistribution

--------------------------
-- SIMPLE DISTRIBUTIONS --
--------------------------

notation "⟪" v "⟫" => (λx => v : 𝔻(_))

@[simp]
theorem zero_le : ∀(a: 𝔻[π](τ)), 0 ≤ a := by intro a v; exact SemiDistribution.zero_le (a v)

@[simp]
theorem le_one : ∀(a: 𝔻[π](τ)), a ≤ 1 := by intro a v; exact SemiDistribution.le_one (a v)

---------------
--------------------
-- MULTIPLICATION --
--------------------

instance instHMul' (τ: Ty): HMul ℙ (𝔻[π](τ)) (𝔻[π](τ)) := ⟨λp d => λ v => p * (d v)⟩
theorem pmul_ext (a: ℙ) (b: 𝔻[π](τ)) : a * b = (λ v => a * (b v)) := rfl

theorem pmul_le_pmul (a b: ℙ) (c d: 𝔻[π](τ)) : a ≤ b → c ≤ d → a * c ≤ b * d := by
  intro h1 h2; rw [Pi.le_def]; intro v; rw [pmul_ext, pmul_ext];
  have : c v ≤ d v := by aesop;
  apply SemiDistribution.pmul_le_pmul <;> aesop

-----------------
-- SUBTRACTION --
-----------------

@[simp]
theorem sub_self_d : ∀(a: 𝔻[π](τ)), a - a = 0 := by
  intro a; unfold HSub.hSub instHSub Sub.sub Pi.instSub; funext; simp_all;

@[simp]
theorem sub_zero_p : ∀(a: 𝔻[π](τ)), a - 0 = a := by
  intro a; unfold HSub.hSub instHSub Sub.sub Pi.instSub
  unfold OfNat.ofNat Zero.toOfNat0 Zero.zero Pi.instZero; simp_all

-----------
-- OTHER --
-----------

open Classical in
@[simp]
theorem summation_ext (X: Finset α): ∀(f: α -> 𝔻[π](τ)), (∑x ∈ X, f x) y = ∑x ∈ X, f x y := by
  induction X using Finset.induction_on <;> simp_all

theorem sSup_add'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: α -> 𝔻[π](τ)) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sSup ((f + g) '' X) = sSup (f '' X) + sSup (g '' X) := by
  funext v; rw [Pi.add_def]; simp_all;
  rw [sSup_apply']
  rw [sSup_apply']
  rw [sSup_apply']
  simp_all
  let f1 := λx => (f x v)
  let g1 := λx => (g x v)
  have : {x | ∃ a ∈ X, f a v = x} = f1 '' X := by aesop
  rw [this]
  have : {x | ∃ a ∈ X, g a v = x} = g1 '' X := by aesop
  rw [this]
  rw [← SemiDistribution.sSup_add'']
  aesop; aesop; aesop;
  intro a b ab; aesop;
  intro a b ab; aesop

theorem sInf_add'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: α -> 𝔻[π](τ)) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sInf ((f + g) '' X) = sInf (f '' X) + sInf (g '' X) := by
  funext v; rw [Pi.add_def]; simp_all;
  rw [sInf_apply']
  rw [sInf_apply']
  rw [sInf_apply']
  simp_all
  let f1 := λx => (f x v)
  let g1 := λx => (g x v)
  have : {x | ∃ a ∈ X, f a v = x} = f1 '' X := by aesop
  rw [this]
  have : {x | ∃ a ∈ X, g a v = x} = g1 '' X := by aesop
  rw [this]
  rw [← SemiDistribution.sInf_add'']
  aesop; aesop; aesop;
  intro a b ab; aesop;
  intro a b ab; aesop

theorem sSup_mul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: α -> 𝔻[π](τ)) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sSup ((f * g) '' X) = sSup (f '' X) * sSup (g '' X) := by
  funext v; rw [Pi.mul_def]; simp_all;
  rw [sSup_apply']
  rw [sSup_apply']
  rw [sSup_apply']
  simp_all
  let f1 := λx => (f x v)
  let g1 := λx => (g x v)
  have : {x | ∃ a ∈ X, f a v = x} = f1 '' X := by aesop
  rw [this]
  have : {x | ∃ a ∈ X, g a v = x} = g1 '' X := by aesop
  rw [this]
  rw [← SemiDistribution.sSup_mul'']
  aesop; aesop; aesop;
  intro a b ab; aesop;
  intro a b ab; aesop

theorem sInf_mul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: α -> 𝔻[π](τ)) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sInf ((f * g) '' X) = sInf (f '' X) * sInf (g '' X) := by
  funext v; rw [Pi.mul_def]; simp_all;
  rw [sInf_apply']
  rw [sInf_apply']
  rw [sInf_apply']
  simp_all
  let f1 := λx => (f x v)
  let g1 := λx => (g x v)
  have : {x | ∃ a ∈ X, f a v = x} = f1 '' X := by aesop
  rw [this]
  have : {x | ∃ a ∈ X, g a v = x} = g1 '' X := by aesop
  rw [this]
  rw [← SemiDistribution.sInf_mul'']
  aesop; aesop; aesop;
  intro a b ab; aesop;
  intro a b ab; aesop

theorem sSup_cmul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: α -> ℙ) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sSup ((λx => f x * g x) '' X) = sSup (f '' X) * sSup (g '' X) := by
  funext v; rw [pmul_ext]; simp_all;
  rw [sSup_apply']
  rw [sSup_apply']
  simp_all
  let g1 := λx => (g x v)
  have : {x | ∃ a ∈ X, g a v = x} = g1 '' X := by aesop
  rw [this]
  rw [← SemiDistribution.sSup_cmul'']
  aesop; aesop; aesop;
  intro a b ab; aesop
  intro a b ab; aesop

theorem sInf_cmul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: α -> ℙ) (mf: Monotone f) (g: α -> 𝔻[π](τ)) (mg: Monotone g)
  : sInf ((λx => f x * g x) '' X) = sInf (f '' X) * sInf (g '' X) := by
  funext v; rw [pmul_ext]; simp_all;
  rw [sInf_apply']
  rw [sInf_apply']
  simp_all
  let g1 := λx => (g x v)
  have : {x | ∃ a ∈ X, g a v = x} = g1 '' X := by aesop
  rw [this]
  rw [← SemiDistribution.sInf_cmul'']
  aesop; aesop; aesop;
  intro a b ab; aesop
  intro a b ab; aesop

open Classical in
theorem sSup_summation [Preorder β] [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: β → α → 𝔻[π](τ)) (mf: ∀b x y, x ≤ y → f b x ≤ f b y) (B: Finset β)
  : ∑b ∈ B, (sSup {f b x | x ∈ X}) = sSup {∑b ∈ B, f b x | x ∈ X} := by
  funext v
  let f1 := λa b => (f a b v)
  rw [summation_ext]
  rw [sSup_apply']
  have : ∀x, {x_1 | ∃ t ∈ {x_2 | ∃ x_3 ∈ X, f x x_3 = x_2}, t v = x_1} = {f1 x y | y ∈ X} := by aesop
  conv_lhs => enter[2,x]; rw [sSup_apply'];
  simp_all;
  have : {x | ∃ a ∈ X, ∑ c ∈ B, f c a v = x} = {∑b ∈ B, f1 b x | x ∈ X} := by aesop
  rw [this]
  rw [← SemiDistribution.sSup_summation];
  aesop; aesop; aesop

open Classical in
theorem sInf_summation [Preorder β] [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· ≤ ·) X) (f: β → α → 𝔻[π](τ)) (mf: ∀b x y, x ≤ y → f b x ≤ f b y) (B: Finset β)
  : ∑b ∈ B, (sInf {f b x | x ∈ X}) = sInf {∑b ∈ B, f b x | x ∈ X} := by
  funext v
  let f1 := λa b => (f a b v)
  rw [summation_ext]
  rw [sInf_apply']
  have : ∀x, {x_1 | ∃ t ∈ {x_2 | ∃ x_3 ∈ X, f x x_3 = x_2}, t v = x_1} = {f1 x y | y ∈ X} := by aesop
  conv_lhs => enter[2,x]; rw [sInf_apply'];
  simp_all;
  have : {x | ∃ a ∈ X, ∑ c ∈ B, f c a v = x} = {∑b ∈ B, f1 b x | x ∈ X} := by aesop
  rw [this]
  rw [← SemiDistribution.sInf_summation];
  aesop; aesop; aesop

end PSemiDistribution
