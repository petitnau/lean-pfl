import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Lean.Meta.AppBuilder
import Lean.Expr
import Data.HList
import Data.List
import Data.Probability
import Data.FlipProb

open BigOperators Probability

inductive Ty where
  | TBool : Ty
  | TPair : Ty -> Ty -> Ty
deriving DecidableEq, BEq, Ord, Repr open Ty
notation "𝔹" => TBool
infix:67 " :×: " => TPair

def Sig: Type := List Ty × Ty

inductive Value : Ty -> Type where
  | VTrue  : Value 𝔹
  | VFalse : Value 𝔹
  | VPair  : Value τ₁ -> Value τ₂ -> Value (τ₁ :×: τ₂)
deriving DecidableEq, BEq, Repr open Value

inductive AExpr : [Ty]' -> Ty -> Type where
  | AVar   : Member τ δ -> AExpr δ τ
  | AValue : Value τ -> AExpr δ τ
deriving DecidableEq, BEq, Repr open AExpr

inductive Expr (Γ: [Sig]') : [Ty]' -> Ty -> Type where
  | Atomic  : AExpr π τ           -> Expr Γ π τ
  | Fst     : AExpr π (τ₁ :×: τ₂) -> Expr Γ π τ₁
  | Snd     : AExpr π (τ₁ :×: τ₂) -> Expr Γ π τ₂
  | Flip    : FlipProb            -> Expr Γ π 𝔹
  | Observe : AExpr π 𝔹           -> Expr Γ π 𝔹
  | Pair    : AExpr π τ₁          -> AExpr π τ₂         -> Expr Γ π (τ₁ :×: τ₂)
  | Let     : Expr Γ π τ₁         -> Expr Γ (τ₁::π) τ₂  -> Expr Γ π τ₂
  | Call    : Member (π', τ) Γ    -> HList (AExpr π) π' -> Expr Γ π τ
  | Ifte    : AExpr π 𝔹           -> Expr Γ π τ         -> Expr Γ π τ           -> Expr Γ π τ
open Expr

abbrev Func (Γ: [Sig]') (π: [Ty]') (τ: Ty): Type
  := Expr ((π,τ)::Γ) π τ

inductive Program (τ: Ty) : [Sig]' -> [Sig]' -> Type where
  | PFunc : Func Γ π' τ' -> Program τ ((π',τ')::Γ) Γ' -> Program τ Γ ((π',τ')::Γ')
  | PExpr : Expr Γ [] τ  -> Program τ Γ []
open Program

-----------------
-- DESTRUCTORS --
-----------------

def AExpr.value : AExpr [] τ → Value τ
  | AValue v => v

----------------
-- PROPERTIES --
----------------

-- Values of any type are finite
instance fintype (τ: Ty) : Fintype (Value τ) :=
  let f : ∀{τ₁ τ₂: Ty}, (Value τ₁ × Value τ₂) -> (Value (τ₁ :×: τ₂)) :=
    fun (v1,v2) => VPair v1 v2
  have inj : ∀(τ₁ τ₂: Ty), Function.Injective (@f τ₁ τ₂) :=
    fun _ _ (a11, a12) (a21, a22) _ => by simp [f, *] at *; assumption
  have sur : ∀(τ₁ τ₂: Ty), Function.Surjective (@f τ₁ τ₂) :=
    fun _ _ (VPair a1 a2) => ⟨(a1, a2), by simp [f]⟩
  have bij : ∀(τ₁ τ₂: Ty), Function.Bijective (@f τ₁ τ₂) :=
    fun τ₁ τ₂ => ⟨inj τ₁ τ₂, sur τ₁ τ₂⟩
  match τ with
  | TBool =>
    ⟨⟨{VTrue, VFalse}, by simp⟩, fun x => by cases x <;> simp⟩
  | TPair τ₁ τ₂ =>
    have : Fintype (Value τ₁) := fintype τ₁
    have : Fintype (Value τ₂) := fintype τ₂
    Fintype.ofBijective f (bij τ₁ τ₂)

def lt : Value τ -> Value τ -> Bool
  | VFalse, VTrue => true
  | VPair a1 a2, VPair b1 b2 =>
      if lt a1 b1 then true
      else if a1 = b1 then lt a2 b2
      else false
  | _, _ => false

instance instLTValue : LT (Value τ) := ⟨fun a b => lt a b⟩
instance instLEValue : LE (Value τ) := ⟨fun a b => a < b ∨ a = b⟩

@[simp] theorem le_atom₀ :  VFalse ≤ VFalse := by unfold_projs; unfold lt; aesop
@[simp] theorem le_atom₁ :  VFalse ≤ VTrue  := by unfold_projs; unfold lt; aesop
@[simp] theorem le_atom₂ :  VTrue  ≤ VTrue  := by unfold_projs; unfold lt; aesop
@[simp] theorem le_atom₃ : ¬VTrue  ≤ VFalse := by unfold_projs; unfold lt; aesop
@[simp] theorem lt_atom₀ : ¬VFalse < VFalse := by unfold_projs; unfold lt; aesop
@[simp] theorem lt_atom₁ :  VFalse < VTrue  := by unfold_projs; unfold lt; aesop
@[simp] theorem lt_atom₂ : ¬VTrue  < VTrue  := by unfold_projs; unfold lt; aesop
@[simp] theorem lt_atom₃ : ¬VTrue  < VFalse := by unfold_projs; unfold lt; aesop
theorem lt_pair₀ : a1 < b1 -> VPair a1 a2 < VPair b1 b2 := by intro h; unfold_projs; unfold lt; aesop
theorem lt_pair₁ : a2 < b2 -> VPair x a2  < VPair x b2  := by intro h; unfold_projs; unfold lt; aesop
theorem le_pair₀ : a1 < b1 -> VPair a1 a2 ≤ VPair b1 b2 := by intro h; unfold_projs; unfold lt; aesop
theorem le_pair₁ : a2 < b2 -> VPair x a2  ≤ VPair x b2  := by intro h; unfold_projs; unfold lt; aesop
@[simp] theorem le_all₀ : (a: Value τ) ≤ a := by unfold_projs; unfold lt; aesop
theorem lt_pair_destr : VPair a1 a2 < VPair b1 b2 -> a1 < b1 ∨ a1 = b1 ∧ a2 < b2 := by intro h; unfold_projs at h; unfold lt at h; aesop
theorem le_if_lt : (a: Value τ) < b -> a ≤ b := by intro h; unfold_projs; aesop

theorem lt_asymm' : ∀a b, (a: Value τ) < b -> ¬b < a := by
  intro a b h1 h2;
  induction a with
  | VFalse => cases b <;> simp_all
  | VTrue => cases b <;> simp_all
  | VPair a1 a2 ih1 ih2 =>
    cases' b with _ _ b1 b2;
    have ih1 := ih1 b1
    have ih2 := ih2 b2
    (apply lt_pair_destr at h1; rcases h1 with (h1a|⟨h1b1,h1b2⟩)) <;>
    (apply lt_pair_destr at h2; rcases h2 with (h2a|⟨h2b1,h2b2⟩))
    . simp_all
    . simp_all
    . rw [h1b1] at h2a ih1; simp_all
    . exact ih2 h1b2 h2b2;

instance instIsTransLT : IsTrans (Value τ) (· < ·) := ⟨by
  intro a b c ab bc;
  induction a with
  | VFalse => cases b <;> cases c <;> simp_all
  | VTrue => cases b <;> cases c <;> simp_all
  | VPair a1 a2 ih1 ih2 =>
    cases' b with _ _ b1 b2; cases' c with _ _ c1 c2
    have ih1 := ih1 b1 c1
    have ih2 := ih2 b2 c2
    (apply lt_pair_destr at ab; rcases ab with (ab1|ab2)) <;>
    (apply lt_pair_destr at bc; rcases bc with (bc1|bc1)) <;>
    (simp_all [lt_pair₀, lt_pair₁])⟩

instance : IsTotal (Value τ) (· ≤ ·) := ⟨by
  intro a b;
  induction a with
  | VFalse =>
    cases b <;> simp
  | VTrue =>
    cases b <;> simp
  | VPair a1 a2 ih1 ih2 =>
    cases' b with _ _ b1 b2
    unfold LE.le instLEValue at ih1 ih2; simp at ih1 ih2
    rcases ih1 b1 with ((ih1a|ih1b)|(ih1c|ih1d)) <;> (first
    | left; simp_all [le_pair₀, le_pair₁]; done
    | right; simp_all [le_pair₀, le_pair₁]; done
    | rcases ih2 b2 with ((ih2a|ih2b)|(ih2c|ih2d)) <;> (first
      | (left; simp_all [le_pair₀, le_pair₁]; done)
      | (right; simp_all [le_pair₀, le_pair₁]; done)))⟩

instance : Preorder (Value τ) :=
  { le_refl := by intro a; simp
  , le_trans := by
      intro a b c ab bc;
      unfold LE.le instLEValue at ab bc ⊢; simp at ab bc ⊢
      rcases ab with (ab1|ab2) <;> rcases bc with (bc1|bc2)
      . left; exact instIsTransLT.trans a b c ab1 bc1
      . rw [← bc2]; left; assumption
      . rw [ab2]; left; assumption
      . right; rw [ab2, bc2]
  , lt_iff_le_not_le := by
      intro a b; unfold_projs; apply Iff.intro <;> (intro h; simp_all); constructor
      have : ∀(x y: Value τ), lt x y = true ↔ x < y := by aesop
      rw [this a b] at h; clear this
      apply lt_asymm' at h; unfold_projs at h; simp_all
      intro h1; rw [h1] at h;
      have a_2 := lt_asymm' a a h; unfold_projs at a_2
      simp_all; aesop
  }
instance : Decidable (instLEValue.le a b) :=
  if h: lt a b ∨ a = b then isTrue (by aesop)
  else isFalse (by intro h; unfold_projs at h; aesop)
