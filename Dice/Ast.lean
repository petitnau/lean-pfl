import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Lean.Meta.AppBuilder
import Lean.Expr
import AssertCmd
import Data.HList
import Data.List

open BigOperators

inductive Ty where
  | TBool : Ty
  | TPair : Ty -> Ty -> Ty
deriving DecidableEq, BEq, Ord, Repr open Ty
notation "𝔹" => TBool
infix:67 " :×: " => TPair

inductive Value : Ty -> Type where
  | VTrue  : Value 𝔹
  | VFalse : Value 𝔹
  | VPair  : Value τ₁ -> Value τ₂ -> Value (τ₁ :×: τ₂)
deriving DecidableEq, BEq,  Repr open Value

inductive AExpr : List Ty -> Ty -> Type where
  | AVar   : Member δ τ -> AExpr δ τ
  | AValue : Value τ -> AExpr δ τ
deriving DecidableEq, BEq, Repr open AExpr

inductive Expr : List (List Ty × Ty) -> List Ty -> Ty -> Type where
  | Atomic  : AExpr δ τ           -> Expr T δ τ
  | Fst     : AExpr δ (τ₁ :×: τ₂) -> Expr T δ τ₁
  | Snd     : AExpr δ (τ₁ :×: τ₂) -> Expr T δ τ₂
  | Flip    : ℚ                   -> Expr T δ 𝔹
  | Observe : AExpr δ 𝔹           -> Expr T δ 𝔹
  | Pair    : AExpr δ τ₁          -> AExpr δ τ₂         -> Expr T δ (τ₁ :×: τ₂)
  | Let     : Expr T δ τ₁         -> Expr T (τ₁::δ) τ₂  -> Expr T δ τ₂
  | Call    : Member T (π, τ)     -> HList (AExpr δ) π  -> Expr T δ τ
  | Ifte    : AExpr δ 𝔹           -> Expr T δ τ         -> Expr T δ τ           -> Expr T δ τ
open Expr

inductive Function : List (List Ty × Ty) -> List Ty -> Ty -> Type where
  | Function : Expr T [] τ -> Function T π τ
open Function

inductive Program : List (List Ty × Ty) -> Ty -> Type where
  | Func       : Function T π τ -> Program ((π,τ)::T) τ -> Program T τ
  | Expression : Expr T [] τ    -> Program T τ
open Program

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
