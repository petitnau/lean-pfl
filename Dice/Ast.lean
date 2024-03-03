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
import Data.Prob
import Data.FlipProb

open BigOperators Probability

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

instance instOrdValue : Ord (Value τ) :=
  ⟨match τ with
  | TBool => fun
    | VTrue,  VTrue  => Ordering.eq
    | VFalse, VFalse => Ordering.eq
    | VFalse, VTrue  => Ordering.lt
    | VTrue,  VFalse => Ordering.gt
  | TPair _ _ => fun
    | VPair a1 b1, VPair a2 b2 =>
      match instOrdValue.compare a1 a2 with
      | Ordering.eq => instOrdValue.compare b1 b2
      | x => x⟩

instance instInhabitedValue {τ: Ty}: Inhabited (Value τ) :=
  ⟨match τ with
  | TBool => VTrue
  | TPair τ1 τ2 => VPair (@instInhabitedValue τ1).default (@instInhabitedValue τ2).default⟩

inductive AExpr : List Ty -> Ty -> Type where
  | AVar   : Member τ δ -> AExpr δ τ
  | AValue : Value τ -> AExpr δ τ
deriving DecidableEq, BEq, Repr open AExpr

inductive Expr : List (List Ty × Ty) -> List Ty -> Ty -> Type where
  | Atomic  {ρ δ τ}     : AExpr δ τ           -> Expr ρ δ τ
  | Fst     {ρ δ τ₁ τ₂} : AExpr δ (τ₁ :×: τ₂) -> Expr ρ δ τ₁
  | Snd     {ρ δ τ₁ τ₂} : AExpr δ (τ₁ :×: τ₂) -> Expr ρ δ τ₂
  | Flip    {ρ δ}       : FlipProb            -> Expr ρ δ 𝔹
  | Observe {ρ δ}       : AExpr δ 𝔹           -> Expr ρ δ 𝔹
  | Pair    {ρ δ τ₁ τ₂} : AExpr δ τ₁          -> AExpr δ τ₂         -> Expr ρ δ (τ₁ :×: τ₂)
  | Let     {ρ δ τ₁ τ₂} : Expr ρ δ τ₁         -> Expr ρ (τ₁::δ) τ₂  -> Expr ρ δ τ₂
  | Call    {ρ δ τ π}   : Member (π, τ) ρ     -> HList (AExpr δ) π  -> Expr ρ δ τ
  | Ifte    {ρ δ τ}     : AExpr δ 𝔹           -> Expr ρ δ τ         -> Expr ρ δ τ           -> Expr ρ δ τ
open Expr

#check Expr.rec

abbrev Function (ρ: List (List Ty × Ty)) (π: List Ty) (τ: Ty): Type
  := Expr ρ π τ

inductive Program : List (List Ty × Ty) -> List (List Ty × Ty) -> Ty -> Type where
  | Func       : Function ((π,τ')::ρ) π τ' -> Program ((π,τ')::ρ) ρ' τ -> Program ρ ((π,τ')::ρ') τ
  | Expression : Expr ρ [] τ    -> Program ρ [] τ
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
