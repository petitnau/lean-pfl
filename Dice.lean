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

open BigOperators

section Dice

------------
-- SYNTAX --
------------

inductive Var : List α -> α -> Type
  | ZVar : Var (a::as) a
  | SVar : Var bs a -> Var (b::bs) a
deriving DecidableEq, BEq, Ord, Repr open Var

inductive Ty where
  | TBool : Ty
  | TPair : Ty -> Ty -> Ty
deriving DecidableEq, BEq, Ord, Repr open Ty
infix:67 " :×: " => TPair

inductive Value : Ty -> Type where
  | VTrue : Value TBool
  | VFalse : Value TBool
  | VPair : Value τ₁ -> Value τ₂ -> Value (τ₁ :×: τ₂)
deriving DecidableEq, BEq,  Repr open Value

inductive AExpr : List Ty -> Ty -> Type where
  | AVar : Var δ τ -> AExpr δ τ
  | AValue : Value τ -> AExpr δ τ
deriving DecidableEq, BEq, Repr open AExpr

inductive Expr : List Ty -> Ty -> Type where
  | Atomic : AExpr δ τ -> Expr δ τ
  | Fst : AExpr δ (τ₁ :×: τ₂) -> Expr δ τ₁
  | Snd : AExpr δ (τ₁ :×: τ₂) -> Expr δ τ₂
  | Pair : AExpr δ τ₁ -> AExpr δ τ₂ -> Expr δ (τ₁ :×: τ₂)
  | Let : Expr δ τ₁ -> Expr (τ₁::δ) τ₂ -> Expr δ τ₂
  | Flip : Rat -> Expr δ TBool
  | Ifte : AExpr δ TBool -> Expr δ τ -> Expr δ τ -> Expr δ τ
  | Observe : AExpr δ TBool -> Expr δ TBool
deriving DecidableEq, Repr open Expr

-------------------
-- DISTRIBUTIONS --
-------------------

def Distribution (τ: Ty): Type := Value τ -> Rat

---------------------------------------
-- ENVIRONMENTS, SUBSTITUTIONS, ETC. --
---------------------------------------

def Env: Type := List Ty
def Inst (δ δ': Env) := ∀τ, Var δ τ → AExpr δ' τ
def Ren  (δ δ': Env) := ∀τ, Var δ τ → Var δ' τ

def ren_inst (τ: Ty) (r: Ren δ δ'): Ren (τ::δ) (τ::δ') := λ τ' => λ
  | ZVar => ZVar
  | SVar v' => SVar (r _ v')

def ren_aexpr (r: Ren δ δ') : AExpr δ τ → AExpr δ' τ
  | AVar v => AVar (r _ v)
  | AValue v => AValue v

def ren_expr (r: Ren δ δ') : Expr δ τ → Expr δ' τ
  | Atomic a => Atomic (ren_aexpr r a)
  | Fst a => Fst (ren_aexpr r a)
  | Snd a => Snd (ren_aexpr r a)
  | Pair a1 a2 => Pair (ren_aexpr r a1) (ren_aexpr r a2)
  | Let e1 e2 => Let (ren_expr r e1) (ren_expr (ren_inst _ r) e2)
  | Flip p => Flip p
  | Ifte a1 e1 e2 => Ifte (ren_aexpr r a1) (ren_expr r e1) (ren_expr r e2)
  | Observe a => Observe (ren_aexpr r a)

def shift_expr (δ: Env) (τ τ': Ty): AExpr δ τ -> AExpr (τ'::δ) τ :=
  ren_aexpr (fun _ v => SVar v)

def shift_inst (τ: Ty) (s: Inst δ δ'): Inst (τ::δ) (τ::δ') := λ τ' => λ
  | ZVar => AVar ZVar
  | SVar v' => shift_expr _ _ _  (s _ v')

def inst_aexpr (s: Inst δ δ') : AExpr δ τ → AExpr δ' τ
  | AVar v => s _ v
  | AValue v => AValue v

def inst_expr (s: Inst δ δ') : Expr δ τ → Expr δ' τ
  | Atomic a => Atomic (inst_aexpr s a)
  | Fst a => Fst (inst_aexpr s a)
  | Snd a => Snd (inst_aexpr s a)
  | Pair a1 a2 => Pair (inst_aexpr s a1) (inst_aexpr s a2)
  | Let e1 e2 => Let (inst_expr s e1) (inst_expr (shift_inst _ s) e2)
  | Flip p => Flip p
  | Ifte a1 e1 e2 => Ifte (inst_aexpr s a1) (inst_expr s e1) (inst_expr s e2)
  | Observe a => Observe (inst_aexpr s a)

def id_inst : Inst δ δ := fun _ => AVar

def cons_inst (e: AExpr δ' τ) (s: Inst δ δ'): Inst (τ::δ) δ' :=
  fun τ' (v: Var (τ::δ) τ') =>
    match v with
    | ZVar => e
    | SVar v' => s _ v'

local notation:max e " [↦ " v " ] " => (inst_expr (cons_inst (AValue v) id_inst) e)

-----------------
-- TERMINATION --
-----------------

def size { τ: Ty}: Expr δ τ -> ℕ
  | Fst _ => 1
  | Snd _ => 1
  | Flip _ => 1
  | Atomic _ => 1
  | Pair _ _ => 1
  | Observe _ => 1
  | Let e1 e2 => 1 + size e1 + size e2
  | Ifte _ e1 e2 => 1 + size e1 + size e2

@[simp] theorem inst_expr_size_unchanged (s: Inst δ δ1') : size (inst_expr s e) = size e := by
  induction' e generalizing δ1'
  repeat (unfold size inst_expr inst_aexpr; simp)

  case Let _ δ1 t1 t2 e1 e2 H1 H2 =>
    unfold size inst_expr; simp [*];

  case Ifte _ δ1 t1 t2 e1 e2 H1 H2 =>
    unfold size inst_expr; simp [*];

  repeat (unfold size inst_expr inst_aexpr)
  unfold size inst_expr; simp
  unfold size inst_expr; simp

--------------------------
-- FINITENESS OF VALUES --
--------------------------

def f (v: Value τ₁ × Value τ₂): (Value (τ₁ :×: τ₂))  :=
  match v with
  | (v1, v2) => VPair v1 v2
instance inj {τ₁ τ₂: Ty} : Function.Injective (@f τ₁ τ₂) := by
  intro a1 a2 h
  cases a1; cases a2
  simp [f, *] at *
  assumption
instance sur {τ₁ τ₂: Ty} : Function.Surjective (@f τ₁ τ₂) := by
  intro a
  cases a with
  | VPair a1 a2 => exact ⟨(a1, a2), by simp [f]⟩
instance bij {τ₁ τ₂: Ty} : Function.Bijective (@f τ₁ τ₂) :=
  ⟨inj, sur⟩
instance fintype (τ: Ty) : Fintype (Value τ) :=
  match τ with
  | TBool => ⟨⟨{VTrue, VFalse}, by simp⟩, fun x => by cases x <;> simp⟩
  | TPair τ₁ τ₂ =>
    have f1 : Fintype (Value τ₁) := fintype τ₁
    have f2 : Fintype (Value τ₂) := fintype τ₂
    (@Fintype.ofBijective _ _ _ f bij)

---------------
-- SEMANTICS --
---------------

set_option hygiene false
local notation:max " 〚 " v " 〛ᵥ " => semValue v
def semValue (v1: Value τ): Distribution τ :=
  fun v => if v == v1 then 1 else 0

local notation:max " 〚 " e " 〛ₐ " => semAExpr e
def semAExpr : AExpr [] τ -> Distribution τ
  | AValue v1 => semValue v1

local notation:max " 〚 " e " 〛 " => semExpr e
local notation:max " 〚 " e " 〛( " v " ) " => semExpr e v
def semExpr : Expr [] τ -> Distribution τ
  | Atomic (AValue v1) =>
    〚v1〛ᵥ

  | Fst (AValue $ VPair v1 _) =>
    〚v1〛ᵥ

  | Snd (AValue $ VPair _ v2) =>
    〚v2〛ᵥ

  | Pair (AValue v1) (AValue v2) =>
    〚VPair v1 v2〛ᵥ

  | Flip θ => λ
    | VTrue  => θ
    | VFalse => 1 - θ

  | Observe (AValue v1) => λ
    | VTrue  => if v1 == VTrue then 1 else 0
    | VFalse => 0

  | Ifte (AValue vg) e1 e2 =>
    match vg with
    | VTrue => 〚e1〛
    | VFalse => 〚e2〛

  | Let e1 e2  => λv =>
    ∑ v', 〚e1〛(v') * 〚e2[↦ v']〛(v)

termination_by e => size e
decreasing_by all_goals (simp_wf; (conv => rhs; unfold size); linarith)

def toFinset (f: Distribution τ): Finset (Value τ × Rat) :=
  Finset.univ.image (fun x => (x, f x))

def normFact (f: Distribution τ): Rat :=
  ∑ x in (toFinset f), x.snd

def normalize (f: Distribution τ): Distribution τ :=
  fun x => (f x)/(normFact f)

end Dice
