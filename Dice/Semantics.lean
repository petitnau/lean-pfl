import Mathlib.Order.Hom.Basic
import Data.Probability
import Data.KFinset
import Data.Table
import Math.DomainTheory
import Dice.Ast
import Data.HList
import Dice.Termination
import Dice.Instantiation
import Math.DomainTheory
import Mathlib.Algebra.Order.Pointwise
import Mathlib.Order.CompleteLattice

open Value AExpr Expr Program
open BigOperators

------------------------------
-- SEMANTICS OF EXPRESSIONS --
------------------------------
section
set_option hygiene false
local notation:max " ⟦ " v " ⟧ᵥ " => semValue v
def semValue (v1: Value τ): 𝔻(τ) :=
  fun v => if v == v1 then 1 else 0
end
notation:max "⟦" v "⟧ᵥ" => semValue v

section
set_option hygiene false
local notation:max T "⟦" e "⟧ " => semExpr T e
local notation:max T "⟦" e "⟧(" v ") " => semExpr T e v
def semExpr (T: Table ρ) : Expr ρ [] τ -> 𝔻(τ)
  | Atomic (AValue v1) =>
    ⟦v1⟧ᵥ

  | Fst (AValue $ VPair v1 _) =>
    ⟦v1⟧ᵥ

  | Snd (AValue $ VPair _ v2) =>
    ⟦v2⟧ᵥ

  | Pair (AValue v1) (AValue v2) =>
    ⟦VPair v1 v2⟧ᵥ

  | Flip θ => λ
    | VTrue  => θ.prob
    | VFalse => θ.invProb

  | Observe (AValue v1) => λ
    | VTrue  => ⟦v1⟧ᵥ <| VTrue
    | VFalse => 0

  | Ifte (AValue vg) e1 e2 =>
    match vg with
    | VTrue => T⟦e1⟧
    | VFalse => T⟦e2⟧

  | Let e1 e2  =>
    (∑ v', (T⟦e1⟧(v')) * (T⟦e2[↦ v'::ᵢ[]ᵢ]⟧))

  | Call f as =>
    (T.get f) (as.map AExpr.value)

  termination_by e => size e
  decreasing_by all_goals (simp_wf; (conv => rhs; unfold size); linarith)
end
notation:max T "⟦" e "⟧(" v ")" => semExpr T e v
notation:max T "⟦" e "⟧" => semExpr T e

@[simp] theorem semExpr_atomic : T⟦Atomic (AValue v1)⟧ = ⟦v1⟧ᵥ := by unfold semExpr; rfl
@[simp] theorem semExpr_fst : T⟦Fst (AValue (VPair v1 v2))⟧ = ⟦v1⟧ᵥ := by unfold semExpr; rfl
@[simp] theorem semExpr_snd : T⟦Snd (AValue (VPair v1 v2))⟧ = ⟦v2⟧ᵥ := by unfold semExpr; rfl
@[simp] theorem semExpr_pair : T⟦Pair (AValue v1) (AValue v2)⟧ = ⟦VPair v1 v2⟧ᵥ := by unfold semExpr; rfl
@[simp] theorem semExpr_flip : T⟦Flip θ⟧ = λ | VTrue => θ.prob | VFalse => θ.invProb := by unfold semExpr; rfl
@[simp] theorem semExpr_observe : T⟦Observe (AValue v1)⟧ = λ | VTrue => ⟦v1⟧ᵥ <| VTrue | VFalse => 0 := by unfold semExpr; rfl
@[simp] theorem semExpr_ifte_true : T⟦Ifte (AValue VTrue) e1 e2⟧ = T⟦e1⟧ := by conv => lhs; unfold semExpr
@[simp] theorem semExpr_ifte_false : T⟦Ifte (AValue VFalse) e1 e2⟧ = T⟦e2⟧ := by conv => lhs; unfold semExpr
@[simp] theorem semExpr_let : T⟦Let e1 e2⟧ = (∑ v', (T⟦e1⟧(v')) * (T⟦e2[↦ v'::ᵢ[]ᵢ]⟧)) := by conv => lhs; unfold semExpr
@[simp] theorem semExpr_call : T⟦Call f as⟧ = (T.get f) (as.map AExpr.value) := by unfold semExpr; rfl

-- @[simp] theorem semProgramC'_simp : semProgramC' I e = semProgramC I []ₕ e := by aesop
-- @[simp] theorem semProgramC_expr : semProgramC I T (PExpr e) = T⟦e⟧ := by unfold semProgramC; rfl
-- @[simp] theorem semProgramC_func : semProgramC (Table.cons i is) T (PFunc e p) = semProgramC is (Table.cons i T) p := by aesop

def functionCharacteristic
  (f: Func ρ π τ) (T: Table ρ)
  : (Value[π]ₕ → 𝔻(τ)) -> (Value[π]ₕ → 𝔻(τ))
  := fun I vs => (@HList.cons _ _ (π,τ) ρ I T)⟦f[↦ inst'' vs]⟧
notation "Φ[" T "," f "](" I ")" => functionCharacteristic f T I
notation "Φ[" T "," f "]" => functionCharacteristic f T

------------------------------------------
-- MONOTONICITY OF EXPRESSION SEMANTICS --
------------------------------------------

theorem semExpr_monotone_table
  (e: Expr ρ π τ) (S: Inst π [])
  : Monotone (fun T => semExpr T (e[↦ S]))
  := by
    induction e with
    | Atomic a1 => intro T1 T2 _; simp_all
    | Fst a1 => intro T1 T2 _; simp_all; cases (inst_aexpr_value S a1); simp_all;
    | Snd a1 => intro T1 T2 _; simp_all; cases (inst_aexpr_value S a1); simp_all;
    | Flip => intro T1 T2 _; simp_all
    | Observe a1 => intro T1 T2 _; simp_all
    | Pair a1 a2 => intro T1 T2 _; simp_all
    | Let e1 e2 ih1 ih2 =>
      intro T1 T2 hT v; simp_all; apply Finset.sum_le_sum
      intro i _; apply Probability.mul_le_mul' _ _ <;>
      simp_all [ih1 S hT i, ih2 (cons_inst (AValue i) S) hT v]
    | Call f as =>
      intro T1 T2 hT v; simp_all
      induction f
      . cases T1; cases T2; rw [Table.le_cons_ext] at hT; apply hT.left
      . cases T1; cases T2; rw [Table.le_cons_ext] at hT; simp_all
    | Ifte a1 e1 e2 ih1 ih2 =>
      intro T1 T2 hT v; simp_all; cases (inst_aexpr_value S a1) <;> aesop

theorem semExpr_monotone_invariant
  (e: Expr ((π,τ)::ρ) π' τ') (T: Table ρ) (S: Inst π' [])
  : Monotone (fun I => (I ::ₕ T)⟦e[↦ S]⟧)
  := by
    intro I1 I2 hI;
    have TH : HList.cons' (π,τ) I1 T ≤ HList.cons' (π,τ) I2 T := by
      unfold_projs; unfold Table.le; simp_all
    intro v; have := semExpr_monotone_table e S TH v
    aesop

theorem functionCharacteristic_monotone
  {π: [Ty]'} {τ: Ty} {ρ: [Sig]'} (f: Func ρ π τ) (T: Table ρ)
  : Monotone (Φ[T,f](·))
  := by
    intro I1 I2 hM
    unfold functionCharacteristic;
    intro i v;
    simp_all
    apply semExpr_monotone_invariant _ _ _ hM

theorem functionCharacteristic_monotone'
  {π: [Ty]'} {τ: Ty} {ρ: [Sig]'} (f: Func ρ π τ)
  : Monotone (Φ[·,f])
  := by
    intro I1 I2 hM
    unfold functionCharacteristic;
    intro i v;
    simp_all
    apply semExpr_monotone_table
    rw [Table.le_cons_ext]; simp_all

------

theorem semExpr_scott_table (e: Expr Γ π τ) (S: Inst π [])
  : ScottContinuous' (·⟦e[↦ S]⟧) := by
  intro T h cT
  induction e with
  | Atomic a => cases a <;> simp_all
  | Fst a => simp_all; cases (inst_aexpr_value S a); simp_all
  | Snd a => simp_all; cases (inst_aexpr_value S a); simp_all
  | Flip p => simp_all
  | Pair a1 a2 => simp_all
  | Observe a => simp_all
  | @Let Γ τ₁ τ₂ e1 e2 ih1 ih2 =>
    unfold inst_expr semExpr;
    simp_all; funext;
    let f := (λx t => t⟦e1[↦ S]⟧(x))
    let g := (λx t => t⟦e2[↦ x::ᵢS]⟧)
    let fg := (λx t => t⟦e1[↦ S]⟧(x) * t⟦e2[↦ x::ᵢS]⟧)
    have : ∀b x y, x ≤ y → fg b x ≤ fg b y := by
      intro b x y h1; apply SemiDistribution.pmul_le_pmul; repeat (apply semExpr_monotone_table; assumption)
    have := SemiDistribution.sSup_summation T (by aesop) cT (λx t => t⟦e1[↦ S]⟧(x) * t⟦e2[↦ x::ᵢS]⟧) this (Finset.univ : Finset (Value τ₁))
    unfold Set.image; simp_all; rw [← this]
    have ⟨t, th⟩ := h
    have t1: ∀x, {x_1 | ∃ x_2 ∈ T, x_2⟦e1[↦ S]⟧(x) * x_2⟦e2[↦ x::ᵢS]⟧ = x_1} = ((λy => f x y * g x y) '' T) := by aesop
    have : ∀x, (Monotone fun t => t⟦e1[↦ S]⟧(x)) := by intro x a b ab; simp_all; apply Pi.le_def.mp ?_ x; apply semExpr_monotone_table; assumption
    have t2 := fun x => SemiDistribution.sSup_cmul'' T h cT (f x) (this x) (g x) (by simp_all; apply semExpr_monotone_table)
    have t3: ∀y, {x_1 | ∃ t ∈ T, t⟦e1[↦ S]⟧(y) = x_1} = (f y '' T) := by aesop
    have t4: ∀y, {x | ∃ t ∈ T, t⟦e2[↦ y::ᵢS]⟧ = x} = (g y '' T) := by aesop
    conv in (∑ b : Value τ₁, sSup {x | ∃ x_1 ∈ T, x_1⟦e1[↦ S]⟧(b) * x_1⟦e2[↦ b::ᵢS]⟧ = x}) =>
      enter [2,x]; rw [t1 x, t2 x]
    conv_rhs =>
      enter [2,x]; rw [← ih1 S, ← ih2 (x::ᵢS), sSup_apply'];
    simp_all
  | Call f as =>
    unfold semExpr inst_expr;
    simp_all
    rw [← Table.sSup_apply, sSup_apply'];
    simp_all
    aesop; aesop
  | Ifte a e1 e2 =>
    simp_all; cases (inst_aexpr_value S a) <;> simp_all

theorem semExpr_coscott_table (e: Expr Γ π τ) (S: Inst π [])
  : CoScottContinuous' (·⟦e[↦ S]⟧) := by
  intro T h cT
  induction e with
  | Atomic a => cases a <;> simp_all
  | Fst a => simp_all; cases (inst_aexpr_value S a); simp_all
  | Snd a => simp_all; cases (inst_aexpr_value S a); simp_all
  | Flip p => simp_all
  | Pair a1 a2 => simp_all
  | Observe a => simp_all
  | @Let Γ τ₁ τ₂ e1 e2 ih1 ih2 =>
    unfold inst_expr semExpr;
    simp_all; funext;
    let f := (λx t => t⟦e1[↦ S]⟧(x))
    let g := (λx t => t⟦e2[↦ x::ᵢS]⟧)
    let fg := (λx t => t⟦e1[↦ S]⟧(x) * t⟦e2[↦ x::ᵢS]⟧)
    have : ∀b x y, x ≤ y → fg b x ≤ fg b y := by
      intro b x y h1; apply SemiDistribution.pmul_le_pmul; repeat (apply semExpr_monotone_table; assumption)
    have := SemiDistribution.sInf_summation T (by aesop) cT (λx t => t⟦e1[↦ S]⟧(x) * t⟦e2[↦ x::ᵢS]⟧) this (Finset.univ : Finset (Value τ₁))
    unfold Set.image; simp_all; rw [← this]
    have ⟨t, th⟩ := h
    have t1: ∀x, {x_1 | ∃ x_2 ∈ T, x_2⟦e1[↦ S]⟧(x) * x_2⟦e2[↦ x::ᵢS]⟧ = x_1} = ((λy => f x y * g x y) '' T) := by aesop
    have : ∀x, (Monotone fun t => t⟦e1[↦ S]⟧(x)) := by intro x a b ab; simp_all; apply Pi.le_def.mp ?_ x; apply semExpr_monotone_table; assumption
    have t2 := fun x => SemiDistribution.sInf_cmul'' T h cT (f x) (this x) (g x) (by simp_all; apply semExpr_monotone_table)
    have t3: ∀y, {x_1 | ∃ t ∈ T, t⟦e1[↦ S]⟧(y) = x_1} = (f y '' T) := by aesop
    have t4: ∀y, {x | ∃ t ∈ T, t⟦e2[↦ y::ᵢS]⟧ = x} = (g y '' T) := by aesop
    conv in (∑ b : Value τ₁, sInf {x | ∃ x_1 ∈ T, x_1⟦e1[↦ S]⟧(b) * x_1⟦e2[↦ b::ᵢS]⟧ = x}) =>
      enter [2,x]; rw [t1 x, t2 x]
    conv_rhs =>
      enter [2,x]; rw [← ih1 S, ← ih2 (x::ᵢS), sInf_apply']
    simp_all
  | Call f as =>
    unfold semExpr inst_expr;
    simp_all
    rw [← Table.sInf_apply, sInf_apply'];
    simp_all
    aesop; aesop
  | Ifte a e1 e2 =>
    simp_all; cases (inst_aexpr_value S a) <;> simp_all

theorem semExpr_monotone_invariant'
  (e: Expr ((π,τ)::ρ) π' τ') (T: Table ρ) (S: Inst π' [])
  : Monotone (fun I => (I ::ₕ T)⟦e[↦ S]⟧)
  := by
    intro I1 I2 hI;
    let T1 := @HList.cons _ _ (π,τ) ρ I1 T
    let T2 := @HList.cons _ _ (π,τ) ρ I2 T
    have TH : T1 ≤ T2 := by
      unfold_projs; unfold Table.le; cases T1; cases T2;
      simp_all
    intro v; have := semExpr_monotone_table e S TH v
    simp_all

theorem functionCharacteristic_scott
  {π: [Ty]'} {τ: Ty} {ρ: [Sig]'} (f: Func ρ π τ) (T: Table ρ)
  : ScottContinuous' Φ[T,f]
  := by
    intro I h cI
    have ⟨i, ih⟩ := h
    unfold functionCharacteristic;
    let IT := {@HList.cons _ _ (π,τ) ρ i T | i ∈ I}
    have : {HList.head it | it ∈ IT} = I := by aesop
    have : {HList.tail it | it ∈ IT} = {T} := by unfold HList.tail; aesop
    have : sSup {T} = T := by aesop
    have : ((fun I vs => (I :: T)⟦f[↦ inst'' vs]⟧) '' I) = {λ vs => t⟦f[↦ inst'' vs]⟧ | t ∈ IT} := by aesop
    rw [this]
    have : IsChain (· ≤ ·) IT := by
      intro a aA b bB aneb; simp_all; cases a; cases b; simp_all; aesop
    have : IT.Nonempty := by existsi (HList.cons' (π,τ) i T); simp_all; existsi i; aesop
    have x := fun vs => (semExpr_scott_table f (inst'' vs) this (by aesop)).symm
    simp_all
    have : @HList.cons _ _ (π,τ) ρ (sSup I) T = sSup IT := by rw [Table.sSup_cons_ext IT]; aesop
    rw [this]; clear this
    conv_rhs => ext vs; rw [x vs]
    funext a;
    rw [sSup_apply'];
    simp_all
    have : {x | ∃t ∈ IT, (fun vs => t⟦f[↦ inst'' vs]⟧) a = x } = {t⟦f[↦ inst'' a]⟧ | t ∈ IT} := by
      ext val; simp_all
    unfold Set.image; simp_all;

theorem functionCharacteristic_coscott
  {π: [Ty]'} {τ: Ty} {ρ: [Sig]'} (f: Func ρ π τ) (T: Table ρ)
  : CoScottContinuous' Φ[T,f]
  := by
    intro I h cI
    have ⟨i, ih⟩ := h
    unfold functionCharacteristic;
    let IT := {@HList.cons _ _ (π,τ) ρ i T | i ∈ I}
    have : {HList.head it | it ∈ IT} = I := by aesop
    have : {HList.tail it | it ∈ IT} = {T} := by unfold HList.tail; aesop
    have : sInf {T} = T := by aesop
    have : ((fun I vs => (I :: T)⟦f[↦ inst'' vs]⟧) '' I) = {λ vs => t⟦f[↦ inst'' vs]⟧ | t ∈ IT} := by aesop
    rw [this]
    have : IsChain (· ≤ ·) IT := by
      intro a aA b bB aneb; simp_all; cases a; cases b; simp_all; aesop
    have : IT.Nonempty := by existsi (HList.cons' (π,τ) i T); simp_all; existsi i; aesop
    have x := fun vs => (semExpr_coscott_table f (inst'' vs) this (by aesop)).symm
    simp_all
    have : @HList.cons _ _ (π,τ) ρ (sInf I) T = sInf IT := by rw [Table.sInf_cons_ext IT]; aesop
    rw [this]; clear this
    conv_rhs => ext vs; rw [x vs]
    funext a;
    rw [sInf_apply'];
    simp_all
    have : {x | ∃t ∈ IT, (fun vs => t⟦f[↦ inst'' vs]⟧) a = x } = {t⟦f[↦ inst'' a]⟧ | t ∈ IT} := by
      ext val; simp_all
    unfold Set.image; simp_all;

------

noncomputable def semFunc
  {π: List Ty} {τ: Ty} {ρ: [Sig]'}
  (T: Table ρ) (f: Func ρ π τ)
  : (Value[π]ₕ -> 𝔻(τ))
  := OrderHom.lfp ⟨Φ[T,f], functionCharacteristic_monotone f T⟩

noncomputable def semProgram {ρ': [Sig]'} (T: Table ρ): Program τ ρ ρ' -> 𝔻(τ)
  | PExpr e => semExpr T e
  | PFunc f e =>
      let T' := HList.cons (semFunc T f) T
      semProgram T' e

noncomputable def semProgram' : Program τ [] ρ -> 𝔻(τ) :=
  semProgram HList.nil

theorem semFunc_monotone_table
  : Monotone (fun T => semFunc T f)
  := by
    intro t1 t2 h
    simp_all; unfold semFunc; rw [← lowerb, ← lowerb]
    apply sSup_le; intro b bB; simp_all
    have ⟨bB1, bB2⟩ := bB
    rw [← bB2]; clear bB2
    have : (Φ[t2,f]^[bB1] ⊥) ∈ {x | ∃ n, Φ[t2,f]^[n] ⊥ = x} := by aesop
    apply le_sSup_of_le this
    induction' bB1 with n ih
    . simp_all
    . simp_all [Function.iterate_succ_apply'];
      calc
        Φ[t1,f](Φ[t1,f]^[n] ⊥)
        _ ≤ Φ[t2,f](Φ[t1,f]^[n] ⊥) := (functionCharacteristic_monotone' f h) (Φ[t1,f]^[n] ⊥)
        _ ≤ Φ[t2,f](Φ[t2,f]^[n] ⊥) := (functionCharacteristic_monotone f t2 ih)
    exact functionCharacteristic_scott f t2
    exact functionCharacteristic_scott f t1

theorem semProgram_monotone_table
  : Monotone (fun T => semProgram T p)
  := by
    induction p with
    | @PFunc _ π' τ' _ f p ih =>
      unfold semProgram; simp_all;
      intro t1 t2 tlet; simp_all
      let t1' := (HList.cons' (π',τ') (semFunc t1 f) t1)
      let t2' := (HList.cons' (π',τ') (semFunc t2 f) t2)
      have := @ih t1' t2'
      simp at this
      have : t1' ≤ t2' := by rw [Table.le_cons_ext]; simp_all; apply semFunc_monotone_table tlet
      have := ih this
      simp_all
    | PExpr e =>
      have : e = e[↦ id_inst] := by simp
      rw [this]
      unfold semProgram; exact semExpr_monotone_table e id_inst

--------------------------
-- COMPUTABLE EXTENSION --
--------------------------

def semProgramC (I: Table ρ') (T: Table ρ) : Program τ ρ ρ' -> 𝔻(τ)
  | PExpr e => T⟦e⟧
  | PFunc _ p =>
    match I with
    | @HList.cons _ _ (π,τ) _ i is =>
      let T': Table ((π,τ)::ρ) := i ::ₕ T
      semProgramC is T' p

def semProgramC' (I: Table ρ) : Program τ [] ρ -> 𝔻(τ) :=
  semProgramC I []ₕ

def toFinset (f: 𝔻(τ)): KFinset (Value τ) ℝ :=
  ⟨Finset.univ, fun v => (f v : ℝ)⟩

def normFact (f: 𝔻(τ)): DReal :=
  ∑ x in Finset.univ, (f x).val

def normProb (f: 𝔻(τ)): 𝔻(τ) :=
  fun x => (f x).divD (normFact f)

def SuperInvariant (I: Value[π]ₕ → 𝔻(τ)) (T: Table ρ) (f: Func ρ π τ)
  : Prop := functionCharacteristic f T I ≤ I

def LowerBound (I: Value[π]ₕ → 𝔻(τ)) (T: Table ρ) (f: Func ρ π τ)
  : Prop := I ≤ semFunc T f

def UpperBound (I: Value[π]ₕ → 𝔻(τ)) (T: Table ρ) (f: Func ρ π τ)
  : Prop := semFunc T f ≤ I

inductive FLInvariant {τ: Ty} : Program τ ρ ρ' -> Table ρ -> Table ρ' -> Type where
  | nil    : FLInvariant (PExpr e) T []
  | cons f : FLInvariant p (i ::ₕ T) I -> LowerBound i T f
          -> FLInvariant (PFunc f (cast (by simp only [Prod.mk.eta]) p)) T (i ::ₕ I)

inductive FUInvariant {τ: Ty} : Program τ ρ ρ' -> Table ρ -> Table ρ' -> Type where
  | nil    : FUInvariant (PExpr e) T []
  | cons f : FUInvariant p (i ::ₕ T) I -> UpperBound i T f
          -> FUInvariant (PFunc f (cast (by simp only [Prod.mk.eta]) p)) T (i ::ₕ I)

theorem semFunc_supI : Φ[T,f](I) ≤ I -> semFunc T f ≤ I := by
  intro h; apply OrderHom.lfp_le; simp_all

@[simp]
theorem semExpr_cast {h1: a = b} {h2: Expr a [] τ = Expr b [] τ} : semExpr (HList.cast T h1) (cast h2 e) = semExpr T e
  := by aesop

theorem semProgram_supB
  {I: Table ρ'} {TC: Table ρ} {TN: Table ρ} {p: Program τ ρ ρ'}
  : FUInvariant p TC I -> TN ≤ TC -> semProgram TN p ≤ semProgramC I TC p := by
    induction p with
    | PExpr e =>
      intro _ h2;
      unfold semProgram semProgramC;
      rw [Pi.le_def]; intro v; rw [Probability.le_ext, DReal.le_ext]
      have := semExpr_monotone_table e id_inst h2 v
      simp at this; assumption
    | PFunc f p' ih =>
      rename_i ρ π τ ρ'
      intro h1 h2;
      have : semProgram TN (PFunc f p') = semProgram (HList.cons' (π,τ) (semFunc TN f) TN) p' := by
        (conv_lhs => unfold semProgram)
      cases' I with _ _ i is
      calc
        semProgram TN (PFunc f p')
        _ = semProgram (HList.cons' (π,τ) (semFunc TN f) TN) p' := by conv_lhs => unfold semProgram
        _ ≤ semProgram (HList.cons' (π,τ) i TN) p' := by
            cases' h1 with _ _ _ πτ E F p' i _ _ f' FUI UB
            unfold UpperBound at UB; simp_all;
            apply semProgram_monotone_table; rw [Table.le_cons_ext]
            have : semFunc TN f' ≤ semFunc TC f' := semFunc_monotone_table h2
            simp_all; exact le_trans this UB
        _ ≤ semProgramC is (HList.cons' (π,τ) i TC) p' := by
            cases' h1 with _ _ _ πτ E F p' i _ _ f' FUI UB
            apply ih;
            . simp_all; exact FUI;
            . rw [Table.le_cons_ext]; simp_all;
        _ = semProgramC (HList.cons' (π,τ) i is) TC (PFunc f p') := by
            conv_rhs => unfold semProgramC

theorem semProgram_lowB
  {I: Table ρ'} {TC: Table ρ} {TN: Table ρ} {p: Program τ ρ ρ'}
  : FLInvariant p TC I -> TC ≤ TN -> semProgramC I TC p ≤ semProgram TN p := by
    induction p with
    | PExpr e =>
      intro _ h2;
      unfold semProgram semProgramC;
      rw [Pi.le_def]; intro v; rw [Probability.le_ext, DReal.le_ext]
      have := semExpr_monotone_table e id_inst h2 v
      simp at this; assumption
    | PFunc f p' ih =>
      rename_i ρ π τ ρ'
      intro h1 h2;
      have : semProgram TN (PFunc f p') = semProgram (HList.cons' (π,τ) (semFunc TN f) TN) p' := by
        (conv_lhs => unfold semProgram)
      cases' I with _ _ i is
      calc
        semProgramC (HList.cons' (π,τ) i is) TC (PFunc f p')
        _ = semProgramC is (HList.cons' (π,τ) i TC) p' := by
            conv_lhs => unfold semProgramC;
        _ ≤ semProgram (HList.cons' (π,τ) i TN) p' := by
            cases' h1 with _ _ _ πτ E F p' i _ _ f' FUI LB
            apply ih;
            . simp_all; exact FUI;
            . rw [Table.le_cons_ext]; simp_all;
        _ ≤ semProgram (HList.cons' (π,τ) (semFunc TN f) TN) p' := by
            cases' h1 with _ _ _ πτ E F p' i _ _ f' FUI LB
            unfold LowerBound at LB; simp_all;
            apply semProgram_monotone_table; rw [Table.le_cons_ext]
            have : semFunc TC f' ≤ semFunc TN f' := semFunc_monotone_table h2
            simp_all; exact le_trans LB this
        _ = semProgram TN (PFunc f p') := by conv_rhs => unfold semProgram

theorem semProgram_supB' {I: Table ρ'} {p: Program τ [] ρ'}
  : FUInvariant p [] I -> semProgram' p ≤ semProgramC' I p := by
    unfold semProgram' semProgramC';
    intro h; apply semProgram_supB; exact h; simp

theorem semProgram_lowB' {I: Table ρ'} {p: Program τ [] ρ'}
  : FLInvariant p [] I -> semProgramC' I p ≤ semProgram' p:= by
    unfold semProgram' semProgramC';
    intro h; apply semProgram_lowB; exact h; simp

theorem search_lowerbound (T: Table ρ) (f: Func ρ π τ): Φ[T,f]^[n] 0 ≤ semFunc T f := by
  let cfun : (Value[π]ₕ → 𝔻(τ)) →o (Value[π]ₕ → 𝔻(τ)) := ⟨Φ[T,f], functionCharacteristic_monotone f T⟩
  have : Φ[T,f] = cfun.toFun := by rfl
  rw [this]
  unfold semFunc;
  apply lowerb' cfun (functionCharacteristic_scott f T)

theorem search_upperbound (T: Table ρ) (f: Func ρ π τ): semFunc T f ≤ Φ[T,f]^[n] 1 := by
  let cfun : (Value[π]ₕ → 𝔻(τ)) →o (Value[π]ₕ → 𝔻(τ)) := ⟨Φ[T,f], functionCharacteristic_monotone f T⟩
  have : Φ[T,f] = cfun.toFun := by rfl
  rw [this]
  unfold semFunc;
  have : OrderHom.lfp cfun ≤ OrderHom.gfp cfun := by
    have := OrderHom.isGreatest_gfp cfun
    have := OrderHom.isLeast_lfp cfun
    unfold IsGreatest IsLeast at *
    aesop
  apply le_trans this
  apply upperb' cfun (functionCharacteristic_coscott f T)
