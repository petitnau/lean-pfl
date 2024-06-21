import Mathlib.Order.Hom.Basic
import Data.Probability
import Data.KFinset
import Data.Table
import Dice.Ast
import Dice.Termination
import Dice.Instantiation

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
    | Atomic a1 =>
      intro T1 T2 _
      have ⟨v', vh⟩ := inst_aexpr_full a1 S;
      unfold semExpr inst_expr; simp_all
    | Fst a1 =>
      intro T1 T2 _
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      unfold semExpr inst_expr; cases v1; simp_all
    | Snd a1 =>
      intro T1 T2 _
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      unfold semExpr inst_expr; cases v1; simp_all
    | Flip =>
      intro T1 T2 _
      unfold semExpr inst_expr; simp_all
    | Observe a1 =>
      intro T1 T2 _
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      unfold semExpr inst_expr; cases v1 <;> simp_all
    | Pair a1 a2 =>
      intro T1 T2 _
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      have ⟨v2, v2h⟩ := inst_aexpr_full a2 S;
      unfold semExpr inst_expr; cases v1 <;> cases v2 <;> simp_all
    | Let e1 e2 ih1 ih2 =>
      intro T1 T2 hT v
      unfold inst_expr semExpr; simp_all
      apply Finset.sum_le_sum;
      intro i _;
      replace ih1 := ih1 S hT i;
      replace ih2 := ih2 (cons_inst (AValue i) S) hT v
      apply Probability.mul_le_mul' _ _;
      simp_all; simp_all
    | Call f as =>
      intro T1 T2 hT v
      unfold semExpr inst_expr;
      induction f <;> simp_all; cases T1; cases T2; simp_all;
      unfold_projs at hT; unfold Table.le at hT;
      apply hT.left;
      rename_i aih; cases T1; cases T2; unfold_projs at hT;
      unfold Table.le at hT;
      replace aih := aih hT.right; unfold HList.get;
      aesop;
    | Ifte a1 e1 e2 ih1 ih2 =>
      intro T1 T2 hT v
      replace ih1 := ih1 S hT v; replace ih2 := ih2 S hT v
      have ⟨v', vh⟩ := inst_aexpr_full a1 S;
      unfold semExpr inst_expr;
      cases v' <;> simp_all

theorem semExpr_monotone_invariant
  (e: Expr ((π,τ)::ρ) π' τ') (T: Table ρ) (S: Inst π' [])
  : Monotone (fun I => (I ::ₕ T)⟦e[↦ S]⟧)
  := by
    intro I1 I2 hI;
    let T1 := @HList.cons _ _ (π,τ) ρ I1 T
    let T2 := @HList.cons _ _ (π,τ) ρ I2 T
    have TH : T1 ≤ T2 := by
      unfold_projs; unfold Table.le; cases T1; cases T2;
      simp_all;
    intro v; have := semExpr_monotone_table e S TH v
    simp_all

theorem functionCharacteristic_monotone
  {π: [Ty]'} {τ: Ty} {ρ: [Sig]'} (f: Func ρ π τ) (T: Table ρ)
  : Monotone (Φ[T,f](·))
  := by
    intro I1 I2 hM
    unfold functionCharacteristic;
    intro i v;
    simp_all
    apply semExpr_monotone_invariant
    exact hM

------

theorem semExpr_scott_table
  (e: Expr Γ π τ) (T: Set (Table Γ)) (S: Inst π []) (h: Set.Nonempty T) (cT: IsChain (· < ·) T)
  : sSup {t⟦e[↦ S]⟧ | t ∈ T} = (sSup T)⟦e[↦ S]⟧ := by
  induction e with
  | Atomic a =>
    have : ∀d ∈ {t⟦(Atomic a)[↦ S]⟧ | t ∈ T}, d = (sSup T)⟦(Atomic a)[↦ S]⟧ := by
      intro d ⟨din, ⟨_, dinh⟩⟩
      simp_all [← dinh]
      have ⟨v', vh⟩ := inst_aexpr_full a S;
      unfold semExpr inst_expr; simp_all
    have : {t⟦(Atomic a)[↦ S]⟧ | t ∈ T} = {(sSup T)⟦(Atomic a)[↦ S]⟧} := by
      simp_all; ext x; apply Iff.intro
      . intro xa; simp_all; aesop
      . intro xa; simp_all; have ⟨hx, hh⟩ := h; existsi hx; simp_all
    aesop
  | Fst a =>
    have : ∀d ∈ {t⟦(Fst a)[↦ S]⟧ | t ∈ T}, d = (sSup T)⟦(Fst a)[↦ S]⟧ := by
      intro d ⟨din, ⟨_, dinh⟩⟩
      simp_all [← dinh]
      have ⟨v', vh⟩ := inst_aexpr_full a S;
      unfold semExpr inst_expr; cases v'; simp_all
    have : {t⟦(Fst a)[↦ S]⟧ | t ∈ T} = {(sSup T)⟦(Fst a)[↦ S]⟧} := by
      simp_all; ext x; apply Iff.intro
      . intro xa; simp_all; aesop
      . intro xa; simp_all; have ⟨hx, hh⟩ := h; existsi hx; simp_all
    aesop
  | Snd a =>
    have : ∀d ∈ {t⟦(Snd a)[↦ S]⟧ | t ∈ T}, d = (sSup T)⟦(Snd a)[↦ S]⟧ := by
      intro d ⟨din, ⟨_, dinh⟩⟩
      simp_all [← dinh]
      have ⟨v', vh⟩ := inst_aexpr_full a S;
      unfold semExpr inst_expr; cases v'; simp_all
    have : {t⟦(Snd a)[↦ S]⟧ | t ∈ T} = {(sSup T)⟦(Snd a)[↦ S]⟧} := by
      simp_all; ext x; apply Iff.intro
      . intro xa; simp_all; aesop
      . intro xa; simp_all; have ⟨hx, hh⟩ := h; existsi hx; simp_all
    aesop
  | Flip p =>
    have : ∀d ∈ {t⟦(Flip p)[↦ S]⟧ | t ∈ T}, d = (sSup T)⟦(Flip p)[↦ S]⟧ := by
      intro d ⟨din, ⟨_, dinh⟩⟩
      simp_all [← dinh]
      unfold semExpr inst_expr; simp_all
    have : {t⟦(Flip p)[↦ S]⟧ | t ∈ T} = {(sSup T)⟦(Flip p)[↦ S]⟧} := by
      simp_all; ext x; apply Iff.intro
      . intro xa; simp_all; aesop
      . intro xa; simp_all; have ⟨hx, hh⟩ := h; existsi hx; simp_all
    aesop
  | Pair a1 a2 =>
    have : ∀d ∈ {t⟦(Pair a1 a2)[↦ S]⟧ | t ∈ T}, d = (sSup T)⟦(Pair a1 a2)[↦ S]⟧ := by
      intro d ⟨din, ⟨_, dinh⟩⟩
      simp_all [← dinh]
      have ⟨v1', v1h⟩ := inst_aexpr_full a1 S;
      have ⟨v2', v2h⟩ := inst_aexpr_full a2 S;
      unfold semExpr inst_expr; simp_all
    have : {t⟦(Pair a1 a2)[↦ S]⟧ | t ∈ T} = {(sSup T)⟦(Pair a1 a2)[↦ S]⟧} := by
      simp_all; ext x; apply Iff.intro
      . intro xa; simp_all; aesop
      . intro xa; simp_all; have ⟨hx, hh⟩ := h; existsi hx; simp_all
    aesop
  | Observe a =>
    have : ∀d ∈ {t⟦(Observe a)[↦ S]⟧ | t ∈ T}, d = (sSup T)⟦(Observe a)[↦ S]⟧ := by
      intro d ⟨din, ⟨_, dinh⟩⟩
      simp_all [← dinh]
      have ⟨v', vh⟩ := inst_aexpr_full a S;
      unfold semExpr inst_expr; cases v'; rw [vh]; simp_all
    have : {t⟦(Observe a)[↦ S]⟧ | t ∈ T} = {(sSup T)⟦(Observe a)[↦ S]⟧} := by
      simp_all; ext x; apply Iff.intro
      . intro xa; simp_all; aesop
      . intro xa; simp_all; have ⟨hx, hh⟩ := h; existsi hx; simp_all
    aesop
  | @Let Γ τ₁ τ₂ e1 e2 ih1 ih2 =>
    unfold inst_expr semExpr;
    simp_all; funext;
    let f := (λx t => t⟦e1[↦ S]⟧(x))
    let g := (λx t => t⟦e2[↦ x::ᵢS]⟧)
    let fg := (λx t => t⟦e1[↦ S]⟧(x) * t⟦e2[↦ x::ᵢS]⟧)
    have : ∀b x y, x ≤ y → fg b x ≤ fg b y := by
      intro b x y h1; apply Distribution.pmul_le_pmul; repeat (apply semExpr_monotone_table; assumption)
    have := Distribution.sSup_summation T h cT (λx t => t⟦e1[↦ S]⟧(x) * t⟦e2[↦ x::ᵢS]⟧) this (Finset.univ : Finset (Value τ₁))
    rw [← this]
    have ⟨t, th⟩ := h
    have t1: ∀x, {x_1 | ∃ x_2 ∈ T, x_2⟦e1[↦ S]⟧(x) * x_2⟦e2[↦ x::ᵢS]⟧ = x_1} = ((λy => f x y * g x y) '' T) := by aesop
    have : ∀x, (Monotone fun t => t⟦e1[↦ S]⟧(x)) := by intro x a b ab; simp_all; apply (Distribution.le_ext (a⟦e1[↦ S]⟧) (b⟦e1[↦ S]⟧)).mp ?_ x; apply semExpr_monotone_table; assumption
    have t2 := fun x => Distribution.sSup_cmul'' T h cT (f x) (this x) (g x) (by simp_all; apply semExpr_monotone_table)
    have t3: ∀y, {x_1 | ∃ t ∈ {x | ∃ t ∈ T, t⟦e1[↦ S]⟧ = x}, t y = x_1} = (f y '' T) := by aesop
    have t4: ∀y, {x | ∃ t ∈ T, t⟦e2[↦ y::ᵢS]⟧ = x} = (g y '' T) := by aesop
    conv in (∑ b : Value τ₁, sSup {x | ∃ x_1 ∈ T, x_1⟦e1[↦ S]⟧(b) * x_1⟦e2[↦ b::ᵢS]⟧ = x}) =>
      enter [2,x]; rw [t1 x, t2 x]
    conv in  (∑ x : Value τ₁, (sSup T)⟦e1[↦ S]⟧(x) * (sSup T)⟦e2[↦ x::ᵢS]⟧ ) =>
      enter [2,x]; rw [← ih1 S, ← ih2 (x::ᵢS), ← Distribution.sSup_apply, t3 x, t4 x]; rfl
  | Call f as =>
    unfold semExpr inst_expr;
    simp_all
    rw [← Table.sSup_apply, ← PDistribution.sSup_apply];
    simp_all; exact h
  | Ifte a e1 e2 =>
    unfold semExpr inst_expr;
    have ⟨v', vh⟩ := inst_aexpr_full a S;
    cases v' <;> simp_all

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
  (I: Set 𝔻[π](τ)) (h: Set.Nonempty I) (cI: IsChain (· < ·) I)
  : PDistribution.instSupSet.sSup {Φ[T,f](i) | i ∈ I} = Φ[T,f](PDistribution.instSupSet.sSup I)
  := by
    have ⟨i, ih⟩ := h
    unfold functionCharacteristic;
    let IT := {@HList.cons _ _ (π,τ) ρ i T | i ∈ I}
    have : {HList.head it | it ∈ IT} = I := by aesop
    have : {HList.tail it | it ∈ IT} = {T} := by unfold HList.tail; aesop
    have : sSup {T} = T := by aesop
    have : ({x | ∃ i ∈ I, (fun vs => (@HList.cons _ _ (π,τ) ρ i T)⟦f[↦ inst'' vs]⟧) = x} : Set 𝔻[π](τ)) = {λ vs => t⟦f[↦ inst'' vs]⟧ | t ∈ IT} := by aesop
    rw [this]
    have : @HList.cons _ _ (π,τ) ρ (sSup I) T = sSup IT := by rw [Table.sSup_cons_ext IT]; aesop
    rw [this]
    have x := fun vs => semExpr_scott_table f IT (inst'' vs) ?_ ?_;
    conv_rhs => ext vs; rw [← x vs]
    funext a; simp_all;
    rw [← PDistribution.sSup_apply];
    have : {x | @Exists 𝔻[π](τ) fun t => t ∈ {x | ∃ t ∈ IT, (fun vs => t⟦f[↦ inst'' vs]⟧) = x} ∧ t a = x } = {t⟦f[↦ inst'' a]⟧ | t ∈ IT} := by
      ext val; simp_all; apply Iff.intro;
      . rintro ⟨hv, hh1, hh2⟩; apply Membership.mem.out at hh1
        have ⟨hhv, hhh1,hhh2⟩ := hh1; aesop
      . rintro ⟨hv, hh1, hh2⟩; apply Membership.mem.out at hh1
        have : (fun vs => hv⟦f[↦ inst'' vs]⟧) ∈ {x | ∃ t ∈ IT, (fun vs => t⟦f[↦ inst'' vs]⟧) = x} := by aesop
        existsi (fun vs => hv⟦f[↦ inst'' vs]⟧); constructor; exact this; simp_all
    conv_lhs => congr; rw [this]
    aesop; simp_all
    existsi (@HList.cons _ _ (π,τ) ρ i T); aesop
    intro a aA b bB aneb; simp_all;
    have ahI : HList.head a ∈ I := by aesop
    have bhI : HList.head b ∈ I := by aesop
    have : b = @HList.cons _ _ (π,τ) ρ (HList.head b) T := by aesop
    rw [this] at aneb ⊢
    clear this
    have : a = @HList.cons _ _ (π,τ) ρ (HList.head a) T := by aesop
    rw [this] at aneb ⊢
    clear this
    simp_all
    by_cases hab : (HList.head a) = (HList.head b)
    contradiction
    have := cI ahI bhI (Ne.intro hab)
    cases' this with h1 h1
    . simp at h1; left; rw [lt_iff_le_not_le] at h1; apply And.intro; exact h1.left; simp_all
    . simp at h1; right; rw [lt_iff_le_not_le] at h1; apply And.intro; rw [Table.le_cons_ext]; simp_all; intro h; simp_all

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

def Invariant (I: Value[π]ₕ → 𝔻(τ)) (T: Table ρ) (f: Func ρ π τ)
  : Prop := functionCharacteristic f T I ≤ I

inductive FInvariant {τ: Ty} : Program τ ρ ρ' -> Table ρ -> Table ρ' -> Type where
  | nil    : FInvariant (PExpr e) T []
  | cons f : FInvariant p (i ::ₕ T) I -> Invariant i T f
          -> FInvariant (PFunc f (cast (by simp only [Prod.mk.eta]) p)) T (i ::ₕ I)

theorem semFunc_supI : Φ[T,f](I) ≤ I -> semFunc T f ≤ I := by
  intro h; apply OrderHom.lfp_le; simp_all

@[simp]
theorem semExpr_cast {h1: a = b} {h2: Expr a [] τ = Expr b [] τ} : semExpr (HList.cast T h1) (cast h2 e) = semExpr T e
  := by aesop

theorem semProgram_supI
  {I: Table ρ'} {TC: Table ρ} {TN: Table ρ} {p: Program τ ρ ρ'}
  : FInvariant p TC I -> TN ≤ TC -> semProgram TN p ≤ semProgramC I TC p := by
    induction p with
    | PExpr e =>
      intro _ h2;
      unfold semProgram semProgramC;
      rw [Distribution.le_ext]; intro v; rw [Probability.le_ext, DReal.le_ext]
      have := semExpr_monotone_table e id_inst h2 v
      simp at this; assumption
    | PFunc f p' ih =>
      rename_i ρ π τ ρ'
      intro h1 h2;
      rw [Distribution.le_ext]; intro v; rw [Probability.le_ext, DReal.le_ext]
      unfold semProgram semProgramC; simp_all
      cases I with | cons i is =>
        let _TC' := @HList.cons _ _ (π,τ) ρ i TC
        cases h1 with
        | cons f' fis fi =>
          rename_i X Y Z i B
          unfold Invariant at fi
          simp_all
          let TN' := HList.cons (semFunc TN f') TN
          simp_all;
          have le1: (@HList.cons _ _ Z ρ i TN) ≤ (@HList.cons _ _ Z ρ i TC) := by
            unfold_projs; unfold Table.le; aesop
          have : functionCharacteristic f' TN i ≤ functionCharacteristic f' TC i := by
            unfold functionCharacteristic; intro vs v; simp_all
            exact semExpr_monotone_table f' (inst'' vs) le1 v
          have : functionCharacteristic f' TN i ≤ i := le_trans this fi
          have : semFunc TN f' ≤ i := by simp_all [semFunc_supI]
          have : TN' ≤ _TC' := by unfold_projs; unfold Table.le; aesop
          apply ih <;> aesop

theorem semProgram_supI' {I: Table ρ'} {p: Program τ [] ρ'}
  : FInvariant p [] I -> semProgram' p ≤ semProgramC' I p := by
    unfold semProgram' semProgramC';
    intro h; apply semProgram_supI; exact h; simp


section Simps

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

@[simp] theorem semProgramC'_simp : semProgramC' I e = semProgramC I []ₕ e := by aesop
@[simp] theorem semProgramC_expr : semProgramC I T (PExpr e) = T⟦e⟧ := by unfold semProgramC; rfl
@[simp] theorem semProgramC_func : semProgramC (Table.cons i is) T (PFunc e p) = semProgramC is (Table.cons i T) p := by aesop

end Simps
