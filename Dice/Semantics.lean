import Dice.Ast
import Dice.Env
import Dice.Termination
import Dice.Instantiation
import Data.Min
import Data.KFinset
import Mathlib.Order.Hom.Basic

open Value AExpr Expr Program
open BigOperators

set_option hygiene false
notation:max " 〚 " v " 〛ᵥ " => semValue v
def semValue (v1: Value τ): Distribution τ :=
  fun v => if v == v1 then 1 else 0

notation:max " 〚 " e " 〛ₐ " => semAExpr e
def semAExpr : AExpr [] τ -> Distribution τ
  | AValue v1 => semValue v1

notation:max T " 〚 " e " 〛 " => semExpr T e
notation:max T " 〚 " e " 〛( " v " ) " => semExpr T e v
def semExpr (T: Table ρ) : Expr ρ [] τ -> Distribution τ
  | Atomic (AValue v1) =>
    〚v1〛ᵥ

  | Fst (AValue $ VPair v1 _) =>
    〚v1〛ᵥ

  | Snd (AValue $ VPair _ v2) =>
    〚v2〛ᵥ

  | Pair (AValue v1) (AValue v2) =>
    〚VPair v1 v2〛ᵥ

  | Flip θ => λ
    | VTrue  => θ.prob
    | VFalse => θ.invProb

  | Observe (AValue v1) => λ
    | VTrue  => if v1 == VTrue then 1 else 0
    | VFalse => 0

  | Ifte (AValue vg) e1 e2 =>
    match vg with
    | VTrue => T〚e1〛
    | VFalse => T〚e2〛

  | Let e1 e2  => λv =>
    (∑ v', (T〚e1〛(v')) * (T〚e2[↦ v']〛(v)))

  | Call f as =>
    let vs := as.map (fun _ (AValue v) => v)
    (T.get f) vs

  termination_by e => size e
  decreasing_by all_goals (simp_wf; (conv => rhs; unfold size); linarith)

def chare (e: Expr ρ [] τ') : Table ρ -> Distribution τ'
  := fun T => @semExpr ρ τ' T e

theorem chare_monotone {π: List Ty} {τ: Ty} {ρ: List (List Ty × Ty)}
  (e: Expr ρ π τ) (S: Inst π [])
  : Monotone (@chare ρ τ (inst_expr S e))
  := by
    induction e with
    | Atomic a1 =>
      intro T1 T2 hT
      have ⟨v', vh⟩ := inst_aexpr_full a1 S;
      unfold chare semExpr inst_expr; simp_all
    | Fst a1 =>
      intro T1 T2 hT
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      unfold chare semExpr inst_expr; cases v1; simp_all
    | Snd a1 =>
      intro T1 T2 hT
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      unfold chare semExpr inst_expr; cases v1; simp_all
    | Flip =>
      intro T1 T2 hT
      unfold chare semExpr inst_expr; simp_all
    | Observe a1 =>
      intro T1 T2 hT
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      unfold chare semExpr inst_expr; cases v1 <;> simp_all
    | Pair a1 a2 =>
      intro T1 T2 hT
      have ⟨v1, v1h⟩ := inst_aexpr_full a1 S;
      have ⟨v2, v2h⟩ := inst_aexpr_full a2 S;
      unfold chare semExpr inst_expr; cases v1 <;> cases v2 <;> simp_all
    | Let e1 e2 ih1 ih2 =>
      intro T1 T2 hT v
      unfold chare at *; unfold inst_expr semExpr; simp_all
      rw [←DReal.le_ext, ←Probability.le_ext];
      apply Finset.sum_le_sum;
      intro i hi;
      replace ih1 := ih1 S hT i;
      replace ih2 := ih2 (cons_inst (AValue i) S) hT v
      apply Probability.mul_le_mul _ _;
      simp_all; simp_all
    | Call f as =>
      intro T1 T2 hT v
      unfold chare semExpr inst_expr;
      induction f <;> simp_all; cases T1; cases T2; simp_all;
      unfold HList.get; unfold_projs at hT; unfold le_table at hT;
      rw [←DReal.le_ext, ←Probability.le_ext]; apply hT.left;
      rename_i aih; cases T1; cases T2; unfold_projs at hT;
      unfold le_table at hT;
      replace aih := aih hT.right; unfold HList.get;
      aesop;
    | Ifte a1 e1 e2 ih1 ih2 =>
      intro T1 T2 hT v
      replace ih1 := ih1 S hT v; replace ih2 := ih2 S hT v
      have ⟨v', vh⟩ := inst_aexpr_full a1 S;
      unfold chare at *; unfold semExpr inst_expr;
      cases v' <;> simp_all

def chare' (e: Expr ((π,τ)::ρ) [] τ') (T: Table ρ): (HList Value π -> Distribution τ) -> Distribution τ'
  := fun I => chare e (HList.cons I T)

theorem chare_monotone' {π: List Ty} {τ τ': Ty} {ρ: List (List Ty × Ty)}
  (e: Expr ((π,τ)::ρ) [] τ') (T: Table ρ)
  : Monotone (@chare' π τ ρ τ' e T)
  := by
    unfold chare'; intro I1 I2 hI;
    let T1 := @HList.cons _ _ (π,τ) ρ I1 T
    let T2 := @HList.cons _ _ (π,τ) ρ I2 T
    have TH : T1 ≤ T2 := by
      unfold_projs; unfold le_table; cases T1; cases T2;
      simp_all; apply le_table_refl
    intro v; have := chare_monotone e id_inst TH v
    simp_all

def semFuncC {π: List Ty} {τ: Ty} {ρ: List (List Ty × Ty)} (T: Table ρ) (I: HList Value π -> Distribution τ) : Function ((π,τ)::ρ) π τ -> (HList Value π -> Distribution τ) :=
  fun e vs =>
    let as := vs.map (fun _ v => AValue v)
    let T' := @HList.cons _ _ (π,τ) ρ I T
    let e' := (inst_expr (inst as) (cast (by simp) e))
    semExpr T' e'

def charf {π: List Ty} {τ: Ty} {ρ: List (List Ty × Ty)}
  (f: Function ((π,τ)::ρ) π τ) (T: Table ρ)
  : (HList Value π → Distribution τ) -> (HList Value π → Distribution τ)
  := fun I vs =>
      let as := vs.map (fun _ v => AValue v)
      let T' := @HList.cons _ _ (π,τ) ρ I T
      let f' := (inst_expr (inst as) (cast (by simp) f))
      semExpr T' f'

theorem charf_monotone {π: List Ty} {τ: Ty} {ρ: List (List Ty × Ty)}
  (f: Function ((π,τ)::ρ) π τ) (T: Table ρ)
  : Monotone (@charf π τ ρ f T)
  := by
    intro I1 I2 hM
    unfold charf;
    intro i v;
    simp_all
    rw [←DReal.le_ext, ←Probability.le_ext]
    apply chare_monotone'
    exact hM

noncomputable def semFunc {π: List Ty} {τ: Ty} {ρ: List (List Ty × Ty)}
  (T: Table ρ) (f: Function ((π,τ)::ρ) π τ)
  : (HList Value π -> Distribution τ)
  := OrderHom.lfp ⟨charf f T, charf_monotone f T⟩

noncomputable def semProgram {ρ': List (List Ty × Ty)} (T: Table ρ): Program ρ ρ' τ -> Distribution τ
  | Expression e => semExpr T e
  | Func f e =>
      let T' := HList.cons (semFunc T f) T
      semProgram T' e

noncomputable def semProgram' : Program [] ρ' τ -> Distribution τ :=
  semProgram HList.nil

def semProgramC (Is: Table ρ') (T: Table ρ) : Program ρ ρ' τ -> Distribution τ
  | Expression e => semExpr T e
  | Func f e =>
    match Is with
    | @HList.cons _ _ (π', τ') _ I Is' =>
      let T' := @HList.cons _ _ (π', τ') ρ I T
      semProgramC Is' T' e

def semProgramC' (Is: Table ρ') : Program [] ρ' τ -> Distribution τ :=
  semProgramC Is HList.nil

def toFinset (f: Distribution τ): KFinset (Value τ) ℝ :=
  ⟨Finset.univ, fun v => f v⟩

def normFact (f: Distribution τ): DReal :=
  ∑ x in Finset.univ, (f x).val

def normProb (f: Distribution τ): Distribution τ :=
  fun x => (f x).div (normFact f)

def Invariant (I: HList Value π → Distribution τ) (T: Table ρ) (f: Function ((π,τ)::ρ) π τ)
  : Prop := charf f T I ≤ I

inductive FInvariant {τ: Ty} : Program ρ ρ' τ -> Table ρ -> Table ρ' -> Type where
  | nil    : FInvariant (Expression e) T []
  | cons f : FInvariant p (HList.cons i T) I -> Invariant i T f -> FInvariant (Func f (cast (by simp only [Prod.mk.eta]) p)) T (HList.cons i I)

theorem semFunc_supI : charf f T I ≤ I -> semFunc T f ≤ I := by
  intro h; apply OrderHom.lfp_le; simp_all

@[simp]
theorem semExpr_cast {h1: a = b} {h2: Expr a [] τ = Expr b [] τ} : semExpr (HList.cast T h1) (cast h2 e) = semExpr T e
  := by aesop

theorem semProgram_supI {I: Table ρ'} {TC: Table ρ} {TN: Table ρ} {p: Program ρ ρ' τ}
  : FInvariant p TC I -> TN ≤ TC -> semProgram TN p ≤ semProgramC I TC p := by
    induction p with
    | Expression e =>
      intro h1 h2;
      unfold semProgram semProgramC; simp_all
      intro v;
      have := chare_monotone e id_inst h2 v
      unfold chare at this; simp at this
      assumption
    | Func f p' ih =>
      rename_i π τ ρ ρ' τ'
      intro h1 h2;
      simp_all
      unfold semProgram semProgramC; simp_all
      intro v; cases I with | cons i is =>
        let TC' := @HList.cons _ _ (π,τ) ρ i TC
        cases h1 with
        | cons f' fis fi =>
          rename_i X Y Z i B
          unfold Invariant at fi
          simp_all
          let TN' := HList.cons (semFunc TN f') TN
          simp_all

          have le1: (@HList.cons _ _ _ ρ i TN) ≤ (@HList.cons _ _ _ ρ i TC) := by unfold_projs; unfold le_table; aesop
          have : charf f' TN i ≤ charf f' TC i := by
            unfold charf; intro vs v; simp_all
            have x := chare_monotone (cast (by simp: Function ((Z.1, Z.2) :: ρ) Z.1 Z.2 = Expr ((Z.1, Z.2) :: ρ) (Z.1 ++ List.nil) Z.2) f') (inst (HList.map (fun x v => AValue v) vs)) le1
            unfold chare at x ; simp_all

          have : charf f' TN i ≤ i := le_trans this fi
          have : semFunc TN f' ≤ i := by simp_all [semFunc_supI]
          have : TN' ≤ TC' := by unfold_projs; unfold le_table; aesop

          apply ih <;> aesop

theorem semProgram_supI' {I: Table ρ'} {p: Program [] ρ' τ}
  : FInvariant p [] I -> semProgram' p ≤ semProgramC' I p := by
    unfold semProgram' semProgramC';
    intro h; apply semProgram_supI; exact h; simp
