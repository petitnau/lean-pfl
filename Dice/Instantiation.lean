import Data.Table
import Dice.Ast

def Inst (π π': [Ty]') := ∀τ, (τ ∈ₗ π) → AExpr π' τ
infix:66 " →ᵢ " => Inst

def Ren  (π π': [Ty]') := ∀τ, (τ ∈ₗ π) → (τ ∈ₗ π')
infix:66 " →ᵣ " => Ren

open Value AExpr Expr

def ren_inst (r: Ren π π') : Ren (τ::π) (τ::π') := λ_ => λ
  | Member.head => Member.head
  | Member.tail v' => Member.tail (r _ v')

def ren_aexpr (r: Ren π π') : AExpr π τ → AExpr π' τ
  | AVar v => AVar (r τ v)
  | AValue v => AValue v

def ren_expr (r: Ren π π') : Expr Γ π τ → Expr Γ π' τ
  | Atomic a => Atomic (ren_aexpr r a)
  | Fst a => Fst (ren_aexpr r a)
  | Snd a => Snd (ren_aexpr r a)
  | Pair a1 a2 => Pair (ren_aexpr r a1) (ren_aexpr r a2)
  | Let e1 e2 => Let (ren_expr r e1) (ren_expr (ren_inst r) e2)
  | Flip p => Flip p
  | Ifte a1 e1 e2 => Ifte (ren_aexpr r a1) (ren_expr r e1) (ren_expr r e2)
  | Observe a => Observe (ren_aexpr r a)
  | Call v as => Call v (as.map (ren_aexpr r))

def shift_expr : AExpr π τ -> AExpr (τ'::π) τ :=
  ren_aexpr λ_ => Member.tail

def shift_inst {τ: Ty} (s: Inst π π'): Inst (τ::π) (τ::π') := λ_ => λ
  | Member.head => AVar Member.head
  | Member.tail v' => shift_expr (s _ v')

def inst_aexpr (s: Inst π π') : AExpr π τ → AExpr π' τ
  | AVar i => s _ i
  | AValue v => AValue v

def inst_aexpr_value (s: Inst π []) : AExpr π τ → Value τ
  | AVar i => (s _ i).value
  | AValue v => v

def inst_expr (s: Inst π π') : Expr Γ π τ → Expr Γ π' τ
  | Atomic a => Atomic (inst_aexpr s a)
  | Fst a => Fst (inst_aexpr s a)
  | Snd a => Snd (inst_aexpr s a)
  | Pair a1 a2 => Pair (inst_aexpr s a1) (inst_aexpr s a2)
  | Let e1 e2 => Let (inst_expr s e1) (inst_expr (shift_inst s) e2)
  | Flip p => Flip p
  | Ifte a1 e1 e2 => Ifte (inst_aexpr s a1) (inst_expr s e1) (inst_expr s e2)
  | Observe a => Observe (inst_aexpr s a)
  | Call v as => Call v (as.map (inst_aexpr s))

def id_inst : Inst π π := λ_ => AVar

def cons_inst (e: AExpr π' τ) (s: Inst π π'): Inst (τ::π) π' := λ _ => λ
  | Member.head => e
  | Member.tail v' => s _ v'

def inst (p: (AExpr π')[π]ₕ) : Inst (π ++ π') π' := λ _ =>
  match π, p with
  | [], _ => id_inst _
  | _, HList.cons p ps => cons_inst p (inst ps) _

def inst' (p: (Value)[π]ₕ) : Inst (π ++ π') π' :=
  inst (p.map AValue)

def inst'' (p: (Value)[π]ₕ) : Inst π [] :=
  cast (by simp) (@inst' π [] p)

def inst_value (idx: τ ∈ₗ π) (s: Inst π []):  Value τ :=
  match s _ idx with
  | AVar m => nomatch m
  | AValue v => v

theorem sub_full (idx: τ ∈ₗ π) (s: Inst π []) : s _ idx = AValue (inst_value idx s) := by
  unfold inst_value; cases' s τ idx with _ _ h3; simp_all; exact Member.no_member_empty h3; simp_all

@[simp]
theorem inst_aexpr_full (a: AExpr π τ) (s: Inst π []) : inst_aexpr s a = AValue (inst_aexpr_value s a) := by
  unfold inst_aexpr inst_aexpr_value; cases a <;> simp; rename_i idx; rw [sub_full idx s]; simp_all

theorem inst_aexprs_full (as: HList (AExpr π) π') (s: Inst π []) : ∃vs, HList.map (inst_aexpr s) as = HList.map AValue vs := by
  unfold inst_aexpr; induction as with
  | nil => unfold HList.map; existsi []; simp_all;
  | cons a as ih =>
    unfold HList.map; have ⟨iv, ivh⟩ := ih; simp_all;
    cases a with
    | AVar v =>
      have ⟨v', vh'⟩: ∃v', s _ v = AValue v' :=
        match s _ v with
        | AValue v' => by existsi v'; rfl
      existsi (v' ::ₕ iv); simp_all;
    | AValue v => existsi (v ::ₕ iv); simp_all

@[simp]
theorem inst_id : inst_expr id_inst e = e
  := e.recOn
      (by intros; unfold inst_expr inst_aexpr id_inst; aesop)
      (by intros; unfold inst_expr inst_aexpr id_inst; aesop)
      (by intros; unfold inst_expr inst_aexpr id_inst; aesop)
      (by intros; unfold inst_expr; aesop)
      (by intros; unfold inst_expr inst_aexpr id_inst; aesop)
      (by intros; unfold inst_expr inst_aexpr id_inst; aesop)
      (by intros; unfold inst_expr; simp_all; rename_i ih1 ih2;
          unfold shift_inst shift_expr ren_aexpr; (conv => rhs; rw [← ih2]);
          congr; unfold id_inst; funext; aesop)
      (by intros; unfold inst_expr inst_aexpr id_inst; simp_all;
          rename_i a_3 a_4; clear a_3;
          induction a_4; aesop; unfold HList.map; aesop)
      (by intros; unfold inst_expr inst_aexpr id_inst; aesop)

@[simp] theorem inst_expr_atomic (S: Inst π π') (a: AExpr π τ)
  : inst_expr S (Atomic a : Expr Γ π τ) = Atomic (inst_aexpr S a) := by unfold inst_expr; rfl
@[simp] theorem inst_expr_fst (S: Inst π π') (a: AExpr π (τ₁ :×: τ₂))
  : inst_expr S (Fst a : Expr Γ π τ₁) = Fst (inst_aexpr S a) := by unfold inst_expr; rfl
@[simp] theorem inst_expr_snd (S: Inst π π') (a: AExpr π (τ₁ :×: τ₂))
  : inst_expr S (Snd a : Expr Γ π τ₂) = Snd (inst_aexpr S a) := by unfold inst_expr; rfl
@[simp] theorem inst_expr_pair (S: Inst π π') (a₁: AExpr π τ₁) (a₂: AExpr π τ₂)
  : inst_expr S (Pair a₁ a₂ : Expr Γ π (τ₁ :×: τ₂)) = Pair (inst_aexpr S a₁) (inst_aexpr S a₂) := by unfold inst_expr; rfl
@[simp] theorem inst_expr_flip (S: Inst π π')
  : inst_expr S (Flip r : Expr Γ π 𝔹) = Flip r := by unfold inst_expr; rfl
@[simp] theorem inst_expr_observe (S: Inst π π') (a: AExpr π 𝔹)
  : inst_expr S (Observe a : Expr Γ π 𝔹) = Observe (inst_aexpr S a) := by unfold inst_expr; rfl
@[simp] theorem inst_expr_ifte (S: Inst π π') (a: AExpr π 𝔹) (e₁: Expr Γ π τ) (e₂: Expr Γ π τ)
  : inst_expr S (Ifte a e₁ e₂ : Expr Γ π τ) = Ifte (inst_aexpr S a) (inst_expr S e₁) (inst_expr S e₂) := by (conv_lhs => unfold inst_expr)
@[simp] theorem inst_expr_let (S: Inst π π') (e₁: Expr Γ π τ₁) (e₂: Expr Γ (τ₁::π) τ)
  : inst_expr S (Let e₁ e₂ : Expr Γ π τ) = Let (inst_expr S e₁) (inst_expr (shift_inst S) e₂) := by (conv_lhs => unfold inst_expr)
@[simp] theorem inst_expr_call (S: Inst π π') (f: Member (π'', τ) Γ) (as: (AExpr π)[π'']ₕ)
  : inst_expr S (Call f as : Expr Γ π τ) = Call f (as.map (inst_aexpr S)) := by (conv_lhs => unfold inst_expr)

theorem inst_compose' (i: Value τ₁) (S: Inst π π') (e: Expr Γ π'' τ₂):
  ∀(h : π'' = (τ₁:: π : [Ty]')),
  (inst_expr (cons_inst (AValue i) id_inst) (inst_expr (shift_inst S) (cast (by rw [h]) e))) =
  (inst_expr (cons_inst (AValue i) S) (cast (by rw [h]) e))
  := by stop
    intro h
    induction e
    . unfold cons_inst shift_inst; simp_all

@[simp]
theorem inst_compose (i: Value τ₁) (S: Inst π π') (e: Expr Γ (τ₁::π) τ₂):
  (inst_expr (cons_inst (AValue i) id_inst) (inst_expr (shift_inst S) e)) =
  (inst_expr (cons_inst (AValue i) S) e)
  := by have := inst_compose' i S e rfl; aesop

notation:max e "[↦ " S "]" => inst_expr S e
notation:max v "::ᵢ" S => cons_inst (AValue v) S
notation:max "[]ᵢ" => id_inst
