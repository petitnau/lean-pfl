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
  | AVar v => s _ v
  | AValue v => AValue v

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

theorem sub_full (idx: τ ∈ₗ π) (s: Inst π []) : ∃v, s _ idx = AValue v := by
  cases s _ idx with
  | AVar m => cases m;
  | AValue v => exact ⟨v, rfl⟩

theorem inst_aexpr_full (a: AExpr π τ) (s: Inst π []) : ∃v, inst_aexpr s a = AValue v := by
  unfold inst_aexpr; cases a <;> simp; rename_i idx; exact sub_full idx s

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
