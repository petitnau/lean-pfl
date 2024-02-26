import Dice.Ast
import Dice.Env

def Inst (δ δ': Env) := ∀τ, Member δ τ → AExpr δ' τ
def Ren  (δ δ': Env) := ∀τ, Member δ τ → Member δ' τ

open Value AExpr Expr

def ren_inst (τ: Ty) (r: Ren δ δ'): Ren (τ::δ) (τ::δ') := λ τ' => λ
  | Member.head => Member.head
  | Member.tail v' => Member.tail (r _ v')

def ren_aexpr (r: Ren δ δ') : AExpr δ τ → AExpr δ' τ
  | AVar v => AVar (r _ v)
  | AValue v => AValue v

def ren_expr (r: Ren δ δ') : Expr T δ τ → Expr T δ' τ
  | Atomic a => Atomic (ren_aexpr r a)
  | Fst a => Fst (ren_aexpr r a)
  | Snd a => Snd (ren_aexpr r a)
  | Pair a1 a2 => Pair (ren_aexpr r a1) (ren_aexpr r a2)
  | Let e1 e2 => Let (ren_expr r e1) (ren_expr (ren_inst _ r) e2)
  | Flip p => Flip p
  | Ifte a1 e1 e2 => Ifte (ren_aexpr r a1) (ren_expr r e1) (ren_expr r e2)
  | Observe a => Observe (ren_aexpr r a)
  | Call v as => Call v (map (fun _ => ren_aexpr r) as)

def shift_expr (δ: Env) (τ τ': Ty): AExpr δ τ -> AExpr (τ'::δ) τ :=
  ren_aexpr (fun _ v => Member.tail v)

def shift_inst (τ: Ty) (s: Inst δ δ'): Inst (τ::δ) (τ::δ') := λ τ' => λ
  | Member.head => AVar Member.head
  | Member.tail v' => shift_expr _ _ _  (s _ v')

def inst_aexpr (s: Inst δ δ') : AExpr δ τ → AExpr δ' τ
  | AVar v => s _ v
  | AValue v => AValue v

def inst_expr (s: Inst δ δ') : Expr T δ τ → Expr T δ' τ
  | Atomic a => Atomic (inst_aexpr s a)
  | Fst a => Fst (inst_aexpr s a)
  | Snd a => Snd (inst_aexpr s a)
  | Pair a1 a2 => Pair (inst_aexpr s a1) (inst_aexpr s a2)
  | Let e1 e2 => Let (inst_expr s e1) (inst_expr (shift_inst _ s) e2)
  | Flip p => Flip p
  | Ifte a1 e1 e2 => Ifte (inst_aexpr s a1) (inst_expr s e1) (inst_expr s e2)
  | Observe a => Observe (inst_aexpr s a)
  | Call v as => Call v (map (fun _ => inst_aexpr s) as)

def id_inst : Inst δ δ := fun _ => AVar

def cons_inst (e: AExpr δ' τ) (s: Inst δ δ'): Inst (τ::δ) δ' :=
  fun τ' (v: Member (τ::δ) τ') =>
    match v with
    | Member.head => e
    | Member.tail v' => s _ v'

notation:max e " [↦ " v " ] " => (inst_expr (cons_inst (AValue v) id_inst) e)
