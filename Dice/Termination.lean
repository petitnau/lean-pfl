import Dice.Ast
import Dice.Instantiation

open Expr

def size { τ: Ty}: Expr T δ τ -> ℕ
  | Fst _ => 1
  | Snd _ => 1
  | Flip _ => 1
  | Atomic _ => 1
  | Pair _ _ => 1
  | Call _ _ => 1
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
  unfold size inst_expr; simp
  unfold size inst_expr; simp
