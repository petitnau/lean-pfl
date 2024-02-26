import Dice.Ast
import Dice.Env
import Dice.Termination
import Dice.Instantiation

open Value AExpr Expr
open BigOperators

set_option hygiene false
notation:max " 〚 " v " 〛ᵥ " => semValue v
def semValue (v1: Value τ): Distribution τ :=
  fun v => if v == v1 then 1 else 0

notation:max " 〚 " e " 〛ₐ " => semAExpr e
def semAExpr : AExpr [] τ -> Distribution τ
  | AValue v1 => semValue v1

notation:max " 〚 " e " 〛 " => semExpr e
notation:max " 〚 " e " 〛( " v " ) " => semExpr e v
def semExpr : Expr [] [] τ -> Distribution τ
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
