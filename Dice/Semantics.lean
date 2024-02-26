import Dice.Ast
import Dice.Env
import Dice.Termination
import Dice.Instantiation

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
    | VTrue  => θ
    | VFalse => 1 - θ

  | Observe (AValue v1) => λ
    | VTrue  => if v1 == VTrue then 1 else 0
    | VFalse => 0

  | Ifte (AValue vg) e1 e2 =>
    match vg with
    | VTrue => T〚e1〛
    | VFalse => T〚e2〛

  | Let e1 e2  => λv =>
    ∑ v', T〚e1〛(v') * T〚e2[↦ v']〛(v)

  | Call f as =>
    let vs := (map (fun _ (AValue v) => v) as)
    (T.get f) vs

termination_by e => size e
decreasing_by all_goals (simp_wf; (conv => rhs; unfold size); linarith)

def semFunc {π: List Ty} {τ: Ty} {ρ: List (List Ty × Ty)} (I: HList Value π -> Distribution τ) (T: Table ρ) : Function ((π,τ)::ρ) π τ -> (HList Value π -> Distribution τ) :=
  fun e vs =>
    let as := (map (fun _ v => AValue v) vs)
    let T' := @HList.cons _ _ (π,τ) ρ I T
    semExpr T' (inst_expr (inst as) (cast (by simp) e))

def semProgram (Is: Table ρ') (T: Table ρ) : Program ρ ρ' τ -> Distribution τ
  | Expression e => semExpr T e
  | Func f e =>
    match Is with
    | @HList.cons _ _ (π', τ') _ I Is' =>
      let Te := semFunc I T f
      let T' := @HList.cons _ _ (π', τ') ρ Te T
      semProgram Is' T' e

def semProgram' (Is: Table ρ') : Program [] ρ' τ -> Distribution τ :=
  semProgram Is HList.nil

def toFinset (f: Distribution τ): Finset (Value τ × Rat) :=
  Finset.univ.image (fun x => (x, f x))

def normFact (f: Distribution τ): Rat :=
  ∑ x in (toFinset f), x.snd

def normalize (f: Distribution τ): Distribution τ :=
  fun x => (f x)/(normFact f)
