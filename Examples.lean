import Dice.Semantics
open Var Ty Value AExpr Expr

------------
-- SYNTAX --
------------

-- Indices
declare_syntax_cat index
syntax "Z" : index
syntax "S" index : index
syntax " ⟪ " index " ⟫ᵢ " : term
macro_rules
  | `(⟪ Z ⟫ᵢ)           => `(ZVar)
  | `(⟪ S $i:index ⟫ᵢ)  => `(SVar (⟪ $i ⟫ᵢ))

-- Values
declare_syntax_cat value
syntax " true " : value
syntax " false " : value
syntax " ( " value " , " value " )" : value
syntax " ( " value " ) " : value
syntax " ⟪ " value " ⟫ᵥ " : term
macro_rules
  | `(⟪ true ⟫ᵥ)                    => `(VTrue)
  | `(⟪ false ⟫ᵥ)                   => `(VFalse)
  | `(⟪ ($v1:value, $v2:value) ⟫ᵥ)  => `(VPair ⟪ $v1 ⟫ᵥ ⟪ $v2 ⟫ᵥ)
  | `(⟪ ($v:value) ⟫ᵥ)              => `(⟪ $v:value ⟫ᵥ)

-- Atomic expressions
declare_syntax_cat aexpr
syntax index : aexpr
syntax value : aexpr
syntax " ( " aexpr " ) " : aexpr
syntax " ⟪ " aexpr " ⟫ₐ " : term
macro_rules
  | `(⟪ $v:value ⟫ₐ)      => `(AValue ⟪ $v ⟫ᵥ)
  | `(⟪ $i:index ⟫ₐ)      => `(AVar ⟪ $i ⟫ᵢ)
  | `(⟪ ( $a:aexpr ) ⟫ₐ)  => `(⟪ $a ⟫ₐ)

-- Expressions
declare_syntax_cat expr
syntax value : expr
syntax aexpr : expr
syntax " fst " aexpr : expr
syntax " snd " aexpr : expr
syntax " ( " aexpr " , " aexpr " )" : expr
syntax " let " expr " in " expr : expr
syntax " flip " scientific : expr
syntax " if " aexpr " then " expr " else " expr : expr
syntax " observe " aexpr : expr
syntax " ( "  expr " ) " : expr
syntax " ⟪ "  expr " ⟫ₑ " : term
macro_rules
  | `(⟪ fst $a:aexpr ⟫ₑ)              => `(Fst ⟪ $a ⟫ₐ)
  | `(⟪ snd $a:aexpr ⟫ₑ)              => `(Snd ⟪ $a ⟫ₐ)
  | `(⟪ ($a1:aexpr, $a2:aexpr) ⟫ₑ)    => `(Pair ⟪ $a1 ⟫ₐ ⟪ $a2 ⟫ₐ)
  | `(⟪ let $e1:expr in $e2:expr ⟫ₑ)  => `(Let ⟪ $e1 ⟫ₑ ⟪ $e2 ⟫ₑ)
  | `(⟪ flip $n:scientific ⟫ₑ)        => `(Flip $n)
  | `(⟪ if $a:aexpr then $e1:expr else $e2:expr ⟫ₑ) => `(Ifte ⟪ $a ⟫ₐ ⟪ $e1 ⟫ₑ ⟪ $e2 ⟫ₑ)
  | `(⟪ observe $a:aexpr ⟫ₑ)          => `(Observe ⟪ $a ⟫ₐ)
  | `(⟪ $v:value ⟫ₑ)                  => `(Atomic (AValue ⟪ $v ⟫ᵥ))
  | `(⟪ $a:aexpr ⟫ₑ)                  => `(Atomic ⟪ $a ⟫ₐ)
  | `(⟪ ( $e:expr ) ⟫ₑ)               => `(⟪ $e ⟫ₑ)

-- Syntactic sugar
syntax aexpr " || " aexpr : expr
macro_rules
  | `(⟪ $a1:aexpr || $a2:aexpr ⟫ₑ) => `(Ifte ⟪ $a1 ⟫ₐ ⟪ true ⟫ₑ (Atomic ⟪ $a2 ⟫ₐ))


--------------
-- EXAMPLES --
--------------

def diceExample1: Expr [] [] TBool := ⟪
  let (flip 0.3) in
  let (flip 0.8) in
  let (S Z || Z) in
  let (observe Z) in
  S S S Z⟫ₑ
#eval (toFinset <| normalize <| semExpr <| diceExample1) == {(VTrue, 15/43), (VFalse, 28/43)}

def diceExample2: Expr [] [] TBool := ⟪
  let (flip 0.3) in
  let (flip 0.8) in
  let (Z, false) in
  let (S S Z, Z) in
  let (snd Z) in
  (fst Z)⟫ₑ
#eval (toFinset <| normalize <| semExpr <| diceExample2) == {(VTrue, 8/10), (VFalse, 2/10)}
