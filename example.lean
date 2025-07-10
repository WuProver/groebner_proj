import Groebner.Basic

open MvPolynomial
open MonomialOrder
example : MonomialOrder.lex.IsGroebnerBasis
    ({ X 0, X 1 } : Finset <| MvPolynomial (Fin 3) ℚ)
    (Ideal.span ({X 0, X 1, X 0 + X 1})) := by
  -- have : MonomialOrder.lex.IsGroebnerBasis
  --   (?_ : Finset <| MvPolynomial (Fin 3) ℚ)
  --   (Ideal.span ({X 0, X 1})) := by
  --   exact (sorry : MonomialOrder.lex.IsGroebnerBasis
  --   (∅ : Finset <| MvPolynomial (Fin 3) ℚ)
  --   (Ideal.span ({X 0, X 1})))
  -- --· exact {}
  sorry


example : MonomialOrder.lex.IsRemainder
    (X 0 ^ 2 * X 1 + X 0 * X 1 ^2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)
    ({ X 0 * X 1 - 1, X 1 ^ 2 - 1 } : Finset <| MvPolynomial (Fin 2) ℚ)
    (2 * X 0 + 1)
    := by
  rw [MonomialOrder.isRemainder_finset₀₁]
  split_ands
  · sorry
  · sorry
  · sorry

-- #check @IsRemainder.isRemainder_def
