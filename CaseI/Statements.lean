import Groebner

/-!
# Statements from “A Conditional Solution to Iima–Yoshino Problem 2.3”

This file formalizes the statements of Theorem 1.1 and Proposition 6.1 over `ℂ`.
Proofs are deliberately left as `sorry` while the statements are reviewed.
-/

open scoped MonomialOrder

namespace CaseI

open MvPolynomial

/-- The polynomial ring `ℂ[x₁, x₂, …]`. -/
abbrev S := MvPolynomial ℕ+ ℂ

/-- The variable `xₙ`; it is defined to be zero at the unused index `n = 0`. -/
noncomputable def x (n : ℕ) : S :=
  if hn : 0 < n then X ⟨n, hn⟩ else 0

/-- The five-periodic coefficient sequence `s` from equation (3). -/
def s (c : ℂ) (n : ℕ) : ℂ :=
  match n % 5 with
  | 0 => 2
  | 1 => c
  | 2 => -1 - c
  | 3 => -1 - c
  | _ => c

/-- The relation `gₙ` from equation (4). -/
noncomputable def g (c : ℂ) (n : ℕ) : S :=
  C (s c n - c) * x n +
    ∑ i ∈ (Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n),
      C (s c (n - 2 * i)) * x i * x (n - i) +
    if 2 ∣ n then x (n / 2) ^ 2 else 0

/-- The non-resonant indices `D` from equation (5). -/
def D : Set ℕ :=
  {n | 2 ≤ n ∧ (n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3)}

/-- The ideal `I = (gₙ : n ∈ D)` from equation (5). -/
noncomputable def I (c : ℂ) : Ideal S :=
  Ideal.span (g c '' D)

/-- The successor of a positive integer, used as a variable index. -/
def next (i : ℕ+) : ℕ+ :=
  ⟨(i : ℕ) + 1, Nat.succ_pos i⟩

/-- The monic family `G` displayed in Theorem 1.1. -/
noncomputable def G (c : ℂ) : Set S :=
  Set.range (fun m : ℕ+ ↦ g c (2 * (m : ℕ))) ∪
    Set.range (fun m : ℕ+ ↦ C c⁻¹ * g c (2 * (m : ℕ) + 1))

/-- Weighted degree `wt(α) = ∑ i αᵢ`. -/
def weightedDegree (a : ℕ+ →₀ ℕ) : ℕ :=
  a.sum fun i e ↦ (i : ℕ) * e

/-- Second moment `σ(α) = ∑ i² αᵢ`. -/
def secondMoment (a : ℕ+ →₀ ℕ) : ℕ :=
  a.sum fun i e ↦ (i : ℕ) ^ 2 * e

/-- The monomial order from Section 4, with ordinary lexicographic tie-breaking. -/
def IsCaseIMonomialOrder (m : MonomialOrder ℕ+) : Prop :=
  ∀ a b,
    a ≺[m] b ↔
      weightedDegree a < weightedDegree b ∨
        weightedDegree a = weightedDegree b ∧
          (secondMoment b < secondMoment a ∨
            secondMoment a = secondMoment b ∧ toLex a < toLex b)

/-- The monomial ideal `J = (xᵢ², xᵢxᵢ₊₁ : i ≥ 1)`. -/
noncomputable def J : Ideal S :=
  Ideal.span
    (Set.range (fun i : ℕ+ ↦ monomial (Finsupp.single i 2) 1) ∪
      Set.range (fun i : ℕ+ ↦
        monomial (Finsupp.single i 1 + Finsupp.single (next i) 1) 1))

/-- Indices congruent to `±1` modulo five. -/
abbrev AllowedIndex :=
  {i : ℕ+ // (i : ℕ) % 5 = 1 ∨ (i : ℕ) % 5 = 4}

/-- The map sending each allowed variable to its residue class modulo `I`. -/
noncomputable def allowedToQuotient (c : ℂ) :
    MvPolynomial AllowedIndex ℂ →ₐ[ℂ] S ⧸ I c :=
  MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk (I c) (X i.1)

/--
Theorem 1.1.  Here the leading monomial is represented by its exponent vector
`m.degree`, and the assertion that the allowed residue classes freely generate the quotient is
represented by bijectivity of the canonical evaluation map `allowedToQuotient`.
-/
theorem theorem_1_1 (c : ℂ) (hc : c ^ 2 + c = 1) (m : MonomialOrder ℕ+)
    (hm : IsCaseIMonomialOrder m) :
    ∃ hG : m.IsGroebnerBasis (G c) (I c),
      hG.IsReduced ∧
        Ideal.span (m.leadingTerm '' (I c : Set S)) = J ∧
        (∀ i : ℕ+, m.degree (g c (2 * (i : ℕ))) = Finsupp.single i 2) ∧
        (∀ i : ℕ+, m.degree (g c (2 * (i : ℕ) + 1)) =
          Finsupp.single i 1 + Finsupp.single (next i) 1) ∧
        Function.Bijective (allowedToQuotient c) := by
  sorry

/-- A partition of `n`, represented by its finite multiplicity vector. -/
def Partition (n : ℕ) :=
  {a : ℕ+ →₀ ℕ // weightedDegree a = n}

/-- The multiplicity vector underlying a partition. -/
def Partition.multiplicities {n : ℕ} (a : Partition n) : ℕ+ →₀ ℕ :=
  a.val

/-- `P(n)`: partitions into parts congruent to `±1` modulo five. -/
def P (n : ℕ) :=
  {a : Partition n //
    ∀ i ∈ (Partition.multiplicities a).support,
      (i : ℕ) % 5 = 1 ∨ (i : ℕ) % 5 = 4}

/-- `Q(n)`: partitions whose adjacent parts differ by at least two. -/
def Q (n : ℕ) :=
  {a : Partition n //
    ∀ i : ℕ+, Partition.multiplicities a i ≤ 1 ∧
      (Partition.multiplicities a i ≠ 0 → Partition.multiplicities a (next i) = 0)}

/-- The monomial corresponding to a partition. -/
noncomputable def partitionMonomial {n : ℕ} (a : Partition n) : S :=
  monomial (Partition.multiplicities a) 1

/-- The unique normal form supplied by a reduced Gröbner basis. -/
noncomputable def normalForm {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) (p : S) : S :=
  Classical.choose <| hB.existsUnique_isRemainder (fun b hb ↦ by
    rw [hred.1 b hb]
    exact isUnit_one) p

/--
Proposition 6.1.  In every weighted degree, the support of the normal-form matrix contains a
perfect matching between `P(n)` and `Q(n)`.
-/
theorem proposition_6_1 (c : ℂ) (m : MonomialOrder ℕ+)
    (hG : m.IsGroebnerBasis (G c) (I c)) (hred : hG.IsReduced) (n : ℕ) :
    ∃ π : P n ≃ Q n,
      ∀ lam : P n,
        (normalForm hG hred (partitionMonomial lam.val)).coeff
          (Partition.multiplicities (π lam).val) ≠ 0 := by
  sorry

end CaseI
