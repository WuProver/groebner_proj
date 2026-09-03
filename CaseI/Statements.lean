import Groebner
import Mathlib.LinearAlgebra.Determinant

/-!
# Statements from “A Conditional Solution to Iima–Yoshino Problem 2.3”

This file formalizes Theorem 1.1 and Proposition 6.1 over `ℂ`.
-/

open scoped MonomialOrder

namespace CaseI

open MvPolynomial

/-- The polynomial ring `ℂ[x₁, x₂, …]`. -/
abbrev S := MvPolynomial ℕ+ ℂ

/-- The variable `xₙ`; it is defined to be zero at the unused index `n = 0`. -/
noncomputable def x (n : ℕ) : S :=
  if hn : 0 < n then X ⟨n, hn⟩ else 0

lemma x_eq_X (i : ℕ+) : x (i : ℕ) = X i := by
  unfold x
  split <;> rename_i h
  · apply congrArg X
    exact Subtype.ext rfl
  · exact (h i.prop).elim

/-- The five-periodic coefficient sequence `s` from equation (3). -/
def s (c : ℂ) (n : ℕ) : ℂ :=
  match n % 5 with
  | 0 => 2
  | 1 => c
  | 2 => -1 - c
  | 3 => -1 - c
  | _ => c

/-- The five-periodic auxiliary coefficient sequence `η` from equation (3). -/
def eta (c : ℂ) (n : ℕ) : ℂ :=
  match n % 5 with
  | 0 => 0
  | 1 => 1
  | 2 => c
  | 3 => -c
  | _ => -1

lemma ne_zero_of_quadratic (c : ℂ) (hc : c ^ 2 + c = 1) : c ≠ 0 := by
  intro h
  simp [h] at hc

lemma one_add_two_mul_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) : 1 + 2 * c ≠ 0 := by
  have hsquare : (1 + 2 * c) ^ 2 = 5 := by
    calc
      (1 + 2 * c) ^ 2 = 1 + 4 * (c ^ 2 + c) := by ring
      _ = 5 := by rw [hc]; norm_num
  intro h
  rw [h] at hsquare
  norm_num at hsquare

lemma two_sub_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) : 2 - c ≠ 0 := by
  have hproduct : (2 - c) * (3 + c) = 5 := by
    calc
      (2 - c) * (3 + c) = 6 - (c ^ 2 + c) := by ring
      _ = 5 := by rw [hc]; norm_num
  intro h
  rw [h] at hproduct
  norm_num at hproduct

lemma eta_mainCoeff_eq_zero (c : ℂ) (_hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3) :
    -(eta c n + c * eta c (2 * n)) = 0 := by
  rcases hn with hn | hn | hn
  · simp [eta, Nat.mul_mod, hn]
  · simp [eta, Nat.mul_mod, hn]
  · simp [eta, Nat.mul_mod, hn]

lemma eta_mainCoeff_of_mod_eq_one (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 1) : -(eta c n + c * eta c (2 * n)) = c - 2 := by
  simp [eta, Nat.mul_mod, hn]
  linear_combination -hc

lemma eta_mainCoeff_of_mod_eq_four (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 4) : -(eta c n + c * eta c (2 * n)) = 2 - c := by
  simp [eta, Nat.mul_mod, hn]
  linear_combination hc

noncomputable def zetaPolynomial (c : ℂ) : Polynomial ℂ :=
  Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (-c) * Polynomial.X + Polynomial.C 1

lemma zetaPolynomial_degree_ne_zero (c : ℂ) : (zetaPolynomial c).degree ≠ 0 := by
  have hdeg : (zetaPolynomial c).natDegree = 2 := by
    exact Polynomial.natDegree_quadratic (a := (1 : ℂ)) (b := -c) (c := 1) (by norm_num)
  have hp : zetaPolynomial c ≠ 0 := by
    intro hp
    rw [hp] at hdeg
    norm_num at hdeg
  rw [Polynomial.degree_eq_natDegree hp, hdeg]
  norm_num

/-- A root of `z² - cz + 1`; under `c² + c = 1` it is a fifth root of unity. -/
noncomputable def zeta (c : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_root (zetaPolynomial c) (zetaPolynomial_degree_ne_zero c))

lemma zeta_spec (c : ℂ) : zeta c ^ 2 - c * zeta c + 1 = 0 := by
  have h := Classical.choose_spec
    (IsAlgClosed.exists_root (zetaPolynomial c) (zetaPolynomial_degree_ne_zero c))
  simpa [zeta, Polynomial.IsRoot, zetaPolynomial, sub_eq_add_neg] using h

lemma zeta_ne_zero (c : ℂ) : zeta c ≠ 0 := by
  intro hz
  have h := zeta_spec c
  simp [hz] at h

lemma zeta_add_inv (c : ℂ) : zeta c + (zeta c)⁻¹ = c := by
  have hz := zeta_ne_zero c
  field_simp [hz]
  linear_combination zeta_spec c

lemma zeta_pow_five (c : ℂ) (hc : c ^ 2 + c = 1) : zeta c ^ 5 = 1 := by
  have h := hc
  rw [← zeta_add_inv c] at h
  field_simp [zeta_ne_zero c] at h
  have hsum : zeta c ^ 4 + zeta c ^ 3 + zeta c ^ 2 + zeta c + 1 = 0 := by
    linear_combination h
  apply sub_eq_zero.mp
  calc
    zeta c ^ 5 - 1 = (zeta c - 1) *
        (zeta c ^ 4 + zeta c ^ 3 + zeta c ^ 2 + zeta c + 1) := by ring
    _ = 0 := by rw [hsum]; ring

lemma zeta_sub_inv_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c - (zeta c)⁻¹ ≠ 0 := by
  intro hdelta
  have hzsq : zeta c ^ 2 = 1 := by
    have hdelta' := hdelta
    field_simp [zeta_ne_zero c] at hdelta'
    exact sub_eq_zero.mp (by simpa [pow_two] using hdelta')
  have hfactor : (zeta c - 1) * (zeta c + 1) = 0 := by
    calc
      (zeta c - 1) * (zeta c + 1) = zeta c ^ 2 - 1 := by ring
      _ = 0 := by rw [hzsq]; ring
  rcases mul_eq_zero.mp hfactor with hz | hz
  · have hzeta : zeta c = 1 := sub_eq_zero.mp hz
    have hc_two : c = 2 := by
      rw [← zeta_add_inv c, hzeta]
      norm_num
    rw [hc_two] at hc
    norm_num at hc
  · have hzeta : zeta c = -1 := by linear_combination hz
    have hc_neg_two : c = -2 := by
      rw [← zeta_add_inv c, hzeta]
      norm_num
    rw [hc_neg_two] at hc
    norm_num at hc

lemma zeta_power_power_mod_five (c : ℂ) (hc : c ^ 2 + c = 1) (k n : ℕ) :
    (zeta c ^ k) ^ n = zeta c ^ ((k * n) % 5) := by
  rw [← pow_mul, pow_eq_pow_mod (k * n) (zeta_pow_five c hc)]

lemma zeta_pow_four_eq_inv (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c ^ 4 = (zeta c)⁻¹ := by
  apply (mul_left_cancel₀ (zeta_ne_zero c))
  rw [mul_inv_cancel₀ (zeta_ne_zero c)]
  calc
    zeta c * zeta c ^ 4 = zeta c ^ 5 := by ring
    _ = 1 := zeta_pow_five c hc

lemma zeta_pow_three_sub_pow_two (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c ^ 3 - zeta c ^ 2 = -c * (zeta c - (zeta c)⁻¹) := by
  have hinv_sq : (zeta c)⁻¹ ^ 2 = zeta c ^ 3 := by
    field_simp [zeta_ne_zero c]
    simpa using (zeta_pow_five c hc).symm
  calc
    zeta c ^ 3 - zeta c ^ 2 = (zeta c)⁻¹ ^ 2 - zeta c ^ 2 := by rw [hinv_sq]
    _ = -(zeta c + (zeta c)⁻¹) * (zeta c - (zeta c)⁻¹) := by ring
    _ = -c * (zeta c - (zeta c)⁻¹) := by rw [zeta_add_inv c]

lemma zeta_pow_three_sub_pow_two' (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c ^ 3 - zeta c ^ 2 = -c * (zeta c - zeta c ^ 4) := by
  rw [zeta_pow_four_eq_inv c hc]
  exact zeta_pow_three_sub_pow_two c hc

lemma zeta_pow_two_add_inv_pow_two (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c ^ 2 + (zeta c)⁻¹ ^ 2 = -1 - c := by
  have hz := zeta_ne_zero c
  calc
    zeta c ^ 2 + (zeta c)⁻¹ ^ 2 = (zeta c + (zeta c)⁻¹) ^ 2 - 2 := by
      field_simp [hz]
      ring
    _ = c ^ 2 - 2 := by rw [zeta_add_inv]
    _ = -1 - c := by linear_combination hc

lemma zeta_pow_three_add_inv_pow_three (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c ^ 3 + (zeta c)⁻¹ ^ 3 = -1 - c := by
  rw [← zeta_pow_two_add_inv_pow_two c hc]
  have hz := zeta_ne_zero c
  have hz5 := zeta_pow_five c hc
  field_simp [hz]
  calc
    zeta c ^ 6 + 1 = zeta c * zeta c ^ 5 + 1 := by ring
    _ = zeta c + 1 := by rw [hz5]; ring
    _ = zeta c * (zeta c ^ 4 + 1) := by
      rw [mul_add, show zeta c * zeta c ^ 4 = zeta c ^ 5 by ring, hz5]
      ring

lemma zeta_pow_four_add_inv_pow_four (c : ℂ) (hc : c ^ 2 + c = 1) :
    zeta c ^ 4 + (zeta c)⁻¹ ^ 4 = c := by
  have hz := zeta_ne_zero c
  have hz5 := zeta_pow_five c hc
  calc
    zeta c ^ 4 + (zeta c)⁻¹ ^ 4 = zeta c + (zeta c)⁻¹ := by
      field_simp [hz]
      calc
        zeta c ^ 8 + 1 = zeta c ^ 3 * zeta c ^ 5 + 1 := by ring
        _ = zeta c ^ 3 + 1 := by rw [hz5]; ring
        _ = zeta c ^ 3 * (zeta c ^ 2 + 1) := by
          rw [mul_add, show zeta c ^ 3 * zeta c ^ 2 = zeta c ^ 5 by ring, hz5]
          ring
    _ = c := zeta_add_inv c

lemma s_eq_zeta_pow_add_inv_pow (c : ℂ) (hc : c ^ 2 + c = 1) (n : ℕ) :
    s c n = zeta c ^ n + (zeta c)⁻¹ ^ n := by
  have hz5 := zeta_pow_five c hc
  have hz5inv : (zeta c)⁻¹ ^ 5 = 1 := by simp [hz5]
  rw [pow_eq_pow_mod n hz5, pow_eq_pow_mod n hz5inv]
  have hn : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 5
  · norm_num [s, h]
  · simpa only [s, h, pow_one] using (zeta_add_inv c).symm
  · simpa only [s, h] using (zeta_pow_two_add_inv_pow_two c hc).symm
  · simpa only [s, h] using (zeta_pow_three_add_inv_pow_three c hc).symm
  · simpa only [s, h] using (zeta_pow_four_add_inv_pow_four c hc).symm

lemma zeta_delta_mul_eta (c : ℂ) (hc : c ^ 2 + c = 1) (n : ℕ) :
    (zeta c - zeta c ^ 4) * eta c n =
      zeta c ^ (n % 5) - zeta c ^ ((4 * n) % 5) := by
  have hn : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hdiff := zeta_pow_three_sub_pow_two' c hc
  interval_cases h : n % 5
  · simp [eta, h, Nat.mul_mod]
  · simp [eta, h, Nat.mul_mod]
  · simp [eta, h, Nat.mul_mod]
    linear_combination hdiff
  · simp [eta, h, Nat.mul_mod]
    linear_combination -hdiff
  · simp [eta, h, Nat.mul_mod]

/-- The relation `gₙ` from equation (4). -/
noncomputable def g (c : ℂ) (n : ℕ) : S :=
  C (s c n - c) * x n +
    ∑ i ∈ (Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n),
      C (s c (n - 2 * i)) * x i * x (n - i) +
    if 2 ∣ n then x (n / 2) ^ 2 else 0

noncomputable def generatingCoefficient (n : ℕ) : S :=
  if n = 0 then 1 else x n

/-- The generating series `1 + ∑ xₙtⁿ` used to package the periodic relations. -/
noncomputable def generatingSeries : PowerSeries S :=
  PowerSeries.mk generatingCoefficient

@[simp]
lemma coeff_generatingSeries (n : ℕ) :
    PowerSeries.coeff n generatingSeries = if n = 0 then 1 else x n := by
  simp [generatingSeries, generatingCoefficient]

/-- The series whose coefficient of `tⁿ`, for `n ≥ 2`, is `gₙ`. -/
noncomputable def relationSeries (c : ℂ) : PowerSeries S :=
  PowerSeries.rescale (C (zeta c)⁻¹) generatingSeries *
      PowerSeries.rescale (C (zeta c)) generatingSeries -
    (PowerSeries.C (C (1 - c)) + PowerSeries.C (C c) * generatingSeries)

lemma sum_range_two_mul_add_two {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m + 2), f i =
      ∑ i ∈ Finset.range (m + 1), (f i + f (2 * m + 1 - i)) := by
  rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, Finset.sum_range_add,
    Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [Finset.mem_range] at hi
  omega

lemma sum_range_two_mul_add_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m + 1), f i =
      f m + ∑ i ∈ Finset.range m, (f i + f (2 * m - i)) := by
  have hu : ∑ i ∈ Finset.range m, f (m + (i + 1)) =
      ∑ i ∈ Finset.range m, f (2 * m - i) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp only [Finset.mem_range] at hi
    omega
  rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ', Finset.sum_add_distrib, hu]
  abel

lemma zeta_pair_factor (c : ℂ) {n i : ℕ} (hi : 2 * i ≤ n) :
    (zeta c)⁻¹ ^ i * zeta c ^ (n - i) + (zeta c)⁻¹ ^ (n - i) * zeta c ^ i =
      zeta c ^ (n - 2 * i) + (zeta c)⁻¹ ^ (n - 2 * i) := by
  have hz := zeta_ne_zero c
  have hii : i ≤ n - i := by omega
  have hsub : n - i - i = n - 2 * i := by omega
  have hfirst : (zeta c)⁻¹ ^ i * zeta c ^ (n - i) = zeta c ^ (n - 2 * i) := by
    rw [inv_pow, mul_comm, ← pow_sub₀ _ hz hii, hsub]
  have hsecond : (zeta c)⁻¹ ^ (n - i) * zeta c ^ i =
      (zeta c)⁻¹ ^ (n - 2 * i) := by
    calc
      (zeta c)⁻¹ ^ (n - i) * zeta c ^ i =
          (zeta c ^ (n - i))⁻¹ * zeta c ^ i := by rw [inv_pow]
      _ = (zeta c ^ (n - i) * (zeta c ^ i)⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_comm]
      _ = (zeta c ^ (n - i - i))⁻¹ := by rw [pow_sub₀ _ hz hii]
      _ = (zeta c)⁻¹ ^ (n - 2 * i) := by rw [hsub, inv_pow]
  rw [hfirst, hsecond]

noncomputable def convolutionTerm (c : ℂ) (n i : ℕ) : S :=
  C (zeta c)⁻¹ ^ i * generatingCoefficient i *
    (C (zeta c) ^ (n - i) * generatingCoefficient (n - i))

lemma convolutionTerm_pair (c : ℂ) (hc : c ^ 2 + c = 1) {n i : ℕ}
    (hi0 : 0 < i) (hi : 2 * i < n) :
    convolutionTerm c n i + convolutionTerm c n (n - i) =
      C (s c (n - 2 * i)) * x i * x (n - i) := by
  have hin : i < n := by omega
  have hni0 : n - i ≠ 0 := by omega
  have hsub : n - (n - i) = i := by omega
  have hfac := zeta_pair_factor c (show 2 * i ≤ n by omega)
  have hfac' : (zeta c)⁻¹ ^ i * zeta c ^ (n - i) +
      (zeta c)⁻¹ ^ (n - i) * zeta c ^ i = s c (n - 2 * i) := by
    rw [s_eq_zeta_pow_add_inv_pow c hc]
    exact hfac
  have hfacC := congrArg (C (σ := ℕ+)) hfac'
  simp only [map_add, map_mul] at hfacC
  simp only [convolutionTerm, generatingCoefficient, hi0.ne', ite_false, hni0, hsub,
    ← map_pow]
  calc
    C ((zeta c)⁻¹ ^ i) * x i * (C (zeta c ^ (n - i)) * x (n - i)) +
        C ((zeta c)⁻¹ ^ (n - i)) * x (n - i) * (C (zeta c ^ i) * x i) =
      (C ((zeta c)⁻¹ ^ i) * C (zeta c ^ (n - i)) +
        C ((zeta c)⁻¹ ^ (n - i)) * C (zeta c ^ i)) * x i * x (n - i) := by ring
    _ = C (s c (n - 2 * i)) * x i * x (n - i) := by rw [hfacC]

lemma convolutionTerm_endpoints (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ} (hn : n ≠ 0) :
    convolutionTerm c n 0 + convolutionTerm c n n = C (s c n) * x n := by
  rw [s_eq_zeta_pow_add_inv_pow c hc]
  simp only [convolutionTerm, generatingCoefficient, if_pos, hn, ite_false, Nat.sub_zero,
    Nat.sub_self, pow_zero, map_one, one_mul, mul_one, ← map_pow, ← map_add]
  rw [inv_pow]
  rw [map_add]
  ring

lemma convolutionTerm_middle (c : ℂ) {m : ℕ} (hm : m ≠ 0) :
    convolutionTerm c (2 * m) m = x m ^ 2 := by
  have hz := zeta_ne_zero c
  simp only [convolutionTerm, generatingCoefficient]
  rw [show 2 * m - m = m by omega]
  simp only [hm, ite_false, ← map_pow]
  calc
    C ((zeta c)⁻¹ ^ m) * x m * (C (zeta c ^ m) * x m) =
        (C ((zeta c)⁻¹ ^ m) * C (zeta c ^ m)) * x m ^ 2 := by ring
    _ = x m ^ 2 := by rw [← map_mul]; simp [hz]

noncomputable def constantConvolutionTerm (c : ℂ) (n i : ℕ) : S :=
  (if i = 0 then C c else 0) * generatingCoefficient (n - i)

lemma sum_constantConvolutionTerm (c : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ Finset.range (n + 1), constantConvolutionTerm c n i = C c * x n := by
  rw [Finset.sum_eq_single 0]
  · simp [constantConvolutionTerm, generatingCoefficient, hn]
  · intro i hi hi0
    simp [constantConvolutionTerm, hi0]
  · simp

lemma coeff_relationSeries (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (relationSeries c) = g c n := by
  have hn0 : n ≠ 0 := by omega
  simp only [relationSeries, map_sub, map_add, PowerSeries.coeff_mul,
    PowerSeries.coeff_rescale, coeff_generatingSeries, PowerSeries.coeff_C]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.fst, Prod.snd, Nat.succ_eq_add_one, ← map_sub]
  change (∑ i ∈ Finset.range (n + 1), convolutionTerm c n i) -
      (((if n = 0 then C 1 else 0) - (if n = 0 then C c else 0)) +
        ∑ i ∈ Finset.range (n + 1), constantConvolutionTerm c n i) = g c n
  rw [sum_constantConvolutionTerm c hn0]
  simp only [hn0, ite_false, zero_add]
  have hconv : ∑ i ∈ Finset.range (n + 1), convolutionTerm c n i =
      C (s c n) * x n +
        ∑ i ∈ (Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n),
          C (s c (n - 2 * i)) * x i * x (n - i) +
        if 2 ∣ n then x (n / 2) ^ 2 else 0 := by
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hm0 : m ≠ 0 := by omega
      rw [sum_range_two_mul_add_one]
      have hmem : 0 ∈ Finset.range m := by simp [Nat.pos_of_ne_zero hm0]
      rw [← Finset.sum_erase_add (Finset.range m)
        (fun i ↦ convolutionTerm c (2 * m) i + convolutionTerm c (2 * m) (2 * m - i))
        hmem]
      have herase : (Finset.range m).erase 0 =
          (Finset.range (2 * m)).filter (fun i ↦ 0 < i ∧ 2 * i < 2 * m) := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_filter]
        omega
      rw [herase]
      have hpairs :
          ∑ i ∈ (Finset.range (2 * m)).filter (fun i ↦ 0 < i ∧ 2 * i < 2 * m),
              (convolutionTerm c (2 * m) i + convolutionTerm c (2 * m) (2 * m - i)) =
            ∑ i ∈ (Finset.range (2 * m)).filter (fun i ↦ 0 < i ∧ 2 * i < 2 * m),
              C (s c (2 * m - 2 * i)) * x i * x (2 * m - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter] at hi
        exact convolutionTerm_pair c hc hi.2.1 hi.2.2
      rw [hpairs]
      simp only [Nat.sub_zero]
      rw [convolutionTerm_endpoints c hc (by omega), convolutionTerm_middle c hm0]
      simp only [Nat.reduceDiv, dvd_mul_right, if_true]
      have hdiv : 2 * m / 2 = m := by omega
      rw [hdiv]
      ring
    · rw [sum_range_two_mul_add_two]
      have hmem : 0 ∈ Finset.range (m + 1) := by simp
      rw [← Finset.sum_erase_add (Finset.range (m + 1))
        (fun i ↦ convolutionTerm c (2 * m + 1) i +
          convolutionTerm c (2 * m + 1) (2 * m + 1 - i)) hmem]
      have herase : (Finset.range (m + 1)).erase 0 =
          (Finset.range (2 * m + 1)).filter
            (fun i ↦ 0 < i ∧ 2 * i < 2 * m + 1) := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_filter]
        omega
      rw [herase]
      have hpairs :
          ∑ i ∈ (Finset.range (2 * m + 1)).filter
              (fun i ↦ 0 < i ∧ 2 * i < 2 * m + 1),
              (convolutionTerm c (2 * m + 1) i +
                convolutionTerm c (2 * m + 1) (2 * m + 1 - i)) =
            ∑ i ∈ (Finset.range (2 * m + 1)).filter
              (fun i ↦ 0 < i ∧ 2 * i < 2 * m + 1),
              C (s c (2 * m + 1 - 2 * i)) * x i * x (2 * m + 1 - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter] at hi
        exact convolutionTerm_pair c hc hi.2.1 hi.2.2
      rw [hpairs]
      simp only [Nat.sub_zero]
      rw [convolutionTerm_endpoints c hc (by omega)]
      rw [if_neg (by omega : ¬2 ∣ 2 * m + 1)]
      ring
  rw [hconv]
  simp only [g]
  rw [map_sub]
  ring

noncomputable def normalizedGeneratingSeries (c : ℂ) : PowerSeries S :=
  PowerSeries.C (C c⁻¹) * generatingSeries

noncomputable def rotatedGeneratingSeries (c a : ℂ) : PowerSeries S :=
  PowerSeries.rescale (C a) (normalizedGeneratingSeries c)

noncomputable def normalizedErrorSeries (c : ℂ) : PowerSeries S :=
  rotatedGeneratingSeries c (zeta c)⁻¹ * rotatedGeneratingSeries c (zeta c) - 1 -
    normalizedGeneratingSeries c

noncomputable def rotatedErrorSeries (c a : ℂ) : PowerSeries S :=
  PowerSeries.rescale (C a) (normalizedErrorSeries c)

lemma inv_sq_mul_one_sub (c : ℂ) (hc : c ^ 2 + c = 1) : c⁻¹ ^ 2 * (1 - c) = 1 := by
  have hc0 := ne_zero_of_quadratic c hc
  field_simp [hc0]
  linear_combination -hc

lemma inv_sq_mul_self (c : ℂ) (hc : c ^ 2 + c = 1) : c⁻¹ ^ 2 * c = c⁻¹ := by
  field_simp [ne_zero_of_quadratic c hc]

lemma rotatedGeneratingSeries_eq (c a : ℂ) :
    rotatedGeneratingSeries c a =
      PowerSeries.C (C c⁻¹) * PowerSeries.rescale (C a) generatingSeries := by
  have hconstant : PowerSeries.rescale (C a) (PowerSeries.C (C c⁻¹) : PowerSeries S) =
      PowerSeries.C (C c⁻¹) := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    by_cases hn : n = 0 <;> simp [hn]
  rw [rotatedGeneratingSeries, normalizedGeneratingSeries, map_mul, hconstant]

lemma normalizedErrorSeries_eq (c : ℂ) (hc : c ^ 2 + c = 1) :
    normalizedErrorSeries c =
      PowerSeries.C (C c⁻¹) ^ 2 * relationSeries c := by
  rw [normalizedErrorSeries, rotatedGeneratingSeries_eq, rotatedGeneratingSeries_eq,
    relationSeries, normalizedGeneratingSeries]
  let A : PowerSeries S := PowerSeries.C (C c⁻¹)
  let U : PowerSeries S := PowerSeries.rescale (C (zeta c)⁻¹) generatingSeries
  let V : PowerSeries S := PowerSeries.rescale (C (zeta c)) generatingSeries
  let B : PowerSeries S := PowerSeries.C (C (1 - c))
  let D : PowerSeries S := PowerSeries.C (C c)
  let F : PowerSeries S := generatingSeries
  change A * U * (A * V) - 1 - A * F = A ^ 2 * (U * V - (B + D * F))
  have hconst : A ^ 2 * B = 1 := by
    dsimp only [A, B]
    rw [← map_pow, ← map_mul, ← map_pow, ← map_mul, inv_sq_mul_one_sub c hc,
      map_one, map_one]
  have hlinear : A ^ 2 * D = A := by
    dsimp only [A, D]
    rw [← map_pow, ← map_mul, ← map_pow, ← map_mul, inv_sq_mul_self c hc]
  calc
    A * U * (A * V) - 1 - A * F = A ^ 2 * (U * V) - A ^ 2 * B - (A ^ 2 * D) * F := by
      rw [hconst, hlinear]
      ring
    _ = A ^ 2 * (U * V - (B + D * F)) := by ring

lemma rotatedErrorSeries_eq (c a : ℂ) :
    rotatedErrorSeries c a =
      rotatedGeneratingSeries c ((zeta c)⁻¹ * a) *
          rotatedGeneratingSeries c (zeta c * a) - 1 -
        rotatedGeneratingSeries c a := by
  simp only [rotatedErrorSeries, normalizedErrorSeries, map_sub, map_mul, map_one,
    rotatedGeneratingSeries, normalizedGeneratingSeries, PowerSeries.rescale_rescale]

lemma pentagon_syzygy_series (c : ℂ) (hc : c ^ 2 + c = 1) :
    rotatedGeneratingSeries c (zeta c ^ 2) * rotatedErrorSeries c (zeta c ^ 4) -
          rotatedGeneratingSeries c (zeta c ^ 3) * rotatedErrorSeries c (zeta c) -
        rotatedErrorSeries c (zeta c ^ 2) + rotatedErrorSeries c (zeta c ^ 3) = 0 := by
  have hz := zeta_ne_zero c
  have hz5 := zeta_pow_five c hc
  rw [rotatedErrorSeries_eq, rotatedErrorSeries_eq, rotatedErrorSeries_eq,
    rotatedErrorSeries_eq]
  simp only [pow_two, pow_succ]
  field_simp [hz]
  simp only [hz5]
  ring

lemma coeff_rotatedGeneratingSeries (c a : ℂ) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (rotatedGeneratingSeries c a) = C (c⁻¹ * a ^ n) * x n := by
  simp only [rotatedGeneratingSeries, PowerSeries.coeff_rescale, normalizedGeneratingSeries,
    PowerSeries.coeff_C_mul, coeff_generatingSeries, hn, ite_false, ← map_pow, ← map_mul]
  rw [map_mul]
  ring

lemma coeff_zero_rotatedGeneratingSeries (c a : ℂ) :
    PowerSeries.coeff 0 (rotatedGeneratingSeries c a) = C c⁻¹ := by
  rw [rotatedGeneratingSeries_eq, PowerSeries.coeff_C_mul]
  simp

lemma coeff_rotatedErrorSeries (c a : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (rotatedErrorSeries c a) = C (a ^ n * c⁻¹ ^ 2) * g c n := by
  rw [rotatedErrorSeries, normalizedErrorSeries_eq c hc]
  rw [← map_pow (PowerSeries.C : S →+* PowerSeries S)]
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_relationSeries c hc hn]
  simp only [← map_pow, ← map_mul]
  rw [map_mul]
  ring

lemma coeff_zero_normalizedErrorSeries (c : ℂ) (hc : c ^ 2 + c = 1) :
    PowerSeries.coeff 0 (normalizedErrorSeries c) = 0 := by
  have hinv : c⁻¹ * c⁻¹ - 1 - c⁻¹ = 0 := by
    field_simp [ne_zero_of_quadratic c hc]
    linear_combination -hc
  rw [normalizedErrorSeries]
  simp only [map_sub]
  simp [PowerSeries.coeff_mul, coeff_zero_rotatedGeneratingSeries,
    normalizedGeneratingSeries, PowerSeries.coeff_C_mul]
  simpa only [map_sub, map_mul, map_one, map_zero] using
    congrArg (C (σ := ℕ+)) hinv

lemma coeff_zero_rotatedErrorSeries (c a : ℂ) (hc : c ^ 2 + c = 1) :
    PowerSeries.coeff 0 (rotatedErrorSeries c a) = 0 := by
  simp [rotatedErrorSeries, coeff_zero_normalizedErrorSeries c hc]

noncomputable def pentagonMainCoefficient (c : ℂ) (n : ℕ) : ℂ :=
  c⁻¹ * ((zeta c ^ 4) ^ n * c⁻¹ ^ 2) -
      c⁻¹ * (zeta c ^ n * c⁻¹ ^ 2) -
    (zeta c ^ 2) ^ n * c⁻¹ ^ 2 + (zeta c ^ 3) ^ n * c⁻¹ ^ 2

lemma g_one (c : ℂ) : g c 1 = 0 := by
  simp [g, s, x]

lemma pentagon_syzygy_coefficient (c : ℂ) (hc : c ^ 2 + c = 1) (N : ℕ) :
    PowerSeries.coeff N
        (rotatedGeneratingSeries c (zeta c ^ 2) * rotatedErrorSeries c (zeta c ^ 4)) -
      PowerSeries.coeff N
        (rotatedGeneratingSeries c (zeta c ^ 3) * rotatedErrorSeries c (zeta c)) -
      PowerSeries.coeff N (rotatedErrorSeries c (zeta c ^ 2)) +
      PowerSeries.coeff N (rotatedErrorSeries c (zeta c ^ 3)) = 0 := by
  have h := congrArg (PowerSeries.coeff N) (pentagon_syzygy_series c hc)
  simpa only [map_sub, map_add, map_zero] using h

noncomputable def pentagonProductTerm (c : ℂ) (N r : ℕ) : S :=
  PowerSeries.coeff r (rotatedGeneratingSeries c (zeta c ^ 2)) *
      PowerSeries.coeff (N - r) (rotatedErrorSeries c (zeta c ^ 4)) -
    PowerSeries.coeff r (rotatedGeneratingSeries c (zeta c ^ 3)) *
      PowerSeries.coeff (N - r) (rotatedErrorSeries c (zeta c))

noncomputable def pentagonTermCoefficient (c : ℂ) (N r : ℕ) : ℂ :=
  (c⁻¹ * (zeta c ^ 2) ^ r) * ((zeta c ^ 4) ^ (N - r) * c⁻¹ ^ 2) -
    (c⁻¹ * (zeta c ^ 3) ^ r) * (zeta c ^ (N - r) * c⁻¹ ^ 2)

lemma pentagonProductTerm_eq (c : ℂ) (hc : c ^ 2 + c = 1) {N r : ℕ}
    (hr : 1 ≤ r) (hrN : r + 2 ≤ N) :
    pentagonProductTerm c N r =
      C (pentagonTermCoefficient c N r) * x r * g c (N - r) := by
  have hr0 : r ≠ 0 := by omega
  have hdiff : 1 ≤ N - r := by omega
  rw [pentagonProductTerm, coeff_rotatedGeneratingSeries c (zeta c ^ 2) hr0,
    coeff_rotatedGeneratingSeries c (zeta c ^ 3) hr0,
    coeff_rotatedErrorSeries c (zeta c ^ 4) hc hdiff,
    coeff_rotatedErrorSeries c (zeta c) hc hdiff]
  simp only [pentagonTermCoefficient, map_mul, map_sub, map_pow]
  ring

lemma pentagonTermCoefficient_eq_eta (c : ℂ) (hc : c ^ 2 + c = 1)
    {N r : ℕ} (hrN : r ≤ N) :
    pentagonTermCoefficient c N r =
      (zeta c - zeta c ^ 4) * c⁻¹ ^ 3 * eta c (4 * N - 2 * r) := by
  have hfirst : (zeta c ^ 2) ^ r * (zeta c ^ 4) ^ (N - r) =
      zeta c ^ (4 * N - 2 * r) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hsecond : (zeta c ^ 3) ^ r * zeta c ^ (N - r) =
      zeta c ^ (N + 2 * r) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hmods : (N + 2 * r) % 5 = (4 * (4 * N - 2 * r)) % 5 := by
    omega
  calc
    pentagonTermCoefficient c N r = c⁻¹ ^ 3 *
        ((zeta c ^ 2) ^ r * (zeta c ^ 4) ^ (N - r) -
          (zeta c ^ 3) ^ r * zeta c ^ (N - r)) := by
      unfold pentagonTermCoefficient
      ring
    _ = c⁻¹ ^ 3 * (zeta c ^ (4 * N - 2 * r) - zeta c ^ (N + 2 * r)) := by
      rw [hfirst, hsecond]
    _ = c⁻¹ ^ 3 *
        (zeta c ^ ((4 * N - 2 * r) % 5) -
          zeta c ^ ((4 * (4 * N - 2 * r)) % 5)) := by
      rw [pow_eq_pow_mod (4 * N - 2 * r) (zeta_pow_five c hc),
        pow_eq_pow_mod (N + 2 * r) (zeta_pow_five c hc), hmods]
    _ = (zeta c - zeta c ^ 4) * c⁻¹ ^ 3 * eta c (4 * N - 2 * r) := by
      rw [← zeta_delta_mul_eta c hc (4 * N - 2 * r)]
      ring

lemma eta_family_one_left (c : ℂ) (m : ℕ) :
    eta c (4 * (3 * m + 1) - 2 * m) = -1 := by
  have hmod : (4 * (3 * m + 1) - 2 * m) % 5 = 4 := by omega
  simp [eta, hmod]

lemma eta_family_one_right (c : ℂ) (m : ℕ) :
    eta c (4 * (3 * m + 1) - 2 * (m + 1)) = c := by
  have hmod : (4 * (3 * m + 1) - 2 * (m + 1)) % 5 = 2 := by omega
  simp [eta, hmod]

lemma eta_family_two_left (c : ℂ) (m : ℕ) :
    eta c (4 * (3 * m + 2) - 2 * m) = -c := by
  have hmod : (4 * (3 * m + 2) - 2 * m) % 5 = 3 := by omega
  simp [eta, hmod]

lemma eta_family_two_right (c : ℂ) (m : ℕ) :
    eta c (4 * (3 * m + 2) - 2 * (m + 1)) = 1 := by
  have hmod : (4 * (3 * m + 2) - 2 * (m + 1)) % 5 = 1 := by omega
  simp [eta, hmod]

lemma eta_family_three_center (c : ℂ) (m : ℕ) :
    eta c (4 * (3 * m) - 2 * m) = 0 := by
  have hmod : (4 * (3 * m) - 2 * m) % 5 = 0 := by omega
  simp [eta, hmod]

lemma eta_family_three_left (c : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    eta c (4 * (3 * m) - 2 * (m - 1)) = c := by
  have hmod : (4 * (3 * m) - 2 * (m - 1)) % 5 = 2 := by omega
  simp [eta, hmod]

lemma eta_family_three_right (c : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    eta c (4 * (3 * m) - 2 * (m + 1)) = -c := by
  have hmod : (4 * (3 * m) - 2 * (m + 1)) % 5 = 3 := by omega
  simp [eta, hmod]

lemma pentagonProductTerm_zero_add_errors (c : ℂ) (hc : c ^ 2 + c = 1)
    {N : ℕ} (hN : 1 ≤ N) :
    pentagonProductTerm c N 0 -
        PowerSeries.coeff N (rotatedErrorSeries c (zeta c ^ 2)) +
      PowerSeries.coeff N (rotatedErrorSeries c (zeta c ^ 3)) =
        C (pentagonMainCoefficient c N) * g c N := by
  rw [pentagonProductTerm, Nat.sub_zero,
    coeff_zero_rotatedGeneratingSeries, coeff_zero_rotatedGeneratingSeries,
    coeff_rotatedErrorSeries c (zeta c ^ 4) hc hN,
    coeff_rotatedErrorSeries c (zeta c) hc hN,
    coeff_rotatedErrorSeries c (zeta c ^ 2) hc hN,
    coeff_rotatedErrorSeries c (zeta c ^ 3) hc hN]
  simp only [pentagonMainCoefficient, map_mul, map_sub, map_add, map_pow]
  ring

lemma pentagonProductTerm_last (c : ℂ) (hc : c ^ 2 + c = 1) {N : ℕ}
    (hN : 1 ≤ N) : pentagonProductTerm c N N = 0 := by
  rw [pentagonProductTerm, Nat.sub_self,
    coeff_zero_rotatedErrorSeries c (zeta c ^ 4) hc,
    coeff_zero_rotatedErrorSeries c (zeta c) hc]
  ring

lemma pentagonProductTerm_penultimate (c : ℂ) (hc : c ^ 2 + c = 1) {N : ℕ}
    (hN : 2 ≤ N) : pentagonProductTerm c N (N - 1) = 0 := by
  have hpos : 0 < N := by omega
  have hindex : N - (N - 1) = 1 := by omega
  rw [pentagonProductTerm, hindex,
    coeff_rotatedErrorSeries c (zeta c ^ 4) hc (by omega),
    coeff_rotatedErrorSeries c (zeta c) hc (by omega), g_one]
  ring

lemma pentagon_syzygy_sum_range (c : ℂ) (hc : c ^ 2 + c = 1) (N : ℕ) :
    (∑ r ∈ Finset.range (N + 1), pentagonProductTerm c N r) -
        PowerSeries.coeff N (rotatedErrorSeries c (zeta c ^ 2)) +
      PowerSeries.coeff N (rotatedErrorSeries c (zeta c ^ 3)) = 0 := by
  simp only [pentagonProductTerm, Finset.sum_sub_distrib]
  simpa only [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
    pentagon_syzygy_coefficient c hc N

lemma pentagon_syzygy_finite (c : ℂ) (hc : c ^ 2 + c = 1) {N : ℕ}
    (hN : 2 ≤ N) :
    C (pentagonMainCoefficient c N) * g c N +
        ∑ r ∈ (Finset.range (N - 1)).erase 0,
          C (pentagonTermCoefficient c N r) * x r * g c (N - r) = 0 := by
  have h := pentagon_syzygy_sum_range c hc N
  rw [Finset.sum_range_succ, pentagonProductTerm_last c hc (by omega), add_zero] at h
  have hrange : Finset.range N = Finset.range ((N - 1) + 1) := by
    congr 1
    omega
  rw [hrange, Finset.sum_range_succ,
    pentagonProductTerm_penultimate c hc hN, add_zero] at h
  have hzero : 0 ∈ Finset.range (N - 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ hzero] at h
  have hmiddle :
      ∑ r ∈ (Finset.range (N - 1)).erase 0, pentagonProductTerm c N r =
        ∑ r ∈ (Finset.range (N - 1)).erase 0,
          C (pentagonTermCoefficient c N r) * x r * g c (N - r) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_erase, Finset.mem_range] at hr
    exact pentagonProductTerm_eq c hc (by omega) (by omega)
  rw [hmiddle] at h
  have hmain := pentagonProductTerm_zero_add_errors c hc (N := N) (by omega)
  linear_combination h - hmain

lemma coeff_mul_sub_constant_mem (K : Ideal S) (A E : PowerSeries S) (n : ℕ)
    (hzero : PowerSeries.coeff 0 E = 0)
    (hlower : ∀ j, 1 ≤ j → j < n → PowerSeries.coeff j E ∈ K) :
    PowerSeries.coeff n (A * E) -
        PowerSeries.coeff 0 A * PowerSeries.coeff n E ∈ K := by
  rw [PowerSeries.coeff_mul]
  have hmem : (0, n) ∈ Finset.HasAntidiagonal.antidiagonal n := by
    simp [Finset.mem_antidiagonal]
  rw [← Finset.sum_erase_add _ _ hmem]
  have hsum :
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
          PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 E ∈ K := by
    apply K.sum_mem
    intro p hp
    simp only [Finset.mem_erase] at hp
    have hadd : p.1 + p.2 = n := by simpa using hp.2
    by_cases hpzero : p.2 = 0
    · rw [hpzero, hzero, mul_zero]
      exact K.zero_mem
    · apply K.mul_mem_left
      apply hlower p.2 (Nat.one_le_iff_ne_zero.mpr hpzero)
      have hpfirst : p.1 ≠ 0 := by
        intro hfirst
        apply hp.1
        apply Prod.ext
        · exact hfirst
        · omega
      omega
  simpa using hsum

lemma pentagonMainCoefficient_of_mod_one (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 1) :
    pentagonMainCoefficient c n =
      -(zeta c - zeta c ^ 4) * c⁻¹ ^ 3 * (2 - c) := by
  have hkn (k : ℕ) : (k * n) % 5 = (k * 1) % 5 := by
    simp [Nat.mul_mod, hn]
  simp only [pentagonMainCoefficient, zeta_power_power_mod_five c hc]
  rw [pow_eq_pow_mod n (zeta_pow_five c hc), hn, hkn 4, hkn 2, hkn 3]
  norm_num
  have hdiff := zeta_pow_three_sub_pow_two' c hc
  field_simp [ne_zero_of_quadratic c hc]
  ring_nf at hdiff ⊢
  linear_combination hdiff * c - hc * (zeta c - zeta c ^ 4)

lemma pentagonMainCoefficient_of_mod_four (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 4) :
    pentagonMainCoefficient c n =
      (zeta c - zeta c ^ 4) * c⁻¹ ^ 3 * (2 - c) := by
  have hkn (k : ℕ) : (k * n) % 5 = (k * 4) % 5 := by
    simp [Nat.mul_mod, hn]
  simp only [pentagonMainCoefficient, zeta_power_power_mod_five c hc]
  rw [pow_eq_pow_mod n (zeta_pow_five c hc), hn, hkn 4, hkn 2, hkn 3]
  norm_num
  have hdiff := zeta_pow_three_sub_pow_two' c hc
  field_simp [ne_zero_of_quadratic c hc]
  ring_nf at hdiff ⊢
  linear_combination -hdiff * c + hc * (zeta c - zeta c ^ 4)

lemma pentagonMainCoefficient_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 1 ∨ n % 5 = 4) : pentagonMainCoefficient c n ≠ 0 := by
  rcases hn with hn | hn
  · rw [pentagonMainCoefficient_of_mod_one c hc hn]
    have hdelta : zeta c - zeta c ^ 4 ≠ 0 := by
      rw [zeta_pow_four_eq_inv c hc]
      exact zeta_sub_inv_ne_zero c hc
    exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr hdelta)
        (pow_ne_zero 3 (inv_ne_zero (ne_zero_of_quadratic c hc))))
      (two_sub_ne_zero c hc)
  · rw [pentagonMainCoefficient_of_mod_four c hc hn]
    have hdelta : zeta c - zeta c ^ 4 ≠ 0 := by
      rw [zeta_pow_four_eq_inv c hc]
      exact zeta_sub_inv_ne_zero c hc
    exact mul_ne_zero
      (mul_ne_zero hdelta
        (pow_ne_zero 3 (inv_ne_zero (ne_zero_of_quadratic c hc))))
      (two_sub_ne_zero c hc)

/-- The non-resonant indices `D` from equation (5). -/
def D : Set ℕ :=
  {n | 2 ≤ n ∧ (n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3)}

/-- The ideal `I = (gₙ : n ∈ D)` from equation (5). -/
noncomputable def I (c : ℂ) : Ideal S :=
  Ideal.span (g c '' D)

lemma all_g_mem_I (c : ℂ) (hc : c ^ 2 + c = 1) (n : ℕ) (hn : 2 ≤ n) :
    g c n ∈ I c := by
  induction n using Nat.strong_induction_on with
  | h N ih =>
      by_cases hD : N % 5 = 0 ∨ N % 5 = 2 ∨ N % 5 = 3
      · apply Ideal.subset_span
        exact ⟨N, ⟨hn, hD⟩, rfl⟩
      · have hres : N % 5 = 1 ∨ N % 5 = 4 := by
          have hlt := Nat.mod_lt N (by norm_num : 0 < 5)
          omega
        let E1 := rotatedErrorSeries c (zeta c)
        let E2 := rotatedErrorSeries c (zeta c ^ 2)
        let E3 := rotatedErrorSeries c (zeta c ^ 3)
        let E4 := rotatedErrorSeries c (zeta c ^ 4)
        let A2 := rotatedGeneratingSeries c (zeta c ^ 2)
        let A3 := rotatedGeneratingSeries c (zeta c ^ 3)
        have hElower (a : ℂ) : ∀ j, 1 ≤ j → j < N →
            PowerSeries.coeff j (rotatedErrorSeries c a) ∈ I c := by
          intro j hjpos hjlt
          rw [coeff_rotatedErrorSeries c a hc hjpos]
          apply (I c).mul_mem_left
          by_cases hjone : j = 1
          · subst j
            rw [g_one]
            exact (I c).zero_mem
          · exact ih j hjlt (by omega)
        have hp2 : PowerSeries.coeff N (A2 * E4) -
              PowerSeries.coeff 0 A2 * PowerSeries.coeff N E4 ∈ I c := by
          apply coeff_mul_sub_constant_mem
          · exact coeff_zero_rotatedErrorSeries c (zeta c ^ 4) hc
          · exact hElower (zeta c ^ 4)
        have hp3 : PowerSeries.coeff N (A3 * E1) -
              PowerSeries.coeff 0 A3 * PowerSeries.coeff N E1 ∈ I c := by
          apply coeff_mul_sub_constant_mem
          · exact coeff_zero_rotatedErrorSeries c (zeta c) hc
          · exact hElower (zeta c)
        have hcoeff := congrArg (PowerSeries.coeff N) (pentagon_syzygy_series c hc)
        change PowerSeries.coeff N (A2 * E4 - A3 * E1 - E2 + E3) =
          PowerSeries.coeff N 0 at hcoeff
        simp only [map_sub, map_add, map_zero] at hcoeff
        have hmain :
            PowerSeries.coeff 0 A2 * PowerSeries.coeff N E4 -
                PowerSeries.coeff 0 A3 * PowerSeries.coeff N E1 -
              PowerSeries.coeff N E2 + PowerSeries.coeff N E3 ∈ I c := by
          have hrem := (I c).sub_mem hp2 hp3
          have hneg := (I c).neg_mem hrem
          convert hneg using 1
          linear_combination hcoeff
        dsimp only [A2, A3, E1, E2, E3, E4] at hmain
        rw [coeff_zero_rotatedGeneratingSeries, coeff_zero_rotatedGeneratingSeries,
          coeff_rotatedErrorSeries c (zeta c ^ 4) hc (by omega),
          coeff_rotatedErrorSeries c (zeta c) hc (by omega),
          coeff_rotatedErrorSeries c (zeta c ^ 2) hc (by omega),
          coeff_rotatedErrorSeries c (zeta c ^ 3) hc (by omega)] at hmain
        have hscalar : C (pentagonMainCoefficient c N) * g c N ∈ I c := by
          have heq : C (pentagonMainCoefficient c N) * g c N =
              C c⁻¹ * (C ((zeta c ^ 4) ^ N * c⁻¹ ^ 2) * g c N) -
                C c⁻¹ * (C (zeta c ^ N * c⁻¹ ^ 2) * g c N) -
              C ((zeta c ^ 2) ^ N * c⁻¹ ^ 2) * g c N +
                C ((zeta c ^ 3) ^ N * c⁻¹ ^ 2) * g c N := by
            simp only [pentagonMainCoefficient, map_sub, map_add, map_mul, map_neg]
            ring
          rw [heq]
          exact hmain
        have hnonzero := pentagonMainCoefficient_ne_zero c hc hres
        have hinv := (I c).mul_mem_left (C ((pentagonMainCoefficient c N)⁻¹)) hscalar
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hnonzero, map_one, one_mul] at hinv
        exact hinv

/-- The successor of a positive integer, used as a variable index. -/
def next (i : ℕ+) : ℕ+ :=
  ⟨(i : ℕ) + 1, Nat.succ_pos i⟩

lemma next_ne_self (i : ℕ+) : next i ≠ i := by
  apply ne_of_gt
  change (i : ℕ) < (i : ℕ) + 1
  exact Nat.lt_succ_self _

/-- The monic family `G` displayed in Theorem 1.1. -/
noncomputable def G (c : ℂ) : Set S :=
  Set.range (fun m : ℕ+ ↦ g c (2 * (m : ℕ))) ∪
    Set.range (fun m : ℕ+ ↦ C c⁻¹ * g c (2 * (m : ℕ) + 1))

noncomputable def normalizedRelation (c : ℂ) (n : ℕ) : S :=
  if 2 ∣ n then g c n else C c⁻¹ * g c n

def normalizationScalar (c : ℂ) (n : ℕ) : ℂ :=
  if 2 ∣ n then 1 else c

noncomputable def pentagonScale (c : ℂ) : ℂ :=
  (zeta c - zeta c ^ 4) * c⁻¹ ^ 3

lemma pentagonScale_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) :
    pentagonScale c ≠ 0 := by
  unfold pentagonScale
  apply mul_ne_zero
  · rw [zeta_pow_four_eq_inv c hc]
    exact zeta_sub_inv_ne_zero c hc
  · exact pow_ne_zero 3 (inv_ne_zero (ne_zero_of_quadratic c hc))

lemma normalizedCoefficient_family_one_left (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : ℕ) :
    pentagonTermCoefficient c (3 * m + 1) m *
        normalizationScalar c (3 * m + 1 - m) = -pentagonScale c * c := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_one_left]
  have hsub : 3 * m + 1 - m = 2 * m + 1 := by omega
  rw [hsub]
  simp [normalizationScalar, pentagonScale]

lemma normalizedCoefficient_family_one_right (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : ℕ) :
    pentagonTermCoefficient c (3 * m + 1) (m + 1) *
        normalizationScalar c (3 * m + 1 - (m + 1)) = pentagonScale c * c := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_one_right]
  have hsub : 3 * m + 1 - (m + 1) = 2 * m := by omega
  rw [hsub]
  simp [normalizationScalar, pentagonScale]

lemma normalizedCoefficient_family_two_left (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : ℕ) :
    pentagonTermCoefficient c (3 * m + 2) m *
        normalizationScalar c (3 * m + 2 - m) = -pentagonScale c * c := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_two_left]
  have hsub : 3 * m + 2 - m = 2 * (m + 1) := by omega
  rw [hsub]
  simp [normalizationScalar, pentagonScale]

lemma normalizedCoefficient_family_two_right (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : ℕ) :
    pentagonTermCoefficient c (3 * m + 2) (m + 1) *
        normalizationScalar c (3 * m + 2 - (m + 1)) = pentagonScale c * c := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_two_right]
  have hsub : 3 * m + 2 - (m + 1) = 2 * m + 1 := by omega
  rw [hsub]
  simp [normalizationScalar, pentagonScale]

lemma normalizedCoefficient_family_three_center (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : ℕ) :
    pentagonTermCoefficient c (3 * m) m *
        normalizationScalar c (3 * m - m) = 0 := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_three_center]
  simp

lemma normalizedCoefficient_family_three_left (c : ℂ) (hc : c ^ 2 + c = 1)
    {m : ℕ} (hm : 1 ≤ m) :
    pentagonTermCoefficient c (3 * m) (m - 1) *
        normalizationScalar c (3 * m - (m - 1)) = pentagonScale c * c ^ 2 := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_three_left c hm]
  have hsub : 3 * m - (m - 1) = 2 * m + 1 := by omega
  rw [hsub]
  simp [normalizationScalar, pentagonScale]
  ring

lemma normalizedCoefficient_family_three_right (c : ℂ) (hc : c ^ 2 + c = 1)
    {m : ℕ} (hm : 1 ≤ m) :
    pentagonTermCoefficient c (3 * m) (m + 1) *
        normalizationScalar c (3 * m - (m + 1)) = -pentagonScale c * c ^ 2 := by
  rw [pentagonTermCoefficient_eq_eta c hc (by omega), eta_family_three_right c hm]
  have hsub : 3 * m - (m + 1) = 2 * m - 1 := by omega
  rw [hsub]
  have hodd : ¬2 ∣ 2 * m - 1 := by omega
  simp [normalizationScalar, hodd, pentagonScale]
  ring

lemma g_eq_normalizationScalar_mul (c : ℂ) (hc : c ^ 2 + c = 1) (n : ℕ) :
    g c n = C (normalizationScalar c n) * normalizedRelation c n := by
  by_cases hn : 2 ∣ n
  · simp [normalizationScalar, normalizedRelation, hn]
  · simp only [normalizationScalar, normalizedRelation, hn, if_false]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (ne_zero_of_quadratic c hc), map_one,
      one_mul]

lemma normalizedRelation_mem_G (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : 2 ≤ n) : normalizedRelation c n ∈ G c := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · have hkpos : 0 < k := by omega
    rw [normalizedRelation, if_pos (by omega), hk]
    exact Or.inl ⟨⟨k, hkpos⟩, rfl⟩
  · have hkpos : 0 < k := by omega
    rw [normalizedRelation, if_neg (by omega), hk]
    exact Or.inr ⟨⟨k, hkpos⟩, rfl⟩

lemma pentagon_syzygy_normalized (c : ℂ) (hc : c ^ 2 + c = 1) {N : ℕ}
    (hN : 2 ≤ N) :
    C (pentagonMainCoefficient c N * normalizationScalar c N) *
        normalizedRelation c N +
      ∑ r ∈ (Finset.range (N - 1)).erase 0,
        C (pentagonTermCoefficient c N r * normalizationScalar c (N - r)) *
          x r * normalizedRelation c (N - r) = 0 := by
  have h := pentagon_syzygy_finite c hc hN
  have hmain : C (pentagonMainCoefficient c N) * g c N =
      C (pentagonMainCoefficient c N * normalizationScalar c N) *
        normalizedRelation c N := by
    rw [g_eq_normalizationScalar_mul c hc N, ← mul_assoc, ← map_mul]
  have hsum :
      ∑ r ∈ (Finset.range (N - 1)).erase 0,
          C (pentagonTermCoefficient c N r) * x r * g c (N - r) =
        ∑ r ∈ (Finset.range (N - 1)).erase 0,
          C (pentagonTermCoefficient c N r * normalizationScalar c (N - r)) *
            x r * normalizedRelation c (N - r) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [g_eq_normalizationScalar_mul c hc (N - r)]
    simp only [map_mul]
    ring
  rw [hmain, hsum] at h
  exact h

lemma G_subset_I (c : ℂ) (hc : c ^ 2 + c = 1) : G c ⊆ I c := by
  intro p hp
  rcases hp with hp | hp
  · obtain ⟨i, rfl⟩ := hp
    exact all_g_mem_I c hc _ (by
      have hi : 0 < (i : ℕ) := i.prop
      nlinarith)
  · obtain ⟨i, rfl⟩ := hp
    apply (I c).mul_mem_left
    exact all_g_mem_I c hc _ (by
      have hi : 0 < (i : ℕ) := i.prop
      nlinarith)

lemma span_G_eq_I (c : ℂ) (hc : c ^ 2 + c = 1) : Ideal.span (G c) = I c := by
  apply le_antisymm
  · rw [Ideal.span_le]
    exact G_subset_I c hc
  · rw [I, Ideal.span_le]
    intro p hp
    obtain ⟨n, hnD, rfl⟩ := hp
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hk : 0 < k := by
        have := hnD.1
        omega
      apply Ideal.subset_span
      left
      exact ⟨⟨k, hk⟩, rfl⟩
    · have hk : 0 < k := by
        have := hnD.1
        omega
      have hnormalized : C c⁻¹ * g c (2 * k + 1) ∈ Ideal.span (G c) := by
        apply Ideal.subset_span
        right
        exact ⟨⟨k, hk⟩, rfl⟩
      have hmul := (Ideal.span (G c)).mul_mem_left (C c) hnormalized
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (ne_zero_of_quadratic c hc),
        map_one, one_mul] at hmul
      change g c (2 * k + 1) ∈ Ideal.span (G c)
      exact hmul

/-- Weighted degree `wt(α) = ∑ i αᵢ`. -/
def weightedDegree (a : ℕ+ →₀ ℕ) : ℕ :=
  a.sum fun i e ↦ (i : ℕ) * e

/-- Second moment `σ(α) = ∑ i² αᵢ`. -/
def secondMoment (a : ℕ+ →₀ ℕ) : ℕ :=
  a.sum fun i e ↦ (i : ℕ) ^ 2 * e

@[simp] lemma weightedDegree_single (i : ℕ+) (e : ℕ) :
    weightedDegree (Finsupp.single i e) = (i : ℕ) * e := by
  simp [weightedDegree]

@[simp] lemma secondMoment_single (i : ℕ+) (e : ℕ) :
    secondMoment (Finsupp.single i e) = (i : ℕ) ^ 2 * e := by
  simp [secondMoment]

lemma weightedDegree_add (a b : ℕ+ →₀ ℕ) :
    weightedDegree (a + b) = weightedDegree a + weightedDegree b := by
  apply Finsupp.sum_add_index' <;> simp [mul_add]

lemma secondMoment_add (a b : ℕ+ →₀ ℕ) :
    secondMoment (a + b) = secondMoment a + secondMoment b := by
  apply Finsupp.sum_add_index' <;> simp [mul_add]

def positiveIndicesUpTo (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).map
    ⟨fun j ↦ ⟨j + 1, Nat.succ_pos j⟩, by
      intro a b h
      have hv : a + 1 = b + 1 := congrArg Subtype.val h
      omega⟩

lemma mem_positiveIndicesUpTo_iff {n : ℕ} {i : ℕ+} :
    i ∈ positiveIndicesUpTo n ↔ (i : ℕ) ≤ n := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp h
    have hjlt : j < n := Finset.mem_range.mp hj
    have hieq : (i : ℕ) = j + 1 := congrArg Subtype.val hji.symm
    omega
  · intro hi
    have hnpos : 0 < n := lt_of_lt_of_le i.prop hi
    apply Finset.mem_map.mpr
    refine ⟨(i : ℕ) - 1, Finset.mem_range.mpr (by omega), ?_⟩
    apply Subtype.ext
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt i.prop))

lemma le_weightedDegree_of_ne_zero {a : ℕ+ →₀ ℕ} {i : ℕ+} (hi : a i ≠ 0) :
    (i : ℕ) ≤ weightedDegree a := by
  classical
  change (i : ℕ) ≤ ∑ j ∈ a.support, (j : ℕ) * a j
  exact le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hi)) <|
    Finset.single_le_sum (s := a.support) (a := i)
      (f := fun j : ℕ+ ↦ (j : ℕ) * a j) (fun _ _ ↦ Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr hi)

lemma value_le_weightedDegree (a : ℕ+ →₀ ℕ) (i : ℕ+) :
    a i ≤ weightedDegree a := by
  by_cases hi : a i = 0
  · simp [hi]
  have hterm : (i : ℕ) * a i ≤ weightedDegree a := by
    classical
    change (i : ℕ) * a i ≤ ∑ j ∈ a.support, (j : ℕ) * a j
    exact Finset.single_le_sum (s := a.support) (a := i)
      (f := fun j : ℕ+ ↦ (j : ℕ) * a j) (fun _ _ ↦ Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr hi)
  exact le_trans (Nat.le_mul_of_pos_left _ i.prop) hterm

lemma finite_weightedDegree_fiber (n : ℕ) :
    Set.Finite {a : ℕ+ →₀ ℕ | weightedDegree a = n} := by
  let candidates : Finset (ℕ+ →₀ ℕ) :=
    (positiveIndicesUpTo n).finsupp (fun _ ↦ Finset.range (n + 1))
  apply candidates.finite_toSet.subset
  intro a ha
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  constructor
  · intro i hi
    rw [mem_positiveIndicesUpTo_iff]
    rw [← ha]
    exact le_weightedDegree_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  · intro i _
    simp only [Finset.mem_range]
    rw [← ha]
    exact Nat.lt_succ_of_le (value_le_weightedDegree a i)

/-- A type synonym carrying the monomial order used in Case I. -/
def CaseIMonomialSyn := ℕ+ →₀ ℕ

/-- The identity equivalence into `CaseIMonomialSyn`. -/
@[match_pattern] def toCaseIMonomialSyn : (ℕ+ →₀ ℕ) ≃ CaseIMonomialSyn := Equiv.refl _

/-- The identity equivalence out of `CaseIMonomialSyn`. -/
@[match_pattern] def ofCaseIMonomialSyn : CaseIMonomialSyn ≃ (ℕ+ →₀ ℕ) := Equiv.refl _

@[simp] lemma ofCaseIMonomialSyn_toCaseIMonomialSyn (a : ℕ+ →₀ ℕ) :
    ofCaseIMonomialSyn (toCaseIMonomialSyn a) = a := rfl

noncomputable instance : AddCommMonoid CaseIMonomialSyn :=
  ofCaseIMonomialSyn.addCommMonoid

lemma toCaseIMonomialSyn_add (a b : ℕ+ →₀ ℕ) :
    toCaseIMonomialSyn (a + b) = toCaseIMonomialSyn a + toCaseIMonomialSyn b := rfl

lemma ofCaseIMonomialSyn_add (a b : CaseIMonomialSyn) :
    ofCaseIMonomialSyn (a + b) = ofCaseIMonomialSyn a + ofCaseIMonomialSyn b := rfl

/-- The comparison key: weight first, reverse second moment next, then lexicographic order. -/
def caseIMonomialKey (a : CaseIMonomialSyn) :
    Lex (ℕ × Lex (OrderDual ℕ × Lex (ℕ+ →₀ ℕ))) :=
  toLex (weightedDegree (ofCaseIMonomialSyn a),
    toLex (OrderDual.toDual (secondMoment (ofCaseIMonomialSyn a)),
      toLex (ofCaseIMonomialSyn a)))

lemma caseIMonomialKey_injective : Function.Injective caseIMonomialKey := by
  intro a b h
  exact congrArg (fun z ↦ ofLex (ofLex (ofLex z).2).2) h

/-- The linear order underlying the Case I monomial order. -/
noncomputable instance : LinearOrder CaseIMonomialSyn :=
  LinearOrder.lift' caseIMonomialKey caseIMonomialKey_injective

lemma caseIMonomialSyn_lt_iff {a b : CaseIMonomialSyn} :
    a < b ↔
      weightedDegree (ofCaseIMonomialSyn a) < weightedDegree (ofCaseIMonomialSyn b) ∨
        weightedDegree (ofCaseIMonomialSyn a) = weightedDegree (ofCaseIMonomialSyn b) ∧
          (secondMoment (ofCaseIMonomialSyn b) < secondMoment (ofCaseIMonomialSyn a) ∨
            secondMoment (ofCaseIMonomialSyn a) = secondMoment (ofCaseIMonomialSyn b) ∧
              toLex (ofCaseIMonomialSyn a) < toLex (ofCaseIMonomialSyn b)) := by
  change caseIMonomialKey a < caseIMonomialKey b ↔ _
  simp [caseIMonomialKey, Prod.Lex.toLex_lt_toLex]

lemma caseIMonomialSyn_le_iff {a b : CaseIMonomialSyn} :
    a ≤ b ↔
      weightedDegree (ofCaseIMonomialSyn a) < weightedDegree (ofCaseIMonomialSyn b) ∨
        weightedDegree (ofCaseIMonomialSyn a) = weightedDegree (ofCaseIMonomialSyn b) ∧
          (secondMoment (ofCaseIMonomialSyn b) < secondMoment (ofCaseIMonomialSyn a) ∨
            secondMoment (ofCaseIMonomialSyn a) = secondMoment (ofCaseIMonomialSyn b) ∧
              toLex (ofCaseIMonomialSyn a) ≤ toLex (ofCaseIMonomialSyn b)) := by
  change caseIMonomialKey a ≤ caseIMonomialKey b ↔ _
  simp [caseIMonomialKey, Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex]

instance : IsOrderedCancelAddMonoid CaseIMonomialSyn where
  le_of_add_le_add_left a b c h := by
    rw [caseIMonomialSyn_le_iff] at h ⊢
    simpa only [ofCaseIMonomialSyn_add, weightedDegree_add, secondMoment_add,
      add_lt_add_iff_left, add_lt_add_iff_right, add_right_inj, toLex_add,
      add_right_cancel_iff, add_left_cancel_iff, add_le_add_iff_left,
      add_le_add_iff_right] using h
  add_le_add_left a b h c := by
    rw [caseIMonomialSyn_le_iff] at h ⊢
    simpa only [ofCaseIMonomialSyn_add, weightedDegree_add, secondMoment_add,
      add_lt_add_iff_left, add_lt_add_iff_right, add_right_inj, toLex_add,
      add_right_cancel_iff, add_left_cancel_iff, add_le_add_iff_left,
      add_le_add_iff_right] using h

instance : WellFoundedLT CaseIMonomialSyn := by
  constructor
  rw [WellFounded.wellFounded_iff_has_min]
  intro u hu
  classical
  let hex : ∃ n, ∃ a ∈ u, weightedDegree (ofCaseIMonomialSyn a) = n := by
    obtain ⟨a, ha⟩ := hu
    exact ⟨weightedDegree (ofCaseIMonomialSyn a), a, ha, rfl⟩
  let n := Nat.find hex
  have hn : ∃ a ∈ u, weightedDegree (ofCaseIMonomialSyn a) = n := Nat.find_spec hex
  let fiber : Set CaseIMonomialSyn :=
    {a | weightedDegree (ofCaseIMonomialSyn a) = n}
  have hfiber : fiber.Finite := by
    change Set.Finite {a : ℕ+ →₀ ℕ | weightedDegree a = n}
    exact finite_weightedDegree_fiber n
  have hinter : (u ∩ fiber).Finite := hfiber.inter_of_right u
  have hinter_nonempty : (u ∩ fiber).Nonempty := by
    obtain ⟨a, ha, hwa⟩ := hn
    exact ⟨a, ha, hwa⟩
  obtain ⟨m, hm⟩ := hinter.exists_minimal hinter_nonempty
  refine ⟨m, hm.1.1, ?_⟩
  intro a ha ham
  have hnle : n ≤ weightedDegree (ofCaseIMonomialSyn a) :=
    Nat.find_min' hex ⟨a, ha, rfl⟩
  have hwm : weightedDegree (ofCaseIMonomialSyn m) = n := hm.1.2
  have ham' := ham
  rw [caseIMonomialSyn_lt_iff] at ham'
  rcases ham' with hweight | hweight
  · omega
  · have ha_fiber : a ∈ u ∩ fiber := ⟨ha, by simpa [fiber, hwm] using hweight.1⟩
    exact (not_le_of_gt ham) (hm.2 ha_fiber (le_of_lt ham))

lemma weightedDegree_eq_zero_iff (a : ℕ+ →₀ ℕ) : weightedDegree a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    ext i
    have hi := value_le_weightedDegree a i
    rw [ha] at hi
    simpa using hi
  · rintro rfl
    simp [weightedDegree]

lemma eq_of_le_of_weightedDegree_eq {a b : ℕ+ →₀ ℕ} (hab : a ≤ b)
    (hweight : weightedDegree a = weightedDegree b) : a = b := by
  have hdecomp : a + (b - a) = b := add_tsub_cancel_of_le hab
  have hzero : weightedDegree (b - a) = 0 := by
    have := congrArg weightedDegree hdecomp
    rw [weightedDegree_add] at this
    omega
  rw [weightedDegree_eq_zero_iff] at hzero
  simpa [hzero] using hdecomp

/-- The concrete monomial order used in the Case I argument. -/
noncomputable def caseIMonomialOrder : MonomialOrder ℕ+ where
  syn := CaseIMonomialSyn
  toSyn := { toEquiv := toCaseIMonomialSyn, map_add' := toCaseIMonomialSyn_add }
  toSyn_monotone a b hab := by
    rw [caseIMonomialSyn_le_iff]
    have hweight_le : weightedDegree a ≤ weightedDegree b := by
      rw [← add_tsub_cancel_of_le hab, weightedDegree_add]
      exact Nat.le_add_right _ _
    rcases hweight_le.eq_or_lt with hweight | hweight
    · have hab_eq : a = b := eq_of_le_of_weightedDegree_eq hab hweight
      subst b
      simp
    · exact Or.inl hweight

/-- The monomial order from Section 4, with ordinary lexicographic tie-breaking. -/
lemma caseI_def :
  ∀ a b,
    a ≺[caseIMonomialOrder] b ↔
      weightedDegree a < weightedDegree b ∨
        weightedDegree a = weightedDegree b ∧
          (secondMoment b < secondMoment a ∨
            secondMoment a = secondMoment b ∧ toLex a < toLex b) := by
  intro a b
  change toCaseIMonomialSyn a < toCaseIMonomialSyn b ↔ _
  exact caseIMonomialSyn_lt_iff

/-- The comparison law characterizing a monomial order of Case I type. -/
def IsCaseIMonomialOrder (m : MonomialOrder ℕ+) : Prop :=
  ∀ a b,
    a ≺[m] b ↔
      weightedDegree a < weightedDegree b ∨
        weightedDegree a = weightedDegree b ∧
          (secondMoment b < secondMoment a ∨
            secondMoment a = secondMoment b ∧ toLex a < toLex b)

lemma caseIMonomialOrder_lt_iff {a b : ℕ+ →₀ ℕ} :
    a ≺[caseIMonomialOrder] b ↔
      weightedDegree a < weightedDegree b ∨
        weightedDegree a = weightedDegree b ∧
          (secondMoment b < secondMoment a ∨
            secondMoment a = secondMoment b ∧ toLex a < toLex b) := by
  change toCaseIMonomialSyn a < toCaseIMonomialSyn b ↔ _
  exact caseIMonomialSyn_lt_iff

lemma isCaseIMonomialOrder_caseIMonomialOrder :
    IsCaseIMonomialOrder caseIMonomialOrder := by
  intro a b
  exact caseIMonomialOrder_lt_iff

lemma linear_lt_even_balanced (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m)
    (i k : ℕ+) (hk : (k : ℕ) = 2 * (i : ℕ)) :
    Finsupp.single k 1 ≺[m] Finsupp.single i 2 := by
  rw [hm]
  right
  constructor
  · simp only [weightedDegree_single]
    omega
  left
  simp only [secondMoment_single]
  have hi : 0 < (i : ℕ) := i.prop
  nlinarith [hk]

lemma unbalanced_lt_even_balanced (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m)
    (i j k : ℕ+) (hsum : (j : ℕ) + (k : ℕ) = 2 * (i : ℕ))
    (hji : (j : ℕ) < (i : ℕ)) :
    Finsupp.single j 1 + Finsupp.single k 1 ≺[m]
      Finsupp.single i 2 := by
  rw [hm]
  right
  constructor
  · rw [weightedDegree_add]
    simp only [weightedDegree_single]
    omega
  left
  rw [secondMoment_add]
  simp only [secondMoment_single]
  have hi : 0 < (i : ℕ) := i.prop
  nlinarith

lemma linear_lt_odd_balanced (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m)
    (i k : ℕ+) (hk : (k : ℕ) = 2 * (i : ℕ) + 1) :
    Finsupp.single k 1 ≺[m]
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
  rw [hm]
  right
  constructor
  · rw [weightedDegree_add]
    simp only [weightedDegree_single]
    simp [next]
    omega
  left
  rw [secondMoment_add]
  simp only [secondMoment_single]
  simp [next]
  have hi : 0 < (i : ℕ) := i.prop
  nlinarith [hk]

lemma unbalanced_lt_odd_balanced (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m)
    (i j k : ℕ+) (hsum : (j : ℕ) + (k : ℕ) = 2 * (i : ℕ) + 1)
    (hji : (j : ℕ) < (i : ℕ)) :
    Finsupp.single j 1 + Finsupp.single k 1 ≺[m]
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
  rw [hm]
  right
  constructor
  · simp only [weightedDegree_add, weightedDegree_single]
    simp [next]
    omega
  left
  simp only [secondMoment_add, secondMoment_single]
  simp [next]
  have hi : 0 < (i : ℕ) := i.prop
  nlinarith

lemma degree_C_mul_X_le (m : MonomialOrder ℕ+) (a : ℂ) (i : ℕ+) :
    m.degree (C a * X i : S) ≼[m] Finsupp.single i 1 := by
  have h := (m.degree_mul_le (f := C a) (g := X i) :
    m.degree (C a * X i : S) ≼[m] m.degree (C a : S) + m.degree (X i : S))
  rw [m.degree_C, m.degree_X, zero_add] at h
  exact h

lemma degree_C_mul_X_mul_X_le (m : MonomialOrder ℕ+) (a : ℂ) (i j : ℕ+) :
    m.degree (C a * X i * X j : S) ≼[m]
      Finsupp.single i 1 + Finsupp.single j 1 := by
  have hmul : m.degree (C a * X i * X j : S) ≼[m]
      m.degree (C a * X i : S) + m.degree (X j : S) := m.degree_mul_le
  rw [m.degree_X] at hmul
  have hadd := add_le_add_right (degree_C_mul_X_le m a i)
    (m.toSyn (m.degree (X j : S)))
  rw [← map_add, m.degree_X, ← map_add] at hadd
  exact le_trans hmul (by simpa [add_comm] using hadd)

lemma degree_finset_sum_le (m : MonomialOrder ℕ+) {T : Type*} (u : Finset T)
    (f : T → S) (q : ℕ+ →₀ ℕ) (h : ∀ i ∈ u, m.degree (f i) ≼[m] q) :
    m.degree (∑ i ∈ u, f i) ≼[m] q := by
  show m.toSyn (m.degree (∑ i ∈ u, f i)) ≤ m.toSyn q
  apply le_trans m.degree_sum_le
  apply Finset.sup_le
  intro i hi
  exact h i hi

lemma degree_add_lt (m : MonomialOrder ℕ+) {f₁ f₂ : S} {q : ℕ+ →₀ ℕ}
    (h₁ : m.degree f₁ ≺[m] q) (h₂ : m.degree f₂ ≺[m] q) :
    m.degree (f₁ + f₂) ≺[m] q := by
  exact lt_of_le_of_lt m.degree_add_le (sup_lt_iff.mpr ⟨h₁, h₂⟩)

lemma degree_finset_sum_lt (m : MonomialOrder ℕ+) {T : Type*} (u : Finset T)
    (f : T → S) (q : ℕ+ →₀ ℕ) (hq : 0 ≺[m] q)
    (h : ∀ i ∈ u, m.degree (f i) ≺[m] q) :
    m.degree (∑ i ∈ u, f i) ≺[m] q := by
  classical
  induction u using Finset.cons_induction_on with
  | empty => simpa using hq
  | cons a u ha ih =>
      rw [Finset.sum_cons]
      apply degree_add_lt m (h a (by simp))
      apply ih
      intro i hi
      exact h i (by simp [hi])

lemma degree_g_even (c : ℂ) (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m)
    (i : ℕ+) :
    m.degree (g c (2 * (i : ℕ))) = Finsupp.single i 2 := by
  classical
  have heven : 2 ∣ 2 * (i : ℕ) := dvd_mul_right 2 (i : ℕ)
  rw [g, if_pos heven]
  let twice : ℕ+ := ⟨2 * (i : ℕ), Nat.mul_pos (by norm_num) i.prop⟩
  have hx_twice : x (2 * (i : ℕ)) = X twice := by
    simp [x, twice]
  rw [hx_twice]
  have hsquare : m.degree (x (2 * (i : ℕ) / 2) ^ 2) = Finsupp.single i 2 := by
    have hx_half : x (2 * (i : ℕ) / 2) = X i := by
      have hind : 2 * (i : ℕ) / 2 = (i : ℕ) := by omega
      rw [hind]
      unfold x
      split <;> rename_i h
      · apply congrArg X
        exact Subtype.ext rfl
      · exact (h i.prop).elim
    rw [hx_half, m.degree_pow, m.degree_X]
    simp [two_smul, ← Finsupp.single_add]
  have hlower : m.degree
      (C (s c (2 * (i : ℕ)) - c) * X twice +
        ∑ j ∈ (Finset.range (2 * (i : ℕ))).filter
          (fun j ↦ 0 < j ∧ 2 * j < 2 * (i : ℕ)),
            C (s c (2 * (i : ℕ) - 2 * j)) * x j * x (2 * (i : ℕ) - j)) ≺[m]
      Finsupp.single i 2 := by
    apply degree_add_lt m
    · have hlinear : m.degree (C (s c (2 * (i : ℕ)) - c) * X twice : S) ≼[m]
        Finsupp.single twice 1 := degree_C_mul_X_le m _ twice
      exact lt_of_le_of_lt hlinear <| linear_lt_even_balanced m hm i twice rfl
    · apply degree_finset_sum_lt m
      · rw [hm]
        left
        simp [weightedDegree, i.prop]
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        rcases hj with ⟨_, hjpos, hjdouble⟩
        have hjlt : j < (i : ℕ) := by omega
        have hdiffpos : 0 < 2 * (i : ℕ) - j := by omega
        let jpos : ℕ+ := ⟨j, hjpos⟩
        let kpos : ℕ+ := ⟨2 * (i : ℕ) - j, hdiffpos⟩
        have hdegree :=
          degree_C_mul_X_mul_X_le m (s c (2 * (i : ℕ) - 2 * j)) jpos kpos
        have hxj : x j = X jpos := by simp [x, jpos, hjpos]
        have hxk : x (2 * (i : ℕ) - j) = X kpos := by simp [x, kpos, hdiffpos]
        rw [hxj, hxk]
        exact lt_of_le_of_lt hdegree <|
          unbalanced_lt_even_balanced m hm i jpos kpos (by simp [jpos, kpos]; omega)
            (by simpa [jpos] using hjlt)
  calc
    m.degree
        (C (s c (2 * (i : ℕ)) - c) * X twice +
          (∑ j ∈ (Finset.range (2 * (i : ℕ))).filter
              (fun j ↦ 0 < j ∧ 2 * j < 2 * (i : ℕ)),
                C (s c (2 * (i : ℕ) - 2 * j)) * x j * x (2 * (i : ℕ) - j)) +
          x (2 * (i : ℕ) / 2) ^ 2) =
        m.degree (x (2 * (i : ℕ) / 2) ^ 2) :=
      m.degree_add_eq_right_of_lt (hsquare ▸ hlower)
    _ = Finsupp.single i 2 := hsquare

lemma coeff_g_even_top (c : ℂ) (i : ℕ+) :
    coeff (Finsupp.single i 2) (g c (2 * (i : ℕ))) = 1 := by
  classical
  let twice : ℕ+ := ⟨2 * (i : ℕ), Nat.mul_pos (by norm_num) i.prop⟩
  have hxN : x (2 * (i : ℕ)) = X twice := by simpa [twice] using x_eq_X twice
  have hxhalf : x (2 * (i : ℕ) / 2) = X i := by
    have : 2 * (i : ℕ) / 2 = (i : ℕ) := by omega
    rw [this, x_eq_X]
  have hlinear : Finsupp.single twice 1 ≠ Finsupp.single i 2 := by
    intro h
    have hsum := congrArg (fun a : ℕ+ →₀ ℕ ↦ a.sum fun _ e ↦ e) h
    simpa using hsum
  rw [g, if_pos (dvd_mul_right 2 (i : ℕ)), hxN, hxhalf]
  simp only [coeff_add, coeff_sum]
  have hcoeffLinear :
      coeff (Finsupp.single i 2) (C (s c (2 * (i : ℕ)) - c) * X twice) = 0 := by
    rw [X, C_mul_monomial]
    simp [hlinear]
  rw [hcoeffLinear]
  have hcoeffSum :
      ∑ j ∈ (Finset.range (2 * (i : ℕ))).filter
          (fun j ↦ 0 < j ∧ 2 * j < 2 * (i : ℕ)),
        coeff (Finsupp.single i 2)
          (C (s c (2 * (i : ℕ) - 2 * j)) * x j * x (2 * (i : ℕ) - j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have hjlt : j < (i : ℕ) := by omega
    let jp : ℕ+ := ⟨j, hj'.1⟩
    let kp : ℕ+ := ⟨2 * (i : ℕ) - j, by omega⟩
    have hxj : x j = X jp := by simpa [jp] using x_eq_X jp
    have hxk : x (2 * (i : ℕ) - j) = X kp := by simpa [kp] using x_eq_X kp
    rw [hxj, hxk]
    simp only [X, C_mul_monomial, mul_one, monomial_mul, one_mul, coeff_monomial]
    rw [if_neg]
    intro heq
    have hjp_i : jp ≠ i := by
      intro h
      have hv := congrArg Subtype.val h
      change j = (i : ℕ) at hv
      omega
    have hjp_kp : jp ≠ kp := by
      intro h
      have hv := congrArg Subtype.val h
      change j = 2 * (i : ℕ) - j at hv
      omega
    have hval := congrArg (fun a : ℕ+ →₀ ℕ ↦ a jp) heq
    simp [Finsupp.single_apply, hjp_i, hjp_kp] at hval
  rw [hcoeffSum]
  rw [X_pow_eq_monomial]
  simp

lemma odd_index_filter (i : ℕ+) :
    (Finset.range (2 * (i : ℕ) + 1)).filter
        (fun j ↦ 0 < j ∧ 2 * j < 2 * (i : ℕ) + 1) =
      insert (i : ℕ) ((Finset.range (i : ℕ)).filter (fun j ↦ 0 < j)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨_, hjpos, hj⟩
    have hle : j ≤ (i : ℕ) := by omega
    rcases hle.eq_or_lt with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hjpos⟩
  · rintro (rfl | ⟨hjlt, hjpos⟩)
    · exact ⟨by omega, i.prop, by omega⟩
    · exact ⟨by omega, hjpos, by omega⟩

lemma coeff_g_odd_top (c : ℂ) (i : ℕ+) :
    coeff (Finsupp.single i 1 + Finsupp.single (next i) 1)
      (g c (2 * (i : ℕ) + 1)) = c := by
  classical
  let n := 2 * (i : ℕ) + 1
  let top : ℕ+ := ⟨n, by simp [n, i.prop]⟩
  let lowerIndices := (Finset.range (i : ℕ)).filter (fun j ↦ 0 < j)
  let lower : S := C (s c n - c) * X top +
    ∑ j ∈ lowerIndices,
      C (s c (n - 2 * j)) * x j * x (n - j)
  let main : S := C c * X i * X (next i)
  have hnodd : ¬2 ∣ n := by simp [n]
  have htop : x n = X top := by simpa [top] using x_eq_X top
  have hmain_term :
      C (s c (n - 2 * (i : ℕ))) * x (i : ℕ) * x (n - (i : ℕ)) = main := by
    have hsub₁ : n - 2 * (i : ℕ) = 1 := by simp [n]
    have hsub₂ : n - (i : ℕ) = (next i : ℕ) := by simp [n, next]; omega
    rw [hsub₁, hsub₂, x_eq_X i, x_eq_X (next i)]
    simp [s, main]
  have hdecomp : g c n = main + lower := by
    rw [g, if_neg hnodd, add_zero, odd_index_filter]
    rw [Finset.sum_insert (by simp [lowerIndices])]
    rw [htop, hmain_term]
    simp only [lower, main]
    abel
  rw [show g c (2 * (i : ℕ) + 1) = g c n by rfl, hdecomp, coeff_add]
  have hmaincoeff :
      coeff (Finsupp.single i 1 + Finsupp.single (next i) 1) main = c := by
    simp [main, X, C_mul_monomial, monomial_mul]
  rw [hmaincoeff]
  suffices coeff (Finsupp.single i 1 + Finsupp.single (next i) 1) lower = 0 by
    rw [this, add_zero]
  simp only [lower, coeff_add, coeff_sum]
  have hlinear : Finsupp.single top 1 ≠
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
    intro h
    have hsum := congrArg (fun a : ℕ+ →₀ ℕ ↦ a.sum fun _ e ↦ e) h
    rw [Finsupp.sum_add_index'] at hsum
    · simp at hsum
    · simp
    · simp
  have hcoeffLinear :
      coeff (Finsupp.single i 1 + Finsupp.single (next i) 1)
        (C (s c n - c) * X top) = 0 := by
    rw [X, C_mul_monomial]
    simp [hlinear]
  rw [hcoeffLinear, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j < (i : ℕ) ∧ 0 < j := by simpa [lowerIndices] using hj
  let jp : ℕ+ := ⟨j, hj'.2⟩
  let kp : ℕ+ := ⟨n - j, by simp [n]; omega⟩
  have hxj : x j = X jp := by simpa [jp] using x_eq_X jp
  have hxk : x (n - j) = X kp := by simpa [kp] using x_eq_X kp
  rw [hxj, hxk]
  simp only [X, C_mul_monomial, mul_one, monomial_mul, coeff_monomial]
  rw [if_neg]
  intro heq
  have hjlt : j < (i : ℕ) := hj'.1
  have hjp_i : jp ≠ i := by
    intro h
    have hv := congrArg Subtype.val h
    change j = (i : ℕ) at hv
    omega
  have hjp_next : jp ≠ next i := by
    intro h
    have hv := congrArg Subtype.val h
    change j = (i : ℕ) + 1 at hv
    omega
  have hjp_kp : jp ≠ kp := by
    intro h
    have hv := congrArg Subtype.val h
    change j = n - j at hv
    simp [n] at hv
    omega
  have hval := congrArg (fun a : ℕ+ →₀ ℕ ↦ a jp) heq
  simp [Finsupp.single_apply, hjp_i, hjp_next, hjp_kp] at hval

lemma degree_odd_main_term (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (i : ℕ+) :
    m.degree (C c * X i * X (next i) : S) =
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
  have hc0 : c ≠ 0 := ne_zero_of_quadratic c hc
  have hCX : (C c * X i : S) ≠ 0 := by simp [hc0]
  rw [m.degree_mul hCX (by simp), m.degree_mul (by simp [hc0]) (by simp),
    m.degree_C, m.degree_X, m.degree_X, zero_add]

lemma degree_g_odd (c : ℂ) (hc : c ^ 2 + c = 1) (m : MonomialOrder ℕ+)
    (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.degree (g c (2 * (i : ℕ) + 1)) =
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
  classical
  let n := 2 * (i : ℕ) + 1
  let top : ℕ+ := ⟨n, by simp [n, i.prop]⟩
  let lowerIndices := (Finset.range (i : ℕ)).filter (fun j ↦ 0 < j)
  let lower : S := C (s c n - c) * X top +
    ∑ j ∈ lowerIndices,
      C (s c (n - 2 * j)) * x j * x (n - j)
  let main : S := C c * X i * X (next i)
  have hnodd : ¬2 ∣ n := by simp [n]
  have htop : x n = X top := by
    simpa [top] using x_eq_X top
  have hmain_term :
      C (s c (n - 2 * (i : ℕ))) * x (i : ℕ) * x (n - (i : ℕ)) = main := by
    have hsub₁ : n - 2 * (i : ℕ) = 1 := by simp [n]
    have hsub₂ : n - (i : ℕ) = (next i : ℕ) := by
      change n - (i : ℕ) = (i : ℕ) + 1
      simp only [n]
      omega
    rw [hsub₁, hsub₂, x_eq_X i, x_eq_X (next i)]
    simp [s, main]
  have hdecomp : g c n = main + lower := by
    rw [g, if_neg hnodd, add_zero, odd_index_filter]
    rw [Finset.sum_insert (by simp [lowerIndices])]
    rw [htop, hmain_term]
    simp only [lower, main]
    abel
  have htarget_pos : 0 ≺[m]
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
    rw [hm]
    left
    rw [weightedDegree_add]
    simp only [weightedDegree_single]
    have hpos : 0 < (i : ℕ) + (next i : ℕ) := Nat.add_pos_left i.prop _
    simpa [weightedDegree] using hpos
  have hlower : m.degree lower ≺[m]
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
    apply degree_add_lt m
    · have hlinear : m.degree (C (s c n - c) * X top : S) ≼[m]
          Finsupp.single top 1 := degree_C_mul_X_le m _ top
      exact lt_of_le_of_lt hlinear <|
        linear_lt_odd_balanced m hm i top (by simp [top, n])
    · apply degree_finset_sum_lt m lowerIndices _ _ htarget_pos
      intro j hj
      simp only [lowerIndices, Finset.mem_filter, Finset.mem_range] at hj
      rcases hj with ⟨hjlt, hjpos⟩
      have hdiffpos : 0 < n - j := by simp [n]; omega
      let jpos : ℕ+ := ⟨j, hjpos⟩
      let kpos : ℕ+ := ⟨n - j, hdiffpos⟩
      have hdegree := degree_C_mul_X_mul_X_le m (s c (n - 2 * j)) jpos kpos
      have hxj : x j = X jpos := by simpa [jpos] using x_eq_X jpos
      have hxk : x (n - j) = X kpos := by simpa [kpos] using x_eq_X kpos
      rw [hxj, hxk]
      exact lt_of_le_of_lt hdegree <|
        unbalanced_lt_odd_balanced m hm i jpos kpos (by simp [jpos, kpos, n]; omega)
          (by simpa [jpos] using hjlt)
  rw [hdecomp, m.degree_add_of_lt]
  · exact degree_odd_main_term c hc m i
  · rw [degree_odd_main_term c hc m i]
    exact hlower

lemma g_even_ne_zero (c : ℂ) (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m)
    (i : ℕ+) : g c (2 * (i : ℕ)) ≠ 0 := by
  intro hzero
  have hdegree := degree_g_even c m hm i
  rw [hzero, m.degree_zero] at hdegree
  have hsingle : Finsupp.single i 2 ≠ 0 := Finsupp.single_ne_zero.mpr (by norm_num)
  exact hsingle hdegree.symm

lemma g_odd_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) (m : MonomialOrder ℕ+)
    (hm : IsCaseIMonomialOrder m) (i : ℕ+) : g c (2 * (i : ℕ) + 1) ≠ 0 := by
  intro hzero
  have hdegree := degree_g_odd c hc m hm i
  rw [hzero, m.degree_zero] at hdegree
  have htarget : Finsupp.single i 1 + Finsupp.single (next i) 1 ≠ 0 := by
    intro h
    have hle : Finsupp.single i 1 ≤
        Finsupp.single i 1 + Finsupp.single (next i) 1 := le_add_right le_rfl
    rw [h] at hle
    have hi := Finsupp.single_le_iff.mp hle
    simp at hi
  exact htarget hdegree.symm

/-- The second moment of the leading monomial of `gₖ`. -/
def balancedSecondMoment (k : ℕ) : ℕ :=
  (k / 2) ^ 2 + ((k + 1) / 2) ^ 2

/-- The second moment of the leading monomial of `xᵣ g_{N-r}`. -/
def rho (N r : ℕ) : ℕ :=
  r ^ 2 + balancedSecondMoment (N - r)

lemma rho_family_one_left (m : ℕ) :
    rho (3 * m + 1) m = 3 * m ^ 2 + 2 * m + 1 := by
  unfold rho balancedSecondMoment
  have hsub : 3 * m + 1 - m = 2 * m + 1 := by omega
  rw [hsub]
  have hdiv₁ : (2 * m + 1) / 2 = m := by omega
  have hdiv₂ : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [hdiv₁, hdiv₂]
  ring

lemma rho_family_one_right (m : ℕ) :
    rho (3 * m + 1) (m + 1) = 3 * m ^ 2 + 2 * m + 1 := by
  unfold rho balancedSecondMoment
  have hsub : 3 * m + 1 - (m + 1) = 2 * m := by omega
  rw [hsub]
  have hdiv₁ : (2 * m) / 2 = m := by omega
  have hdiv₂ : (2 * m + 1) / 2 = m := by omega
  rw [hdiv₁, hdiv₂]
  ring

lemma rho_family_two_left (m : ℕ) :
    rho (3 * m + 2) m = 3 * m ^ 2 + 4 * m + 2 := by
  unfold rho balancedSecondMoment
  have hsub : 3 * m + 2 - m = 2 * m + 2 := by omega
  rw [hsub]
  have hdiv₁ : (2 * m + 2) / 2 = m + 1 := by omega
  have hdiv₂ : (2 * m + 2 + 1) / 2 = m + 1 := by omega
  rw [hdiv₁, hdiv₂]
  ring

lemma rho_family_two_right (m : ℕ) :
    rho (3 * m + 2) (m + 1) = 3 * m ^ 2 + 4 * m + 2 := by
  unfold rho balancedSecondMoment
  have hsub : 3 * m + 2 - (m + 1) = 2 * m + 1 := by omega
  rw [hsub]
  have hdiv₁ : (2 * m + 1) / 2 = m := by omega
  have hdiv₂ : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [hdiv₁, hdiv₂]
  ring

lemma rho_family_three_center (m : ℕ) :
    rho (3 * m) m = 3 * m ^ 2 := by
  unfold rho balancedSecondMoment
  have hsub : 3 * m - m = 2 * m := by omega
  rw [hsub]
  have hdiv₁ : (2 * m) / 2 = m := by omega
  have hdiv₂ : (2 * m + 1) / 2 = m := by omega
  rw [hdiv₁, hdiv₂]
  ring

lemma rho_family_three_left {m : ℕ} (hm : 1 ≤ m) :
    rho (3 * m) (m - 1) = 3 * m ^ 2 + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    exact ⟨m - 1, by omega⟩
  unfold rho balancedSecondMoment
  have hsub : 3 * (k + 1) - (k + 1 - 1) = 2 * (k + 1) + 1 := by omega
  rw [hsub]
  have hdiv₁ : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
  have hdiv₂ : (2 * (k + 1) + 1 + 1) / 2 = k + 2 := by omega
  rw [hdiv₁, hdiv₂]
  simp
  ring

lemma rho_family_three_right {m : ℕ} (hm : 1 ≤ m) :
    rho (3 * m) (m + 1) = 3 * m ^ 2 + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    exact ⟨m - 1, by omega⟩
  unfold rho balancedSecondMoment
  have hsub : 3 * (k + 1) - (k + 1 + 1) = 2 * (k + 1) - 1 := by omega
  rw [hsub]
  have hdiv₁ : (2 * (k + 1) - 1) / 2 = k := by omega
  have hdiv₂ : (2 * (k + 1) - 1 + 1) / 2 = k + 1 := by omega
  rw [hdiv₁, hdiv₂]
  ring

lemma rho_family_one_strict {m r : ℕ} (hr : r ≤ 3 * m + 1)
    (hne₁ : r ≠ m) (hne₂ : r ≠ m + 1) :
    rho (3 * m + 1) m < rho (3 * m + 1) r := by
  rw [rho_family_one_left]
  rcases Nat.even_or_odd' (3 * m + 1 - r) with ⟨j, hj | hj⟩
  · have hsum : 3 * m + 1 = r + 2 * j := by omega
    unfold rho balancedSecondMoment
    rw [hj]
    have hdiv₁ : (2 * j) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1) / 2 = j := by omega
    rw [hdiv₁, hdiv₂]
    have hside : r + 1 ≤ m ∨ m + 2 ≤ r := by omega
    rcases hside with hside | hside <;> nlinarith
  · have hsum : 3 * m + 1 = r + (2 * j + 1) := by omega
    unfold rho balancedSecondMoment
    rw [hj]
    have hdiv₁ : (2 * j + 1) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [hdiv₁, hdiv₂]
    have hside : r + 1 ≤ m ∨ m + 2 ≤ r := by omega
    rcases hside with hside | hside <;> nlinarith

lemma rho_family_two_strict {m r : ℕ} (hr : r ≤ 3 * m + 2)
    (hne₁ : r ≠ m) (hne₂ : r ≠ m + 1) :
    rho (3 * m + 2) m < rho (3 * m + 2) r := by
  rw [rho_family_two_left]
  rcases Nat.even_or_odd' (3 * m + 2 - r) with ⟨j, hj | hj⟩
  · have hsum : 3 * m + 2 = r + 2 * j := by omega
    unfold rho balancedSecondMoment
    rw [hj]
    have hdiv₁ : (2 * j) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1) / 2 = j := by omega
    rw [hdiv₁, hdiv₂]
    have hside : r + 1 ≤ m ∨ m + 2 ≤ r := by omega
    rcases hside with hside | hside <;> nlinarith
  · have hsum : 3 * m + 2 = r + (2 * j + 1) := by omega
    unfold rho balancedSecondMoment
    rw [hj]
    have hdiv₁ : (2 * j + 1) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [hdiv₁, hdiv₂]
    have hside : r + 1 ≤ m ∨ m + 2 ≤ r := by omega
    rcases hside with hside | hside <;> nlinarith

lemma rho_family_three_strict {m r : ℕ} (hm : 2 ≤ m) (hr : r ≤ 3 * m)
    (hne₁ : r ≠ m - 1) (hne₂ : r ≠ m) (hne₃ : r ≠ m + 1) :
    rho (3 * m) (m - 1) < rho (3 * m) r := by
  rw [rho_family_three_left (m := m) (by omega)]
  rcases Nat.even_or_odd' (3 * m - r) with ⟨j, hj | hj⟩
  · have hsum : 3 * m = r + 2 * j := by omega
    unfold rho balancedSecondMoment
    rw [hj]
    have hdiv₁ : (2 * j) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1) / 2 = j := by omega
    rw [hdiv₁, hdiv₂]
    have hside : r + 2 ≤ m ∨ m + 2 ≤ r := by omega
    rcases hside with hside | hside <;> nlinarith
  · have hsum : 3 * m = r + (2 * j + 1) := by omega
    unfold rho balancedSecondMoment
    rw [hj]
    have hdiv₁ : (2 * j + 1) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [hdiv₁, hdiv₂]
    have hside : r + 2 ≤ m ∨ m + 2 ≤ r := by omega
    rcases hside with hside | hside <;> nlinarith

lemma rho_family_one_lt_balanced {k : ℕ} (hk : 1 ≤ k) :
    rho (3 * k + 1) k < balancedSecondMoment (3 * k + 1) := by
  rw [rho_family_one_left]
  rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
  · have htpos : 1 ≤ t := by omega
    unfold balancedSecondMoment
    rw [ht]
    have hdiv₁ : (3 * (2 * t) + 1) / 2 = 3 * t := by omega
    have hdiv₂ : (3 * (2 * t) + 1 + 1) / 2 = 3 * t + 1 := by omega
    rw [hdiv₁, hdiv₂]
    nlinarith
  · unfold balancedSecondMoment
    rw [ht]
    have hdiv₁ : (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 := by omega
    have hdiv₂ : (3 * (2 * t + 1) + 1 + 1) / 2 = 3 * t + 2 := by omega
    rw [hdiv₁, hdiv₂]
    nlinarith

lemma rho_family_two_lt_balanced {k : ℕ} (hk : 1 ≤ k) :
    rho (3 * k + 2) k < balancedSecondMoment (3 * k + 2) := by
  rw [rho_family_two_left]
  rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
  · have htpos : 1 ≤ t := by omega
    unfold balancedSecondMoment
    rw [ht]
    have hdiv₁ : (3 * (2 * t) + 2) / 2 = 3 * t + 1 := by omega
    have hdiv₂ : (3 * (2 * t) + 2 + 1) / 2 = 3 * t + 1 := by omega
    rw [hdiv₁, hdiv₂]
    nlinarith
  · unfold balancedSecondMoment
    rw [ht]
    have hdiv₁ : (3 * (2 * t + 1) + 2) / 2 = 3 * t + 2 := by omega
    have hdiv₂ : (3 * (2 * t + 1) + 2 + 1) / 2 = 3 * t + 3 := by omega
    rw [hdiv₁, hdiv₂]
    nlinarith

lemma rho_family_three_lt_balanced {k : ℕ} (hk : 2 ≤ k) :
    rho (3 * k) (k - 1) < balancedSecondMoment (3 * k) := by
  rw [rho_family_three_left (m := k) (by omega)]
  rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
  · have htpos : 1 ≤ t := by omega
    unfold balancedSecondMoment
    rw [ht]
    have hdiv₁ : (3 * (2 * t)) / 2 = 3 * t := by omega
    have hdiv₂ : (3 * (2 * t) + 1) / 2 = 3 * t := by omega
    rw [hdiv₁, hdiv₂]
    nlinarith
  · have htpos : 1 ≤ t := by omega
    unfold balancedSecondMoment
    rw [ht]
    have hdiv₁ : (3 * (2 * t + 1)) / 2 = 3 * t + 1 := by omega
    have hdiv₂ : (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 := by omega
    rw [hdiv₁, hdiv₂]
    nlinarith
lemma secondMoment_degree_x_mul_g (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {N r : ℕ}
    (hr : 1 ≤ r) (hrN : r + 2 ≤ N) :
    secondMoment (m.degree (x r * g c (N - r))) = rho N r := by
  let rp : ℕ+ := ⟨r, by omega⟩
  have hx : x r = X rp := by simpa [rp] using x_eq_X rp
  rcases Nat.even_or_odd' (N - r) with ⟨j, hj | hj⟩
  · have hjpos : 0 < j := by omega
    let jp : ℕ+ := ⟨j, hjpos⟩
    have hg0 := g_even_ne_zero c m hm jp
    rw [hx, m.degree_mul (by simp) (by simpa [jp, hj] using hg0),
      m.degree_X, show g c (N - r) = g c (2 * (jp : ℕ)) by simp [jp, hj],
      degree_g_even c m hm jp, secondMoment_add]
    simp only [secondMoment_single]
    simp [rho, balancedSecondMoment, rp, jp, hj]
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [hdiv]
    omega
  · have hjpos : 0 < j := by omega
    let jp : ℕ+ := ⟨j, hjpos⟩
    have hg0 := g_odd_ne_zero c hc m hm jp
    rw [hx, m.degree_mul (by simp) (by simpa [jp, hj] using hg0),
      m.degree_X,
      show g c (N - r) = g c (2 * (jp : ℕ) + 1) by simp [jp, hj],
      degree_g_odd c hc m hm jp, secondMoment_add, secondMoment_add]
    simp only [secondMoment_single]
    simp [rho, balancedSecondMoment, rp, jp, hj, next]
    have hdiv₁ : (2 * j + 1) / 2 = j := by omega
    have hdiv₂ : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [hdiv₁, hdiv₂]

lemma weightedDegree_degree_x_mul_g (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {N r : ℕ}
    (hr : 1 ≤ r) (hrN : r + 2 ≤ N) :
    weightedDegree (m.degree (x r * g c (N - r))) = N := by
  let rp : ℕ+ := ⟨r, by omega⟩
  have hx : x r = X rp := by simpa [rp] using x_eq_X rp
  rcases Nat.even_or_odd' (N - r) with ⟨j, hj | hj⟩
  · have hjpos : 0 < j := by omega
    let jp : ℕ+ := ⟨j, hjpos⟩
    have hg0 := g_even_ne_zero c m hm jp
    rw [hx, m.degree_mul (by simp) (by simpa [jp, hj] using hg0),
      m.degree_X, show g c (N - r) = g c (2 * (jp : ℕ)) by simp [jp, hj],
      degree_g_even c m hm jp, weightedDegree_add]
    simp only [weightedDegree_single]
    simp [rp, jp]
    omega
  · have hjpos : 0 < j := by omega
    let jp : ℕ+ := ⟨j, hjpos⟩
    have hg0 := g_odd_ne_zero c hc m hm jp
    rw [hx, m.degree_mul (by simp) (by simpa [jp, hj] using hg0),
      m.degree_X,
      show g c (N - r) = g c (2 * (jp : ℕ) + 1) by simp [jp, hj],
      degree_g_odd c hc m hm jp, weightedDegree_add, weightedDegree_add]
    simp only [weightedDegree_single]
    simp [rp, jp, next]
    omega

lemma degree_x_mul_g_lt_of_rho_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {N r s : ℕ}
    (hr : 1 ≤ r) (hrN : r + 2 ≤ N) (hs : 1 ≤ s) (hsN : s + 2 ≤ N)
    (hρ : rho N r < rho N s) :
    m.degree (x s * g c (N - s)) ≺[m] m.degree (x r * g c (N - r)) := by
  rw [hm]
  right
  refine ⟨?_, Or.inl ?_⟩
  · rw [weightedDegree_degree_x_mul_g c hc m hm hs hsN,
      weightedDegree_degree_x_mul_g c hc m hm hr hrN]
  · rw [secondMoment_degree_x_mul_g c hc m hm hr hrN,
      secondMoment_degree_x_mul_g c hc m hm hs hsN]
    exact hρ

lemma degree_normalized_g_odd (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.degree (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S) =
      Finsupp.single i 1 + Finsupp.single (next i) 1 := by
  have hc0 : c ≠ 0 := ne_zero_of_quadratic c hc
  rw [m.degree_mul (by simp [hc0]) (g_odd_ne_zero c hc m hm i),
    m.degree_C, zero_add, degree_g_odd c hc m hm i]

lemma weightedDegree_degree_normalizedRelation (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {n : ℕ} (hn : 2 ≤ n) :
    weightedDegree (m.degree (normalizedRelation c n)) = n := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · have hkpos : 0 < k := by omega
    let kp : ℕ+ := ⟨k, hkpos⟩
    rw [normalizedRelation, if_pos (by omega),
      show g c n = g c (2 * (kp : ℕ)) by simp [kp, hk],
      degree_g_even c m hm kp]
    rw [weightedDegree_single]
    simp [kp, hk]
    omega
  · have hkpos : 0 < k := by omega
    let kp : ℕ+ := ⟨k, hkpos⟩
    rw [normalizedRelation, if_neg (by omega),
      show C c⁻¹ * g c n = C c⁻¹ * g c (2 * (kp : ℕ) + 1) by simp [kp, hk],
      degree_normalized_g_odd c hc m hm kp]
    rw [weightedDegree_add, weightedDegree_single, weightedDegree_single]
    simp [kp, hk, next]
    omega

lemma secondMoment_degree_normalizedRelation (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {n : ℕ} (hn : 2 ≤ n) :
    secondMoment (m.degree (normalizedRelation c n)) = balancedSecondMoment n := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · have hkpos : 0 < k := by omega
    let kp : ℕ+ := ⟨k, hkpos⟩
    rw [normalizedRelation, if_pos (by omega),
      show g c n = g c (2 * (kp : ℕ)) by simp [kp, hk],
      degree_g_even c m hm kp, secondMoment_single]
    unfold balancedSecondMoment
    rw [hk]
    have hdiv₁ : (2 * k) / 2 = k := by omega
    have hdiv₂ : (2 * k + 1) / 2 = k := by omega
    rw [hdiv₁, hdiv₂]
    simp [kp]
    ring
  · have hkpos : 0 < k := by omega
    let kp : ℕ+ := ⟨k, hkpos⟩
    rw [normalizedRelation, if_neg (by omega),
      show C c⁻¹ * g c n = C c⁻¹ * g c (2 * (kp : ℕ) + 1) by simp [kp, hk],
      degree_normalized_g_odd c hc m hm kp, secondMoment_add,
      secondMoment_single, secondMoment_single]
    unfold balancedSecondMoment
    rw [hk]
    have hdiv₁ : (2 * k + 1) / 2 = k := by omega
    have hdiv₂ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [hdiv₁, hdiv₂]
    simp [kp, next]

lemma normalizedRelation_injective_of_two_le (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (h : normalizedRelation c a = normalizedRelation c b) :
    a = b := by
  have hd := congrArg (fun p : S ↦ weightedDegree (m.degree p)) h
  rw [weightedDegree_degree_normalizedRelation c hc m hm ha,
    weightedDegree_degree_normalizedRelation c hc m hm hb] at hd
  exact hd

lemma degree_normalizedRelation_lt_x_mul_g (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {N r : ℕ}
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrN : r + 2 ≤ N)
    (hρ : rho N r < balancedSecondMoment N) :
    m.degree (normalizedRelation c N) ≺[m] m.degree (x r * g c (N - r)) := by
  rw [hm]
  right
  refine ⟨?_, Or.inl ?_⟩
  · rw [weightedDegree_degree_normalizedRelation c hc m hm hN,
      weightedDegree_degree_x_mul_g c hc m hm hr hrN]
  · rw [secondMoment_degree_x_mul_g c hc m hm hr hrN,
      secondMoment_degree_normalizedRelation c hc m hm hN]
    exact hρ

lemma degree_C_mul_le (m : MonomialOrder ℕ+) (a : ℂ) (p : S) :
    m.degree (C a * p) ≼[m] m.degree p := by
  simpa using (m.degree_mul_le (f := C a) (g := p))

lemma degree_x_mul_normalizedRelation_eq (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {N r : ℕ}
    (hr : 1 ≤ r) (hrN : r + 2 ≤ N) :
    m.degree (x r * normalizedRelation c (N - r)) =
      m.degree (x r * g c (N - r)) := by
  rcases Nat.even_or_odd' (N - r) with ⟨k, hk | hk⟩
  · rw [normalizedRelation, if_pos (by omega)]
  · have hkpos : 0 < k := by omega
    let kp : ℕ+ := ⟨k, hkpos⟩
    have hx0 : x r ≠ 0 := by
      let rp : ℕ+ := ⟨r, by omega⟩
      simpa [show x r = X rp by simpa [rp] using x_eq_X rp]
    have hg0 : g c (N - r) ≠ 0 := by
      simpa [kp, hk] using g_odd_ne_zero c hc m hm kp
    rw [normalizedRelation, if_neg (by omega)]
    have hreorder : x r * (C c⁻¹ * g c (N - r)) =
        C c⁻¹ * (x r * g c (N - r)) := by ring
    rw [hreorder, m.degree_mul (by simp [ne_zero_of_quadratic c hc])
      (mul_ne_zero hx0 hg0), m.degree_C, zero_add]

noncomputable def standardSummand (c : ℂ) (N r : ℕ) : S :=
  C (pentagonTermCoefficient c N r * normalizationScalar c (N - r)) *
    x r * normalizedRelation c (N - r)

lemma degree_standardSummand_le (c : ℂ) (m : MonomialOrder ℕ+) (N r : ℕ) :
    m.degree (standardSummand c N r) ≼[m]
      m.degree (x r * normalizedRelation c (N - r)) := by
  rw [standardSummand, show
    C (pentagonTermCoefficient c N r * normalizationScalar c (N - r)) * x r *
        normalizedRelation c (N - r) =
      C (pentagonTermCoefficient c N r * normalizationScalar c (N - r)) *
        (x r * normalizedRelation c (N - r)) by ring]
  exact degree_C_mul_le m _ _

lemma degree_standardMain_le (c : ℂ) (m : MonomialOrder ℕ+) (N : ℕ) :
    m.degree
        (C (pentagonMainCoefficient c N * normalizationScalar c N) *
          normalizedRelation c N) ≼[m]
      m.degree (normalizedRelation c N) :=
  degree_C_mul_le m _ _

lemma family_one_standardSummand_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k r : ℕ} (hk : 1 ≤ k)
    (hr : r ∈ (((Finset.range (3 * k)).erase 0).erase k).erase (k + 1)) :
    mord.degree (standardSummand c (3 * k + 1) r) ≺[mord]
      mord.degree (x k * g c (2 * k + 1)) := by
  have hrs := hr
  simp only [Finset.mem_erase, Finset.mem_range] at hrs
  apply lt_of_le_of_lt (degree_standardSummand_le c mord (3 * k + 1) r)
  rw [degree_x_mul_normalizedRelation_eq c hc mord hmord (by omega) (by omega)]
  have hlt := degree_x_mul_g_lt_of_rho_lt c hc mord hmord
    (N := 3 * k + 1) (r := k) (s := r) (by omega) (by omega) (by omega) (by omega)
    (rho_family_one_strict (by omega) (by omega) (by omega))
  simpa [show 3 * k + 1 - k = 2 * k + 1 by omega] using hlt

lemma family_one_standardMain_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.degree
        (C (pentagonMainCoefficient c (3 * k + 1) * normalizationScalar c (3 * k + 1)) *
          normalizedRelation c (3 * k + 1)) ≺[mord]
      mord.degree (x k * g c (2 * k + 1)) := by
  apply lt_of_le_of_lt (degree_standardMain_le c mord (3 * k + 1))
  have hlt := degree_normalizedRelation_lt_x_mul_g c hc mord hmord
    (N := 3 * k + 1) (r := k) (by omega) (by omega) (by omega)
    (rho_family_one_lt_balanced hk)
  simpa [show 3 * k + 1 - k = 2 * k + 1 by omega] using hlt

lemma family_two_standardSummand_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k r : ℕ} (hk : 1 ≤ k)
    (hr : r ∈ (((Finset.range (3 * k + 1)).erase 0).erase k).erase (k + 1)) :
    mord.degree (standardSummand c (3 * k + 2) r) ≺[mord]
      mord.degree (x k * g c (2 * (k + 1))) := by
  have hrs := hr
  simp only [Finset.mem_erase, Finset.mem_range] at hrs
  apply lt_of_le_of_lt (degree_standardSummand_le c mord (3 * k + 2) r)
  rw [degree_x_mul_normalizedRelation_eq c hc mord hmord (by omega) (by omega)]
  have hlt := degree_x_mul_g_lt_of_rho_lt c hc mord hmord
    (N := 3 * k + 2) (r := k) (s := r) (by omega) (by omega) (by omega) (by omega)
    (rho_family_two_strict (by omega) (by omega) (by omega))
  simpa [show 3 * k + 2 - k = 2 * (k + 1) by omega] using hlt

lemma family_two_standardMain_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.degree
        (C (pentagonMainCoefficient c (3 * k + 2) * normalizationScalar c (3 * k + 2)) *
          normalizedRelation c (3 * k + 2)) ≺[mord]
      mord.degree (x k * g c (2 * (k + 1))) := by
  apply lt_of_le_of_lt (degree_standardMain_le c mord (3 * k + 2))
  have hlt := degree_normalizedRelation_lt_x_mul_g c hc mord hmord
    (N := 3 * k + 2) (r := k) (by omega) (by omega) (by omega)
    (rho_family_two_lt_balanced hk)
  simpa [show 3 * k + 2 - k = 2 * (k + 1) by omega] using hlt

lemma family_three_standardSummand_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k r : ℕ} (hk : 2 ≤ k)
    (hr : r ∈
      ((((Finset.range (3 * k - 1)).erase 0).erase (k - 1)).erase k).erase (k + 1)) :
    mord.degree (standardSummand c (3 * k) r) ≺[mord]
      mord.degree (x (k - 1) * g c (2 * k + 1)) := by
  have hrs := hr
  simp only [Finset.mem_erase, Finset.mem_range] at hrs
  apply lt_of_le_of_lt (degree_standardSummand_le c mord (3 * k) r)
  rw [degree_x_mul_normalizedRelation_eq c hc mord hmord (by omega) (by omega)]
  have hlt := degree_x_mul_g_lt_of_rho_lt c hc mord hmord
    (N := 3 * k) (r := k - 1) (s := r)
    (by omega) (by omega) (by omega) (by omega)
    (rho_family_three_strict hk (by omega) (by omega) (by omega) (by omega))
  simpa [show 3 * k - (k - 1) = 2 * k + 1 by omega] using hlt

lemma family_three_standardMain_lt (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 2 ≤ k) :
    mord.degree
        (C (pentagonMainCoefficient c (3 * k) * normalizationScalar c (3 * k)) *
          normalizedRelation c (3 * k)) ≺[mord]
      mord.degree (x (k - 1) * g c (2 * k + 1)) := by
  apply lt_of_le_of_lt (degree_standardMain_le c mord (3 * k))
  have hlt := degree_normalizedRelation_lt_x_mul_g c hc mord hmord
    (N := 3 * k) (r := k - 1) (by omega) (by omega) (by omega)
    (rho_family_three_lt_balanced hk)
  simpa [show 3 * k - (k - 1) = 2 * k + 1 by omega] using hlt

lemma monic_g_even (c : ℂ) (m : MonomialOrder ℕ+)
    (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.Monic (g c (2 * (i : ℕ))) := by
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
    degree_g_even c m hm, coeff_g_even_top]

lemma monic_normalized_g_odd (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.Monic (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S) := by
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
    degree_normalized_g_odd c hc m hm, coeff_C_mul, coeff_g_odd_top]
  exact inv_mul_cancel₀ (ne_zero_of_quadratic c hc)

lemma G_monic (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) :
    ∀ p ∈ G c, m.Monic p := by
  intro p hp
  rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact monic_g_even c m hm i
  · exact monic_normalized_g_odd c hc m hm i

lemma sPolynomial_even_odd_adjacent (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.sPolynomial (g c (2 * (i : ℕ)))
        (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S) =
      x (next i : ℕ) * g c (2 * (i : ℕ)) -
        x (i : ℕ) * (C c⁻¹ * g c (2 * (i : ℕ) + 1)) := by
  rw [m.sPolynomial_def, degree_g_even c m hm,
    degree_normalized_g_odd c hc m hm,
    (monic_g_even c m hm i).leadingCoeff_eq_one,
    (monic_normalized_g_odd c hc m hm i).leadingCoeff_eq_one,
    x_eq_X i, x_eq_X (next i)]
  have hleft :
      (Finsupp.single i 2 ⊔
          (Finsupp.single i 1 + Finsupp.single (next i) 1)) -
        Finsupp.single i 2 = Finsupp.single (next i) 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    by_cases hjnext : j = next i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    simp [Finsupp.sup_apply, hji, hjnext]
  have hright :
      (Finsupp.single i 2 ⊔
          (Finsupp.single i 1 + Finsupp.single (next i) 1)) -
        (Finsupp.single i 1 + Finsupp.single (next i) 1) =
          Finsupp.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    by_cases hjnext : j = next i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    simp [Finsupp.sup_apply, hji, hjnext]
  rw [hleft, hright]
  rfl

lemma sPolynomial_odd_even_adjacent (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.sPolynomial (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S)
        (g c (2 * (next i : ℕ))) =
      x (next i : ℕ) * (C c⁻¹ * g c (2 * (i : ℕ) + 1)) -
        x (i : ℕ) * g c (2 * (next i : ℕ)) := by
  rw [m.sPolynomial_def, degree_normalized_g_odd c hc m hm,
    degree_g_even c m hm,
    (monic_normalized_g_odd c hc m hm i).leadingCoeff_eq_one,
    (monic_g_even c m hm (next i)).leadingCoeff_eq_one,
    x_eq_X i, x_eq_X (next i)]
  have hleft :
      ((Finsupp.single i 1 + Finsupp.single (next i) 1) ⊔
          Finsupp.single (next i) 2) -
        (Finsupp.single i 1 + Finsupp.single (next i) 1) =
          Finsupp.single (next i) 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    by_cases hjnext : j = next i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    simp [Finsupp.sup_apply, hji, hjnext]
  have hright :
      ((Finsupp.single i 1 + Finsupp.single (next i) 1) ⊔
          Finsupp.single (next i) 2) - Finsupp.single (next i) 2 =
        Finsupp.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    by_cases hjnext : j = next i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    simp [Finsupp.sup_apply, hji, hjnext]
  rw [hleft, hright]
  rfl

lemma sPolynomial_odd_odd_adjacent (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) :
    m.sPolynomial (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S)
        (C c⁻¹ * g c (2 * (next i : ℕ) + 1) : S) =
      x (next (next i) : ℕ) * (C c⁻¹ * g c (2 * (i : ℕ) + 1)) -
        x (i : ℕ) * (C c⁻¹ * g c (2 * (next i : ℕ) + 1)) := by
  rw [m.sPolynomial_def, degree_normalized_g_odd c hc m hm,
    degree_normalized_g_odd c hc m hm,
    (monic_normalized_g_odd c hc m hm i).leadingCoeff_eq_one,
    (monic_normalized_g_odd c hc m hm (next i)).leadingCoeff_eq_one,
    x_eq_X i, x_eq_X (next (next i))]
  have hskip : next (next i) ≠ i := by
    intro h
    have hv := congrArg Subtype.val h
    change (i : ℕ) + 1 + 1 = (i : ℕ) at hv
    omega
  have hleft :
      ((Finsupp.single i 1 + Finsupp.single (next i) 1) ⊔
          (Finsupp.single (next i) 1 + Finsupp.single (next (next i)) 1)) -
        (Finsupp.single i 1 + Finsupp.single (next i) 1) =
          Finsupp.single (next (next i)) 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self, hskip]
    by_cases hjnext : j = next i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    by_cases hjnextnext : j = next (next i)
    · subst j
      simp [Finsupp.sup_apply, next_ne_self, hskip]
    simp [Finsupp.sup_apply, hji, hjnext, hjnextnext]
  have hright :
      ((Finsupp.single i 1 + Finsupp.single (next i) 1) ⊔
          (Finsupp.single (next i) 1 + Finsupp.single (next (next i)) 1)) -
        (Finsupp.single (next i) 1 + Finsupp.single (next (next i)) 1) =
          Finsupp.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self, hskip]
    by_cases hjnext : j = next i
    · subst j
      simp [Finsupp.sup_apply, next_ne_self]
    by_cases hjnextnext : j = next (next i)
    · subst j
      simp [Finsupp.sup_apply, next_ne_self, hskip]
    simp [Finsupp.sup_apply, hji, hjnext, hjnextnext]
  rw [hleft, hright]
  rfl

lemma family_one_syzygy_standard (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    C (pentagonScale c * c) *
          mord.sPolynomial (g c (2 * k)) (C c⁻¹ * g c (2 * k + 1) : S) +
        C (pentagonMainCoefficient c (3 * k + 1) *
            normalizationScalar c (3 * k + 1)) *
          normalizedRelation c (3 * k + 1) +
      ∑ r ∈ (((Finset.range (3 * k)).erase 0).erase k).erase (k + 1),
        C (pentagonTermCoefficient c (3 * k + 1) r *
            normalizationScalar c (3 * k + 1 - r)) *
          x r * normalizedRelation c (3 * k + 1 - r) = 0 := by
  have hkpos : 0 < k := hk
  let i : ℕ+ := ⟨k, hkpos⟩
  have h := pentagon_syzygy_normalized c hc (N := 3 * k + 1) (by omega)
  have hrange : 3 * k + 1 - 1 = 3 * k := by omega
  rw [hrange] at h
  have hkF : k ∈ (Finset.range (3 * k)).erase 0 := by simp; omega
  have hk1F : k + 1 ∈ ((Finset.range (3 * k)).erase 0).erase k := by simp; omega
  rw [← Finset.sum_erase_add _ _ hkF, ← Finset.sum_erase_add _ _ hk1F] at h
  rw [normalizedCoefficient_family_one_left c hc k,
    normalizedCoefficient_family_one_right c hc k] at h
  have hodd : normalizedRelation c (3 * k + 1 - k) =
      C c⁻¹ * g c (2 * k + 1) := by
    have hsub : 3 * k + 1 - k = 2 * k + 1 := by omega
    rw [hsub]
    simp [normalizedRelation]
  have heven : normalizedRelation c (3 * k + 1 - (k + 1)) = g c (2 * k) := by
    have hsub : 3 * k + 1 - (k + 1) = 2 * k := by omega
    rw [hsub]
    simp [normalizedRelation]
  rw [hodd, heven] at h
  have hsPoly := sPolynomial_even_odd_adjacent c hc mord hmord i
  change mord.sPolynomial (g c (2 * k)) (C c⁻¹ * g c (2 * k + 1)) =
    x (k + 1) * g c (2 * k) - x k * (C c⁻¹ * g c (2 * k + 1)) at hsPoly
  rw [hsPoly]
  have hneg : -pentagonScale c * c = -(pentagonScale c * c) := by ring
  rw [hneg, map_neg] at h
  linear_combination h

lemma family_two_syzygy_standard (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    C (pentagonScale c * c) *
          mord.sPolynomial (C c⁻¹ * g c (2 * k + 1) : S) (g c (2 * (k + 1))) +
        C (pentagonMainCoefficient c (3 * k + 2) *
            normalizationScalar c (3 * k + 2)) *
          normalizedRelation c (3 * k + 2) +
      ∑ r ∈ (((Finset.range (3 * k + 1)).erase 0).erase k).erase (k + 1),
        C (pentagonTermCoefficient c (3 * k + 2) r *
            normalizationScalar c (3 * k + 2 - r)) *
          x r * normalizedRelation c (3 * k + 2 - r) = 0 := by
  have hkpos : 0 < k := hk
  let i : ℕ+ := ⟨k, hkpos⟩
  have h := pentagon_syzygy_normalized c hc (N := 3 * k + 2) (by omega)
  have hrange : 3 * k + 2 - 1 = 3 * k + 1 := by omega
  rw [hrange] at h
  have hkF : k ∈ (Finset.range (3 * k + 1)).erase 0 := by simp; omega
  have hk1F : k + 1 ∈ ((Finset.range (3 * k + 1)).erase 0).erase k := by simp; omega
  rw [← Finset.sum_erase_add _ _ hkF, ← Finset.sum_erase_add _ _ hk1F] at h
  rw [normalizedCoefficient_family_two_left c hc k,
    normalizedCoefficient_family_two_right c hc k] at h
  have heven : normalizedRelation c (3 * k + 2 - k) = g c (2 * (k + 1)) := by
    have hsub : 3 * k + 2 - k = 2 * (k + 1) := by omega
    rw [hsub]
    simp [normalizedRelation]
  have hodd : normalizedRelation c (3 * k + 2 - (k + 1)) =
      C c⁻¹ * g c (2 * k + 1) := by
    have hsub : 3 * k + 2 - (k + 1) = 2 * k + 1 := by omega
    rw [hsub]
    simp [normalizedRelation]
  rw [heven, hodd] at h
  have hsPoly := sPolynomial_odd_even_adjacent c hc mord hmord i
  change mord.sPolynomial (C c⁻¹ * g c (2 * k + 1)) (g c (2 * (k + 1))) =
    x (k + 1) * (C c⁻¹ * g c (2 * k + 1)) - x k * g c (2 * (k + 1)) at hsPoly
  rw [hsPoly]
  have hneg : -pentagonScale c * c = -(pentagonScale c * c) := by ring
  rw [hneg, map_neg] at h
  linear_combination h

set_option maxHeartbeats 800000 in
lemma family_three_syzygy_standard (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 2 ≤ k) :
    C (-(pentagonScale c * c ^ 2)) *
          mord.sPolynomial (C c⁻¹ * g c (2 * k - 1) : S)
            (C c⁻¹ * g c (2 * k + 1) : S) +
        C (pentagonMainCoefficient c (3 * k) * normalizationScalar c (3 * k)) *
          normalizedRelation c (3 * k) +
      ∑ r ∈
          ((((Finset.range (3 * k - 1)).erase 0).erase (k - 1)).erase k).erase (k + 1),
        C (pentagonTermCoefficient c (3 * k) r *
            normalizationScalar c (3 * k - r)) *
          x r * normalizedRelation c (3 * k - r) = 0 := by
  have hkprev : 0 < k - 1 := by
    omega
  let i : ℕ+ := ⟨k - 1, hkprev⟩
  have hN : 2 ≤ 3 * k := by omega
  have h := pentagon_syzygy_normalized c hc (N := 3 * k) hN
  have hkprevF : k - 1 ∈ (Finset.range (3 * k - 1)).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hkF : k ∈ ((Finset.range (3 * k - 1)).erase 0).erase (k - 1) := by
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hknextF : k + 1 ∈
      (((Finset.range (3 * k - 1)).erase 0).erase (k - 1)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  rw [← Finset.sum_erase_add _ _ hkprevF,
    ← Finset.sum_erase_add _ _ hkF,
    ← Finset.sum_erase_add _ _ hknextF] at h
  have hkone : 1 ≤ k := by omega
  rw [normalizedCoefficient_family_three_left c hc hkone,
    normalizedCoefficient_family_three_center c hc k,
    normalizedCoefficient_family_three_right c hc hkone] at h
  have hoddNext : normalizedRelation c (3 * k - (k - 1)) =
      C c⁻¹ * g c (2 * k + 1) := by
    have hsub : 3 * k - (k - 1) = 2 * k + 1 := by omega
    rw [hsub]
    simp [normalizedRelation]
  have hoddPrev : normalizedRelation c (3 * k - (k + 1)) =
      C c⁻¹ * g c (2 * k - 1) := by
    have hsub : 3 * k - (k + 1) = 2 * k - 1 := by omega
    rw [hsub]
    have hodd : ¬2 ∣ 2 * k - 1 := by omega
    simp [normalizedRelation, hodd]
  rw [hoddNext, hoddPrev] at h
  simp only [map_zero, zero_mul, add_zero] at h
  have hi : (i : ℕ) = k - 1 := rfl
  have hinext : (next i : ℕ) = k := by simp [next, hi]; omega
  have hinextnext : (next (next i) : ℕ) = k + 1 := by
    simp [next]
    omega
  have hprevArg : 2 * (i : ℕ) + 1 = 2 * k - 1 := by omega
  have hnextArg : 2 * (next i : ℕ) + 1 = 2 * k + 1 := by omega
  have hsPoly : mord.sPolynomial (C c⁻¹ * g c (2 * k - 1))
      (C c⁻¹ * g c (2 * k + 1)) =
        x (k + 1) * (C c⁻¹ * g c (2 * k - 1)) -
          x (k - 1) * (C c⁻¹ * g c (2 * k + 1)) := by
    have hsBase := sPolynomial_odd_odd_adjacent c hc mord hmord i
    rw [hprevArg, hnextArg, hinextnext, hi] at hsBase
    exact hsBase
  rw [hsPoly]
  simp only [map_neg, mul_sub, neg_mul, mul_neg, neg_neg, mul_assoc] at h ⊢
  abel_nf at h ⊢
  exact h

lemma G_leadingCoeff_isUnit (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) :
    ∀ p ∈ G c, IsUnit (m.leadingCoeff p) := by
  intro p hp
  rw [isUnit_iff_ne_zero, m.leadingCoeff_ne_zero_iff]
  rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact g_even_ne_zero c m hm i
  · exact mul_ne_zero (by simp [ne_zero_of_quadratic c hc])
      (g_odd_ne_zero c hc m hm i)

lemma isRemainder_zero_of_finset_representation (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (p : S)
    (B : Finset (G c)) (q : G c → S)
    (hsum : p = ∑ b ∈ B, q b * b.val)
    (hdeg : ∀ b ∈ B, m.degree (b.val * q b) ≼[m] m.degree p) :
    m.IsRemainder p (G c) 0 := by
  rw [MonomialOrder.IsRemainder.isRemainder_iff_degree
    (f := p) (B := G c) (r := 0)
    (fun b hb ↦ (G_leadingCoeff_isUnit c hc m hm b hb).mem_nonZeroDivisors)]
  constructor
  · let q' : G c → S := fun b ↦ if b ∈ B then q b else 0
    let q₀ : G c →₀ S := Finsupp.onFinset B q' (by
      intro a ha
      by_contra hnot
      simp [q', hnot] at ha)
    refine ⟨q₀, ?_, ?_⟩
    · rw [add_zero, Finsupp.linearCombination_apply, Finsupp.sum]
      have hsum' : p = ∑ b ∈ B, q' b * b.val := by simpa [q'] using hsum
      rw [hsum']
      simp only [q₀, q', Finsupp.support_onFinset, Finsupp.onFinset_apply,
        ite_mul, zero_mul, Finset.sum_ite_mem, smul_eq_mul]
      symm
      apply Finset.sum_subset
      · simp
      · intro a haB haT
        simp only [Finset.mem_inter, Finset.mem_filter] at haT
        simp_all
    · intro b
      by_cases hb : b ∈ B
      · simpa [q₀, q', Finsupp.onFinset_apply, hb, mul_comm] using hdeg b hb
      · simp [q₀, q', Finsupp.onFinset_apply, hb]
  · simp

lemma hasStandardRepresentation_of_finset (m : MonomialOrder ℕ+)
    (G₀ : Set S) (p : S) (d : m.syn) (hd : 0 < d)
    (u : ℂ) (hu : u ≠ 0) {ι : Type*} (T : Finset ι)
    (b : ι → G₀) (a : ι → S)
    (heq : C u * p + ∑ i ∈ T, a i * (b i).val = 0)
    (hdeg : ∀ i ∈ T, m.toSyn (m.degree (a i * (b i).val)) < d) :
    m.HasStandardRepresentation G₀ p d := by
  classical
  let q : G₀ →₀ S := ∑ i ∈ T,
    Finsupp.single (b i) (-C u⁻¹ * a i)
  refine ⟨q, ?_, ?_⟩
  · have heq' : C u * p = -(∑ i ∈ T, a i * (b i).val) :=
      eq_neg_of_add_eq_zero_left heq
    calc
      p = C u⁻¹ * (C u * p) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
      _ = ∑ i ∈ T, (-C u⁻¹ * a i) * (b i).val := by
        rw [heq', mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = Finsupp.linearCombination S (fun z : G₀ ↦ z.val) q := by
        symm
        simp only [q, map_sum, Finsupp.linearCombination_single, smul_eq_mul]
  · intro z hz
    have hsum : z.val * q z =
        ∑ i ∈ T, z.val * (Finsupp.single (b i) (-C u⁻¹ * a i)) z := by
      simp [q, Finset.mul_sum]
    rw [hsum]
    rw [← m.toSyn.apply_symm_apply d]
    change m.degree (∑ i ∈ T,
      z.val * (Finsupp.single (b i) (-C u⁻¹ * a i)) z) ≺[m] m.toSyn.symm d
    apply degree_finset_sum_lt m T _ (m.toSyn.symm d)
    · simpa using hd
    intro i hi
    by_cases hbi : b i = z
    · subst z
      simp only [Finsupp.single_eq_same]
      rw [show (b i).val * (-C u⁻¹ * a i) =
          C (-u⁻¹) * (a i * (b i).val) by rw [map_neg]; ring]
      apply lt_of_le_of_lt (degree_C_mul_le m (-u⁻¹) (a i * (b i).val))
      have hi := hdeg i hi
      rw [← m.toSyn.apply_symm_apply d] at hi
      change m.degree (a i * (b i).val) ≺[m] m.toSyn.symm d at hi
      simpa [mul_comm, mul_left_comm, mul_assoc] using hi
    · have hzbi : z ≠ b i := Ne.symm hbi
      simp [Finsupp.single_apply, hzbi]
      exact hd

lemma product_hasStandardRepresentation (m : MonomialOrder ℕ+) (G₀ : Set S)
    (f g : S) (hfG : f ∈ G₀) (hgG : g ∈ G₀)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfmonic : m.leadingCoeff f = 1) (hgmonic : m.leadingCoeff g = 1)
    (hsup : m.degree f ⊔ m.degree g = m.degree f + m.degree g) :
    m.HasStandardRepresentation G₀ (m.sPolynomial f g)
      (m.toSyn (m.degree f ⊔ m.degree g)) := by
  classical
  let bf : G₀ := ⟨f, hfG⟩
  let bg : G₀ := ⟨g, hgG⟩
  let q : G₀ →₀ S :=
    Finsupp.single bf (-(g - m.leadingTerm g)) +
      Finsupp.single bg (f - m.leadingTerm f)
  have hleft : (m.degree f + m.degree g) - m.degree f = m.degree g :=
    add_tsub_cancel_left _ _
  have hright : (m.degree f + m.degree g) - m.degree g = m.degree f := by
    rw [add_comm]
    exact add_tsub_cancel_left _ _
  have hsp : m.sPolynomial f g =
      m.leadingTerm g * f - m.leadingTerm f * g := by
    rw [m.sPolynomial_def, hsup, hleft, hright, hfmonic, hgmonic]
    simp only [MonomialOrder.leadingTerm, hfmonic, hgmonic]
  refine ⟨q, ?_, ?_⟩
  · rw [hsp]
    simp only [q, map_add, Finsupp.linearCombination_single, smul_eq_mul]
    ring
  · intro b hb
    by_cases hfg : bf = bg
    · have hfgval : f = g := congrArg Subtype.val hfg
      have hq0 : q = 0 := by
        apply Finsupp.ext
        intro z
        change (Finsupp.single bf (-(g - m.leadingTerm g)) +
          Finsupp.single bg (f - m.leadingTerm f)) z = 0
        rw [← hfgval, ← hfg]
        simp
      rw [hq0] at hb
      exact (hb rfl).elim
    by_cases hbf : b = bf
    · subst b
      have htail : g - m.leadingTerm g ≠ 0 := by
        intro hzero
        have : q bf = 0 := by simp [q, hfg, hzero]
        exact hb this
      have hqbf : q bf = -(g - m.leadingTerm g) := by simp [q, hfg]
      rw [hqbf]
      change m.toSyn (m.degree (f * -(g - m.leadingTerm g))) <
        m.toSyn (m.degree f ⊔ m.degree g)
      apply lt_of_le_of_lt m.toSyn_degree_mul_le
      rw [hsup, AddEquiv.map_add]
      apply add_lt_add_right _ _
      rw [m.degree_neg]
      exact m.degree_sub_leadingTerm_lt_degree
        (m.degree_ne_zero_of_sub_leadingTerm_ne_zero htail)
    by_cases hbg : b = bg
    · subst b
      have htail : f - m.leadingTerm f ≠ 0 := by
        intro hzero
        have : q bg = 0 := by simp [q, hfg, hzero]
        exact hb this
      have hqbg : q bg = f - m.leadingTerm f := by simp [q, hfg]
      rw [hqbg]
      change m.toSyn (m.degree (g * (f - m.leadingTerm f))) <
        m.toSyn (m.degree f ⊔ m.degree g)
      apply lt_of_le_of_lt m.toSyn_degree_mul_le
      rw [hsup, AddEquiv.map_add]
      simpa only [add_comm] using add_lt_add_right
        (m.degree_sub_leadingTerm_lt_degree
          (m.degree_ne_zero_of_sub_leadingTerm_ne_zero htail)) (m.toSyn (m.degree g))
    · have : q b = 0 := by simp [q, hbf, hbg]
      exact (hb this).elim

lemma HasStandardRepresentation.neg {m : MonomialOrder ℕ+} {G₀ : Set S}
    {p : S} {d : m.syn} (h : m.HasStandardRepresentation G₀ p d) :
    m.HasStandardRepresentation G₀ (-p) d := by
  rcases h with ⟨q, hq, hdeg⟩
  refine ⟨-q, ?_, ?_⟩
  · rw [hq, map_neg]
  · intro b hb
    have hb' : q b ≠ 0 := by simpa using hb
    simpa using hdeg b hb'

lemma HasStandardRepresentation.sPolynomial_swap {m : MonomialOrder ℕ+}
    {G₀ : Set S} {f g : S}
    (h : m.HasStandardRepresentation G₀ (m.sPolynomial f g)
      (m.toSyn (m.degree f ⊔ m.degree g))) :
    m.HasStandardRepresentation G₀ (m.sPolynomial g f)
      (m.toSyn (m.degree g ⊔ m.degree f)) := by
  rw [m.sPolynomial_antisymm, sup_comm]
  exact HasStandardRepresentation.neg h

lemma zero_hasStandardRepresentation (m : MonomialOrder ℕ+) (G₀ : Set S) (d : m.syn) :
    m.HasStandardRepresentation G₀ 0 d := by
  refine ⟨0, by simp, ?_⟩
  simp

lemma sup_even_even_eq_add {i j : ℕ+} (hij : i ≠ j) :
    Finsupp.single i 2 ⊔ Finsupp.single j 2 =
      Finsupp.single i 2 + Finsupp.single j 2 := by
  ext t
  by_cases hti : t = i
  · subst t
    simp [Finsupp.sup_apply, hij]
  by_cases htj : t = j
  · subst t
    simp [Finsupp.sup_apply, hij]
  simp [Finsupp.sup_apply, hti, htj]

lemma sup_even_odd_eq_add {i j : ℕ+} (hij : i ≠ j) (hinext : i ≠ next j) :
    Finsupp.single i 2 ⊔
        (Finsupp.single j 1 + Finsupp.single (next j) 1) =
      Finsupp.single i 2 +
        (Finsupp.single j 1 + Finsupp.single (next j) 1) := by
  ext t
  by_cases hti : t = i
  · subst t
    simp [Finsupp.sup_apply, hij, hinext]
  by_cases htj : t = j
  · subst t
    simp [Finsupp.sup_apply, hij, next_ne_self]
  by_cases htnext : t = next j
  · subst t
    simp [Finsupp.sup_apply, hinext, next_ne_self]
  simp [Finsupp.sup_apply, hti, htj, htnext]

lemma sup_odd_odd_eq_add {i j : ℕ+} (hij : i ≠ j)
    (hinext : i ≠ next j) (hnexti : next i ≠ j) :
    (Finsupp.single i 1 + Finsupp.single (next i) 1) ⊔
        (Finsupp.single j 1 + Finsupp.single (next j) 1) =
      (Finsupp.single i 1 + Finsupp.single (next i) 1) +
        (Finsupp.single j 1 + Finsupp.single (next j) 1) := by
  have hnextnext : next i ≠ next j := by
    intro h
    apply hij
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    change (i : ℕ) + 1 = (j : ℕ) + 1 at hv
    exact Nat.add_right_cancel hv
  ext t
  by_cases hti : t = i
  · subst t
    simp [Finsupp.sup_apply, hij, hinext, next_ne_self]
  by_cases htni : t = next i
  · subst t
    simp [Finsupp.sup_apply, hnexti, hnextnext, next_ne_self]
  by_cases htj : t = j
  · subst t
    simp [Finsupp.sup_apply, hij, hnexti, next_ne_self]
  by_cases htnj : t = next j
  · subst t
    simp [Finsupp.sup_apply, hinext, hnextnext, next_ne_self]
  simp [Finsupp.sup_apply, hti, htni, htj, htnj]

set_option maxHeartbeats 800000 in
lemma family_one_hasStandardRepresentation (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.HasStandardRepresentation (G c)
      (mord.sPolynomial (g c (2 * k)) (C c⁻¹ * g c (2 * k + 1) : S))
      (mord.toSyn (mord.degree (x k * g c (2 * k + 1)))) := by
  let L := (((Finset.range (3 * k)).erase 0).erase k).erase (k + 1)
  let ι := Option {r : ℕ // r ∈ L}
  let b : ι → G c
    | none => ⟨normalizedRelation c (3 * k + 1),
        normalizedRelation_mem_G c hc (by omega)⟩
    | some r => ⟨normalizedRelation c (3 * k + 1 - r.val),
        normalizedRelation_mem_G c hc (by
          have hr := r.prop
          simp only [L, Finset.mem_erase, Finset.mem_range] at hr
          omega)⟩
  let a : ι → S
    | none => C (pentagonMainCoefficient c (3 * k + 1) *
        normalizationScalar c (3 * k + 1))
    | some r => C (pentagonTermCoefficient c (3 * k + 1) r.val *
        normalizationScalar c (3 * k + 1 - r.val)) * x r.val
  have hd : 0 < mord.toSyn (mord.degree (x k * g c (2 * k + 1))) := by
    rw [mord.toSyn_lt_iff_ne_zero, mord.toSyn.map_ne_zero_iff]
    intro hzero
    have hw := weightedDegree_degree_x_mul_g c hc mord hmord
      (N := 3 * k + 1) (r := k) (by omega) (by omega)
    rw [show 3 * k + 1 - k = 2 * k + 1 by omega, hzero] at hw
    simp [weightedDegree] at hw
  apply hasStandardRepresentation_of_finset mord (G c) _ _ hd
    (pentagonScale c * c) (mul_ne_zero (pentagonScale_ne_zero c hc)
      (ne_zero_of_quadratic c hc)) Finset.univ b a
  · change C (pentagonScale c * c) *
        mord.sPolynomial (g c (2 * k)) (C c⁻¹ * g c (2 * k + 1) : S) +
      ∑ i : ι, a i * (b i).val = 0
    rw [Fintype.sum_option]
    dsimp only [a, b]
    change C (pentagonScale c * c) *
        mord.sPolynomial (g c (2 * k)) (C c⁻¹ * g c (2 * k + 1) : S) +
      (C (pentagonMainCoefficient c (3 * k + 1) * normalizationScalar c (3 * k + 1)) *
          normalizedRelation c (3 * k + 1) +
        ∑ r ∈ L.attach, standardSummand c (3 * k + 1) r.val) = 0
    rw [Finset.sum_attach]
    simpa only [L, standardSummand, map_mul, mul_assoc, add_assoc] using
      family_one_syzygy_standard c hc mord hmord hk
  · intro i hi
    cases i with
    | none =>
        simpa [a, b] using
          (family_one_standardMain_lt c hc mord hmord hk)
    | some r =>
        simpa [a, b, L, standardSummand] using
          (family_one_standardSummand_lt c hc mord hmord hk r.prop)

set_option maxHeartbeats 800000 in
lemma family_two_hasStandardRepresentation (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.HasStandardRepresentation (G c)
      (mord.sPolynomial (C c⁻¹ * g c (2 * k + 1) : S) (g c (2 * (k + 1))))
      (mord.toSyn (mord.degree (x k * g c (2 * (k + 1))))) := by
  let L := (((Finset.range (3 * k + 1)).erase 0).erase k).erase (k + 1)
  let ι := Option {r : ℕ // r ∈ L}
  let b : ι → G c
    | none => ⟨normalizedRelation c (3 * k + 2),
        normalizedRelation_mem_G c hc (by omega)⟩
    | some r => ⟨normalizedRelation c (3 * k + 2 - r.val),
        normalizedRelation_mem_G c hc (by
          have hr := r.prop
          simp only [L, Finset.mem_erase, Finset.mem_range] at hr
          omega)⟩
  let a : ι → S
    | none => C (pentagonMainCoefficient c (3 * k + 2) *
        normalizationScalar c (3 * k + 2))
    | some r => C (pentagonTermCoefficient c (3 * k + 2) r.val *
        normalizationScalar c (3 * k + 2 - r.val)) * x r.val
  have hd : 0 < mord.toSyn (mord.degree (x k * g c (2 * (k + 1)))) := by
    rw [mord.toSyn_lt_iff_ne_zero, mord.toSyn.map_ne_zero_iff]
    intro hzero
    have hw := weightedDegree_degree_x_mul_g c hc mord hmord
      (N := 3 * k + 2) (r := k) (by omega) (by omega)
    rw [show 3 * k + 2 - k = 2 * (k + 1) by omega, hzero] at hw
    simp [weightedDegree] at hw
  apply hasStandardRepresentation_of_finset mord (G c) _ _ hd
    (pentagonScale c * c) (mul_ne_zero (pentagonScale_ne_zero c hc)
      (ne_zero_of_quadratic c hc)) Finset.univ b a
  · change C (pentagonScale c * c) *
        mord.sPolynomial (C c⁻¹ * g c (2 * k + 1) : S) (g c (2 * (k + 1))) +
      ∑ i : ι, a i * (b i).val = 0
    rw [Fintype.sum_option]
    dsimp only [a, b]
    change C (pentagonScale c * c) *
        mord.sPolynomial (C c⁻¹ * g c (2 * k + 1) : S) (g c (2 * (k + 1))) +
      (C (pentagonMainCoefficient c (3 * k + 2) * normalizationScalar c (3 * k + 2)) *
          normalizedRelation c (3 * k + 2) +
        ∑ r ∈ L.attach, standardSummand c (3 * k + 2) r.val) = 0
    rw [Finset.sum_attach]
    simpa only [L, standardSummand, map_mul, mul_assoc, add_assoc] using
      family_two_syzygy_standard c hc mord hmord hk
  · intro i hi
    cases i with
    | none =>
        simpa [a, b] using
          (family_two_standardMain_lt c hc mord hmord hk)
    | some r =>
        simpa [a, b, L, standardSummand] using
          (family_two_standardSummand_lt c hc mord hmord hk r.prop)

set_option maxHeartbeats 800000 in
lemma family_three_hasStandardRepresentation (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 2 ≤ k) :
    mord.HasStandardRepresentation (G c)
      (mord.sPolynomial (C c⁻¹ * g c (2 * k - 1) : S)
        (C c⁻¹ * g c (2 * k + 1) : S))
      (mord.toSyn (mord.degree (x (k - 1) * g c (2 * k + 1)))) := by
  let L := ((((Finset.range (3 * k - 1)).erase 0).erase (k - 1)).erase k).erase (k + 1)
  let ι := Option {r : ℕ // r ∈ L}
  let b : ι → G c
    | none => ⟨normalizedRelation c (3 * k), normalizedRelation_mem_G c hc (by omega)⟩
    | some r => ⟨normalizedRelation c (3 * k - r.val),
        normalizedRelation_mem_G c hc (by
          have hr := r.prop
          simp only [L, Finset.mem_erase, Finset.mem_range] at hr
          omega)⟩
  let a : ι → S
    | none => C (pentagonMainCoefficient c (3 * k) * normalizationScalar c (3 * k))
    | some r => C (pentagonTermCoefficient c (3 * k) r.val *
        normalizationScalar c (3 * k - r.val)) * x r.val
  have hd : 0 < mord.toSyn (mord.degree (x (k - 1) * g c (2 * k + 1))) := by
    rw [mord.toSyn_lt_iff_ne_zero, mord.toSyn.map_ne_zero_iff]
    intro hzero
    have hw := weightedDegree_degree_x_mul_g c hc mord hmord
      (N := 3 * k) (r := k - 1) (by omega) (by omega)
    rw [show 3 * k - (k - 1) = 2 * k + 1 by omega, hzero] at hw
    simp [weightedDegree] at hw
    omega
  apply hasStandardRepresentation_of_finset mord (G c) _ _ hd
    (-(pentagonScale c * c ^ 2))
    (neg_ne_zero.mpr (mul_ne_zero (pentagonScale_ne_zero c hc)
      (pow_ne_zero 2 (ne_zero_of_quadratic c hc)))) Finset.univ b a
  · change C (-(pentagonScale c * c ^ 2)) *
        mord.sPolynomial (C c⁻¹ * g c (2 * k - 1) : S)
          (C c⁻¹ * g c (2 * k + 1) : S) +
      ∑ i : ι, a i * (b i).val = 0
    rw [Fintype.sum_option]
    dsimp only [a, b]
    change C (-(pentagonScale c * c ^ 2)) *
        mord.sPolynomial (C c⁻¹ * g c (2 * k - 1) : S)
          (C c⁻¹ * g c (2 * k + 1) : S) +
      (C (pentagonMainCoefficient c (3 * k) * normalizationScalar c (3 * k)) *
          normalizedRelation c (3 * k) +
        ∑ r ∈ L.attach, standardSummand c (3 * k) r.val) = 0
    rw [Finset.sum_attach]
    simpa only [L, standardSummand, map_mul, mul_assoc, add_assoc] using
      family_three_syzygy_standard c hc mord hmord hk
  · intro i hi
    cases i with
    | none =>
        simpa [a, b] using
          (family_three_standardMain_lt c hc mord hmord hk)
    | some r =>
        simpa [a, b, L, standardSummand] using
          (family_three_standardSummand_lt c hc mord hmord hk r.prop)

lemma degree_family_one_top_eq_sup (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.degree (x k * g c (2 * k + 1)) =
      mord.degree (g c (2 * k)) ⊔
        mord.degree (C c⁻¹ * g c (2 * k + 1) : S) := by
  let i : ℕ+ := ⟨k, hk⟩
  have hx : x k = X i := by simpa [i] using x_eq_X i
  rw [hx]
  change mord.degree (X i * g c (2 * (i : ℕ) + 1)) =
    mord.degree (g c (2 * (i : ℕ))) ⊔
      mord.degree (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S)
  rw [mord.degree_mul (by simp) (g_odd_ne_zero c hc mord hmord i),
    mord.degree_X, degree_g_odd c hc mord hmord i,
    degree_g_even c mord hmord i, degree_normalized_g_odd c hc mord hmord i]
  ext j
  by_cases hji : j = i
  · subst j
    simp [Finsupp.sup_apply, next_ne_self]
  by_cases hjnext : j = next i
  · subst j
    simp [Finsupp.sup_apply, next_ne_self]
  simp [Finsupp.sup_apply, hji, hjnext]

lemma degree_family_two_top_eq_sup (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.degree (x k * g c (2 * (k + 1))) =
      mord.degree (C c⁻¹ * g c (2 * k + 1) : S) ⊔
        mord.degree (g c (2 * (k + 1))) := by
  let i : ℕ+ := ⟨k, hk⟩
  have hx : x k = X i := by simpa [i] using x_eq_X i
  rw [hx]
  change mord.degree (X i * g c (2 * (next i : ℕ))) =
    mord.degree (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S) ⊔
      mord.degree (g c (2 * (next i : ℕ)))
  rw [mord.degree_mul (by simp) (g_even_ne_zero c mord hmord (next i)),
    mord.degree_X,
    degree_g_even c mord hmord (next i),
    degree_normalized_g_odd c hc mord hmord i]
  ext j
  by_cases hji : j = i
  · subst j
    simp [Finsupp.sup_apply, next_ne_self]
  by_cases hjnext : j = next i
  · subst j
    simp [Finsupp.sup_apply, next_ne_self]
  simp [Finsupp.sup_apply, hji, hjnext]

lemma degree_family_three_top_eq_sup (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 2 ≤ k) :
    mord.degree (x (k - 1) * g c (2 * k + 1)) =
      mord.degree (C c⁻¹ * g c (2 * k - 1) : S) ⊔
        mord.degree (C c⁻¹ * g c (2 * k + 1) : S) := by
  let i : ℕ+ := ⟨k - 1, by omega⟩
  have hnext : (next i : ℕ) = k := by simp [i, next]; omega
  have hx : x (k - 1) = X i := by simpa [i] using x_eq_X i
  have hprevArg : 2 * k - 1 = 2 * (i : ℕ) + 1 := by
    simp [i]
    omega
  have hnextArg : 2 * k + 1 = 2 * (next i : ℕ) + 1 := by omega
  rw [hx, hnextArg, hprevArg, mord.degree_mul (by simp)
      (by simpa [hnext] using g_odd_ne_zero c hc mord hmord (next i)),
    mord.degree_X,
    degree_g_odd c hc mord hmord (next i),
    degree_normalized_g_odd c hc mord hmord i,
    degree_normalized_g_odd c hc mord hmord (next i)]
  have hskip : next (next i) ≠ i := by
    intro h
    have hv := congrArg Subtype.val h
    change (i : ℕ) + 1 + 1 = (i : ℕ) at hv
    omega
  ext j
  by_cases hji : j = i
  · subst j
    simp [Finsupp.sup_apply, next_ne_self, hskip]
  by_cases hjnext : j = next i
  · subst j
    simp [Finsupp.sup_apply, next_ne_self]
  by_cases hjnextnext : j = next (next i)
  · subst j
    simp [Finsupp.sup_apply, next_ne_self, hskip]
  simp [Finsupp.sup_apply, hji, hjnext, hjnextnext]

lemma family_one_hasStandardRepresentation_lcm (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.HasStandardRepresentation (G c)
      (mord.sPolynomial (g c (2 * k)) (C c⁻¹ * g c (2 * k + 1) : S))
      (mord.toSyn (mord.degree (g c (2 * k)) ⊔
        mord.degree (C c⁻¹ * g c (2 * k + 1) : S))) := by
  rw [← degree_family_one_top_eq_sup c hc mord hmord hk]
  exact family_one_hasStandardRepresentation c hc mord hmord hk

lemma family_two_hasStandardRepresentation_lcm (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 1 ≤ k) :
    mord.HasStandardRepresentation (G c)
      (mord.sPolynomial (C c⁻¹ * g c (2 * k + 1) : S) (g c (2 * (k + 1))))
      (mord.toSyn (mord.degree (C c⁻¹ * g c (2 * k + 1) : S) ⊔
        mord.degree (g c (2 * (k + 1))))) := by
  rw [← degree_family_two_top_eq_sup c hc mord hmord hk]
  exact family_two_hasStandardRepresentation c hc mord hmord hk

lemma family_three_hasStandardRepresentation_lcm (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord)
    {k : ℕ} (hk : 2 ≤ k) :
    mord.HasStandardRepresentation (G c)
      (mord.sPolynomial (C c⁻¹ * g c (2 * k - 1) : S)
        (C c⁻¹ * g c (2 * k + 1) : S))
      (mord.toSyn (mord.degree (C c⁻¹ * g c (2 * k - 1) : S) ⊔
        mord.degree (C c⁻¹ * g c (2 * k + 1) : S))) := by
  rw [← degree_family_three_top_eq_sup c hc mord hmord hk]
  exact family_three_hasStandardRepresentation c hc mord hmord hk

set_option maxHeartbeats 1000000 in
lemma all_sPolynomials_haveStandardRepresentation (c : ℂ) (hc : c ^ 2 + c = 1)
    (mord : MonomialOrder ℕ+) (hmord : IsCaseIMonomialOrder mord) :
    ∀ f g : G c, mord.HasStandardRepresentation (G c)
      (mord.sPolynomial f.val g.val)
      (mord.toSyn (mord.degree f.val ⊔ mord.degree g.val)) := by
  rintro ⟨f, hf⟩ ⟨g', hg⟩
  rcases hf with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases hg with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · by_cases hij : i = j
    · subst j
      simpa using zero_hasStandardRepresentation mord (G c)
        (mord.toSyn (mord.degree (g c (2 * (i : ℕ))) ⊔
          mord.degree (g c (2 * (i : ℕ)))))
    · apply product_hasStandardRepresentation mord (G c)
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inl ⟨j, rfl⟩
      · exact g_even_ne_zero c mord hmord i
      · exact g_even_ne_zero c mord hmord j
      · exact (monic_g_even c mord hmord i).leadingCoeff_eq_one
      · exact (monic_g_even c mord hmord j).leadingCoeff_eq_one
      · rw [degree_g_even c mord hmord i, degree_g_even c mord hmord j]
        exact sup_even_even_eq_add hij
  · by_cases hij : i = j
    · subst j
      exact family_one_hasStandardRepresentation_lcm c hc mord hmord i.prop
    by_cases hinext : i = next j
    · subst i
      have h := HasStandardRepresentation.sPolynomial_swap
        (family_two_hasStandardRepresentation_lcm c hc mord hmord j.prop)
      exact h
    · apply product_hasStandardRepresentation mord (G c)
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
      · exact g_even_ne_zero c mord hmord i
      · exact mul_ne_zero (by simp [ne_zero_of_quadratic c hc])
          (g_odd_ne_zero c hc mord hmord j)
      · exact (monic_g_even c mord hmord i).leadingCoeff_eq_one
      · exact (monic_normalized_g_odd c hc mord hmord j).leadingCoeff_eq_one
      · rw [degree_g_even c mord hmord i,
          degree_normalized_g_odd c hc mord hmord j]
        exact sup_even_odd_eq_add hij hinext
  · by_cases hij : i = j
    · subst j
      exact HasStandardRepresentation.sPolynomial_swap
        (family_one_hasStandardRepresentation_lcm c hc mord hmord i.prop)
    by_cases hnext : next i = j
    · subst j
      exact family_two_hasStandardRepresentation_lcm c hc mord hmord i.prop
    · apply product_hasStandardRepresentation mord (G c)
      · exact Or.inr ⟨i, rfl⟩
      · exact Or.inl ⟨j, rfl⟩
      · exact mul_ne_zero (by simp [ne_zero_of_quadratic c hc])
          (g_odd_ne_zero c hc mord hmord i)
      · exact g_even_ne_zero c mord hmord j
      · exact (monic_normalized_g_odd c hc mord hmord i).leadingCoeff_eq_one
      · exact (monic_g_even c mord hmord j).leadingCoeff_eq_one
      · rw [degree_normalized_g_odd c hc mord hmord i,
          degree_g_even c mord hmord j, sup_comm]
        rw [sup_even_odd_eq_add (Ne.symm hij) (Ne.symm hnext), add_comm]
  · by_cases hij : i = j
    · subst j
      rw [mord.sPolynomial_self]
      exact zero_hasStandardRepresentation mord (G c) _
    by_cases hnexti : next i = j
    · subst j
      have hjtwo : 2 ≤ (next i : ℕ) := by
        change 2 ≤ (i : ℕ) + 1
        exact Nat.succ_le_succ i.prop
      have h := family_three_hasStandardRepresentation_lcm c hc mord hmord hjtwo
      have hprev : 2 * (next i : ℕ) - 1 = 2 * (i : ℕ) + 1 := by
        simp [next]
        omega
      rw [hprev] at h
      exact h
    by_cases hinext : i = next j
    · subst i
      have hitwo : 2 ≤ (next j : ℕ) := by
        change 2 ≤ (j : ℕ) + 1
        exact Nat.succ_le_succ j.prop
      have h := family_three_hasStandardRepresentation_lcm c hc mord hmord hitwo
      have hprev : 2 * (next j : ℕ) - 1 = 2 * (j : ℕ) + 1 := by
        simp [next]
        omega
      rw [hprev] at h
      exact HasStandardRepresentation.sPolynomial_swap h
    · apply product_hasStandardRepresentation mord (G c)
      · exact Or.inr ⟨i, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
      · exact mul_ne_zero (by simp [ne_zero_of_quadratic c hc])
          (g_odd_ne_zero c hc mord hmord i)
      · exact mul_ne_zero (by simp [ne_zero_of_quadratic c hc])
          (g_odd_ne_zero c hc mord hmord j)
      · exact (monic_normalized_g_odd c hc mord hmord i).leadingCoeff_eq_one
      · exact (monic_normalized_g_odd c hc mord hmord j).leadingCoeff_eq_one
      · rw [degree_normalized_g_odd c hc mord hmord i,
          degree_normalized_g_odd c hc mord hmord j]
        exact sup_odd_odd_eq_add hij hinext hnexti

/-- The monomial ideal `J = (xᵢ², xᵢxᵢ₊₁ : i ≥ 1)`. -/
noncomputable def J : Ideal S :=
  Ideal.span
    (Set.range (fun i : ℕ+ ↦ monomial (Finsupp.single i 2) 1) ∪
      Set.range (fun i : ℕ+ ↦
        monomial (Finsupp.single i 1 + Finsupp.single (next i) 1) 1))

lemma degree_image_G (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) :
    m.degree '' G c =
      Set.range (fun i : ℕ+ ↦ Finsupp.single i 2) ∪
        Set.range (fun i : ℕ+ ↦
          Finsupp.single i 1 + Finsupp.single (next i) 1) := by
  ext a
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨i, (degree_g_even c m hm i).symm⟩
    · exact Or.inr ⟨i, (degree_normalized_g_odd c hc m hm i).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨g c (2 * (i : ℕ)), Or.inl ⟨i, rfl⟩, degree_g_even c m hm i⟩
    · exact ⟨C c⁻¹ * g c (2 * (i : ℕ) + 1), Or.inr ⟨i, rfl⟩,
        degree_normalized_g_odd c hc m hm i⟩

lemma span_leadingTerm_G_eq_J (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) :
    Ideal.span (m.leadingTerm '' G c) = J := by
  rw [m.span_leadingTerm_eq_span_monomial (G_leadingCoeff_isUnit c hc m hm)]
  have himage : (fun p : S ↦ monomial (m.degree p) 1) '' G c =
      (fun a : ℕ+ →₀ ℕ ↦ monomial a (1 : ℂ)) '' (m.degree '' G c) := by
    rw [Set.image_image]
  calc
    Ideal.span ((fun p : S ↦ monomial (m.degree p) 1) '' G c) =
        Ideal.span ((fun a : ℕ+ →₀ ℕ ↦ monomial a (1 : ℂ)) '' (m.degree '' G c)) :=
      congrArg Ideal.span himage
    _ = J := by
      rw [degree_image_G c hc m hm]
      unfold J
      congr 1
      ext p
      simp only [Set.mem_image, Set.mem_union, Set.mem_range]
      aesop

lemma initialIdeal_eq_J_of_isGroebnerBasis (c : ℂ) (hc : c ^ 2 + c = 1)
    (hG : caseIMonomialOrder.IsGroebnerBasis (G c) (I c)) :
    Ideal.span (caseIMonomialOrder.leadingTerm '' (I c : Set S)) = J := by
  rw [hG.span_leadingTerm_image]
  exact span_leadingTerm_G_eq_J c hc caseIMonomialOrder
    isCaseIMonomialOrder_caseIMonomialOrder

lemma G_isGroebnerBasis (c : ℂ) (hc : c ^ 2 + c = 1) :
    caseIMonomialOrder.IsGroebnerBasis (G c) (I c) := by
  have h := MonomialOrder.IsGroebnerBasis.isGroebnerBasis_of_hasStandardRepresentation_sPolynomial
    (G_leadingCoeff_isUnit c hc caseIMonomialOrder
      isCaseIMonomialOrder_caseIMonomialOrder)
    (all_sPolynomials_haveStandardRepresentation c hc caseIMonomialOrder
      isCaseIMonomialOrder_caseIMonomialOrder)
  rw [span_G_eq_I c hc] at h
  exact h

/-- Indices congruent to `±1` modulo five. -/
abbrev AllowedIndex :=
  {i : ℕ+ // (i : ℕ) % 5 = 1 ∨ (i : ℕ) % 5 = 4}

abbrev AllowedPolynomial := MvPolynomial AllowedIndex ℂ

abbrev IsAllowedNat (n : ℕ) : Prop := n % 5 = 1 ∨ n % 5 = 4

lemma badCoefficient_ne_zero (c : ℂ) (hc : c ^ 2 + c = 1) {n : ℕ}
    (hn : n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3) : s c n - c ≠ 0 := by
  rcases hn with hn | hn | hn
  · simpa [s, hn] using two_sub_ne_zero c hc
  · have h := one_add_two_mul_ne_zero c hc
    convert neg_ne_zero.mpr h using 1 <;> simp [s, hn] <;> ring
  · have h := one_add_two_mul_ne_zero c hc
    convert neg_ne_zero.mpr h using 1 <;> simp [s, hn] <;> ring

noncomputable def eliminatedVariable (c : ℂ) : ℕ → AllowedPolynomial :=
  Nat.strongRec fun n rec ↦
    if hn0 : n = 0 then 0
    else if ha : IsAllowedNat n then
      X ⟨⟨n, Nat.pos_of_ne_zero hn0⟩, ha⟩
    else
      -C (s c n - c)⁻¹ *
        (∑ i ∈ ((Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n)).attach,
            C (s c (n - 2 * i.val)) *
              rec i.val (by
                have hi := i.prop
                simp only [Finset.mem_filter, Finset.mem_range] at hi
                omega) *
              rec (n - i.val) (by
                have hi := i.prop
                simp only [Finset.mem_filter, Finset.mem_range] at hi
                omega) +
          if heven : 2 ∣ n then
            (rec (n / 2) (by
              have hn2 : 2 ≤ n := by
                by_contra h
                interval_cases n <;> simp [IsAllowedNat] at ha hn0
              exact Nat.div_lt_self (by omega) (by omega))) ^ 2
          else 0)

lemma eliminatedVariable_eq (c : ℂ) (n : ℕ) :
    eliminatedVariable c n =
      if hn0 : n = 0 then 0
      else if ha : IsAllowedNat n then
        X ⟨⟨n, Nat.pos_of_ne_zero hn0⟩, ha⟩
      else
        -C (s c n - c)⁻¹ *
          (∑ i ∈ ((Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n)).attach,
              C (s c (n - 2 * i.val)) * eliminatedVariable c i.val *
                eliminatedVariable c (n - i.val) +
            if heven : 2 ∣ n then (eliminatedVariable c (n / 2)) ^ 2 else 0) := by
  rw [eliminatedVariable, Nat.strongRec_eq]
  congr 1

noncomputable def eliminationHom (c : ℂ) : S →ₐ[ℂ] AllowedPolynomial :=
  MvPolynomial.aeval fun i ↦ eliminatedVariable c i.val

lemma eliminationHom_X (c : ℂ) (i : ℕ+) :
    eliminationHom c (X i) = eliminatedVariable c i.val := by
  simp [eliminationHom]

lemma eliminationHom_C (c a : ℂ) : eliminationHom c (C a) = C a := by
  simp [eliminationHom]

lemma eliminatedVariable_allowed (c : ℂ) (i : AllowedIndex) :
    eliminatedVariable c i.val.val = X i := by
  rw [eliminatedVariable_eq]
  simp only [i.val.ne_zero, i.prop, ↓reduceIte]
  apply congrArg X
  exact Subtype.ext (Subtype.ext rfl)

noncomputable def gTail (c : ℂ) (n : ℕ) : S :=
  (∑ i ∈ (Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n),
      C (s c (n - 2 * i)) * x i * x (n - i)) +
    if 2 ∣ n then x (n / 2) ^ 2 else 0

lemma g_eq_linear_add_tail (c : ℂ) (n : ℕ) :
    g c n = C (s c n - c) * x n + gTail c n := by
  simp [g, gTail, add_assoc]

lemma eliminationHom_x (c : ℂ) {n : ℕ} (hn : 0 < n) :
    eliminationHom c (x n) = eliminatedVariable c n := by
  rw [x, dif_pos hn]
  simpa using eliminationHom_X c ⟨n, hn⟩

lemma eliminationHom_gTail (c : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    eliminationHom c (gTail c n) =
      (∑ i ∈ ((Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n)).attach,
          C (s c (n - 2 * i.val)) * eliminatedVariable c i.val *
            eliminatedVariable c (n - i.val)) +
        if 2 ∣ n then (eliminatedVariable c (n / 2)) ^ 2 else 0 := by
  rw [gTail, map_add]
  congr 1
  · rw [map_sum]
    simp_rw [map_mul, eliminationHom_C]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := i.prop
    simp only [Finset.mem_filter, Finset.mem_range] at hi'
    rw [eliminationHom_x c hi'.2.1, eliminationHom_x c (by omega)]
  · split_ifs with heven
    · rw [map_pow, eliminationHom_x c]
      exact Nat.div_pos hn (by norm_num)
    · simp

lemma eliminationHom_g_of_mem_D (c : ℂ) (hc : c ^ 2 + c = 1)
    {n : ℕ} (hn : n ∈ D) : eliminationHom c (g c n) = 0 := by
  have hn2 : 2 ≤ n := hn.1
  have hbad := hn.2
  have hnotAllowed : ¬IsAllowedNat n := by
    intro ha
    rcases hbad with h | h | h <;> rcases ha with ha | ha <;> omega
  rw [g_eq_linear_add_tail, map_add, map_mul]
  rw [eliminationHom_C,
    eliminationHom_x c (by omega), eliminationHom_gTail c hn2,
    eliminatedVariable_eq, dif_neg (by omega), dif_neg hnotAllowed]
  have hcoeff := badCoefficient_ne_zero c hc hbad
  have hscalar : (s c n - c) * (-(s c n - c)⁻¹) = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hcoeff]
  rw [show -C (s c n - c)⁻¹ = C (-(s c n - c)⁻¹) by rw [map_neg],
    ← mul_assoc, ← map_mul, hscalar, map_neg, map_one]
  split_ifs <;> ring

/-- The map sending each allowed variable to its residue class modulo `I`. -/
noncomputable def allowedToQuotient (c : ℂ) :
    MvPolynomial AllowedIndex ℂ →ₐ[ℂ] S ⧸ I c :=
  MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk (I c) (X i.1)

lemma allowedToQuotient_X (c : ℂ) (i : AllowedIndex) :
    allowedToQuotient c (X i) = Ideal.Quotient.mk (I c) (X i.1) := by
  simp [allowedToQuotient]

lemma allowedToQuotient_C (c a : ℂ) :
    allowedToQuotient c (C a) = Ideal.Quotient.mk (I c) (C a) := by
  simp [allowedToQuotient]
  symm
  exact Ideal.Quotient.mk_algebraMap ℂ (I c) a

lemma quotient_mk_C (c a : ℂ) :
    Ideal.Quotient.mk (I c) (C a) = algebraMap ℂ (S ⧸ I c) a := by
  exact Ideal.Quotient.mk_algebraMap ℂ (I c) a

lemma eliminationHom_vanishes_on_I (c : ℂ) (hc : c ^ 2 + c = 1) :
    ∀ p ∈ I c, eliminationHom c p = 0 := by
  change I c ≤ RingHom.ker (eliminationHom c).toRingHom
  rw [I, Ideal.span_le]
  rintro p ⟨n, hn, rfl⟩
  exact eliminationHom_g_of_mem_D c hc hn

noncomputable def quotientToAllowed (c : ℂ) (hc : c ^ 2 + c = 1) :
    S ⧸ I c →ₐ[ℂ] AllowedPolynomial :=
  Ideal.Quotient.liftₐ (I c) (eliminationHom c) (eliminationHom_vanishes_on_I c hc)

lemma quotientToAllowed_mk (c : ℂ) (hc : c ^ 2 + c = 1) (p : S) :
    quotientToAllowed c hc (Ideal.Quotient.mk (I c) p) = eliminationHom c p := by
  rfl

lemma quotientToAllowed_comp_allowedToQuotient (c : ℂ) (hc : c ^ 2 + c = 1) :
    (quotientToAllowed c hc).comp (allowedToQuotient c) = AlgHom.id ℂ AllowedPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, allowedToQuotient_X, quotientToAllowed_mk,
    eliminationHom_X, eliminatedVariable_allowed]
  rfl

set_option maxHeartbeats 800000 in
lemma allowedToQuotient_eliminatedVariable (c : ℂ) (hc : c ^ 2 + c = 1)
    {n : ℕ} (hn : 0 < n) :
    allowedToQuotient c (eliminatedVariable c n) =
      Ideal.Quotient.mk (I c) (x n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [eliminatedVariable_eq]
    simp only [dif_neg (Nat.ne_of_gt hn)]
    by_cases ha : IsAllowedNat n
    · rw [dif_pos ha, allowedToQuotient_X]
      rw [x, dif_pos hn]
    · rw [dif_neg ha]
      have hbad : n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3 := by
        have hlt := Nat.mod_lt n (by norm_num : 0 < 5)
        omega
      have hn2 : 2 ≤ n := by
        by_contra h
        interval_cases n <;> simp [IsAllowedNat] at ha hn
      let T : AllowedPolynomial :=
        (∑ i ∈ ((Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n)).attach,
            C (s c (n - 2 * i.val)) * eliminatedVariable c i.val *
              eliminatedVariable c (n - i.val)) +
          if 2 ∣ n then (eliminatedVariable c (n / 2)) ^ 2 else 0
      change allowedToQuotient c (-C (s c n - c)⁻¹ * T) = _
      rw [map_mul, map_neg, allowedToQuotient_C]
      have htail : allowedToQuotient c T =
          Ideal.Quotient.mk (I c) (gTail c n) := by
        dsimp only [T]
        rw [gTail, map_add, map_add]
        congr 1
        · rw [map_sum, map_sum]
          simp_rw [map_mul, allowedToQuotient_C]
          trans ∑ i ∈ ((Finset.range n).filter
              (fun i ↦ 0 < i ∧ 2 * i < n)).attach,
            Ideal.Quotient.mk (I c) (C (s c (n - 2 * i.val))) *
              Ideal.Quotient.mk (I c) (x i.val) *
                Ideal.Quotient.mk (I c) (x (n - i.val))
          · apply Finset.sum_congr rfl
            intro i hi
            have hi' := i.prop
            simp only [Finset.mem_filter, Finset.mem_range] at hi'
            rw [ih i.val (by omega) hi'.2.1,
              ih (n - i.val) (by omega) (by omega)]
          · exact Finset.sum_attach
              ((Finset.range n).filter (fun i ↦ 0 < i ∧ 2 * i < n))
              (fun r ↦ Ideal.Quotient.mk (I c) (C (s c (n - 2 * r))) *
                Ideal.Quotient.mk (I c) (x r) *
                  Ideal.Quotient.mk (I c) (x (n - r)))
        · split_ifs with heven
          · rw [map_pow, ih (n / 2) (Nat.div_lt_self (by omega) (by omega))]
            · simp [map_pow]
            · exact Nat.div_pos hn2 (by norm_num)
          · simp
      rw [htail]
      have hgzero : Ideal.Quotient.mk (I c) (g c n) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact all_g_mem_I c hc n hn2
      rw [g_eq_linear_add_tail, map_add, map_mul] at hgzero
      have hcoeff := badCoefficient_ne_zero c hc hbad
      rw [quotient_mk_C] at hgzero
      rw [quotient_mk_C]
      have hneg : -(Ideal.Quotient.mk (I c) (gTail c n)) =
          algebraMap ℂ (S ⧸ I c) (s c n - c) *
            Ideal.Quotient.mk (I c) (x n) :=
        (eq_neg_of_add_eq_zero_left hgzero).symm
      calc
        -(algebraMap ℂ (S ⧸ I c) (s c n - c)⁻¹) *
              Ideal.Quotient.mk (I c) (gTail c n) =
            algebraMap ℂ (S ⧸ I c) (s c n - c)⁻¹ *
              (-(Ideal.Quotient.mk (I c) (gTail c n))) := by ring
        _ = algebraMap ℂ (S ⧸ I c) (s c n - c)⁻¹ *
              (algebraMap ℂ (S ⧸ I c) (s c n - c) *
                Ideal.Quotient.mk (I c) (x n)) := by rw [hneg]
        _ = Ideal.Quotient.mk (I c) (x n) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcoeff, map_one, one_mul]

lemma allowedToQuotient_comp_quotientToAllowed (c : ℂ) (hc : c ^ 2 + c = 1) :
    (allowedToQuotient c).comp (quotientToAllowed c hc) = AlgHom.id ℂ (S ⧸ I c) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    quotientToAllowed_mk, eliminationHom_X]
  change allowedToQuotient c (eliminatedVariable c i.val) =
    Ideal.Quotient.mk (I c) (X i)
  calc
    allowedToQuotient c (eliminatedVariable c i.val) =
        Ideal.Quotient.mk (I c) (x i.val) :=
      allowedToQuotient_eliminatedVariable c hc (n := i.val) i.prop
    _ = Ideal.Quotient.mk (I c) (X i) := by rw [x_eq_X]

lemma allowedToQuotient_bijective (c : ℂ) (hc : c ^ 2 + c = 1) :
    Function.Bijective (allowedToQuotient c) := by
  have hl : Function.LeftInverse (quotientToAllowed c hc) (allowedToQuotient c) := by
    intro p
    have h := AlgHom.congr_fun (quotientToAllowed_comp_allowedToQuotient c hc) p
    simpa using h
  have hr : Function.RightInverse (quotientToAllowed c hc) (allowedToQuotient c) := by
    intro p
    have h := AlgHom.congr_fun (allowedToQuotient_comp_quotientToAllowed c hc) p
    simpa using h
  exact ⟨hl.injective, hr.surjective⟩

lemma support_g_cases (c : ℂ) {n : ℕ} (hn : 2 ≤ n) {a : ℕ+ →₀ ℕ}
    (ha : a ∈ (g c n).support) :
    a = Finsupp.single ⟨n, Nat.zero_lt_of_lt hn⟩ 1 ∨
      (∃ j k : ℕ+, 2 * (j : ℕ) < n ∧ n = (j : ℕ) + (k : ℕ) ∧
        a = Finsupp.single j 1 + Finsupp.single k 1) ∨
      (2 ∣ n ∧ a = Finsupp.single ⟨n / 2, Nat.div_pos hn (by norm_num)⟩ 2) := by
  rw [g_eq_linear_add_tail, gTail] at ha
  have ha₁ := MvPolynomial.support_add ha
  simp only [Finset.mem_union] at ha₁
  rcases ha₁ with ha₁ | ha₁
  · left
    let np : ℕ+ := ⟨n, Nat.zero_lt_of_lt hn⟩
    have hx : x n = X np := by simpa [np] using x_eq_X np
    rw [hx, C_mul_X_eq_monomial] at ha₁
    have hamem := support_monomial_subset ha₁
    simpa [np] using hamem
  have ha₂ := MvPolynomial.support_add ha₁
  simp only [Finset.mem_union] at ha₂
  rcases ha₂ with ha₂ | ha₂
  · have ha₃ := MvPolynomial.support_sum ha₂
    simp only [Finset.mem_biUnion] at ha₃
    rcases ha₃ with ⟨j, hj, haj⟩
    have hj' := hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj'
    right; left
    let jp : ℕ+ := ⟨j, hj'.2.1⟩
    let kp : ℕ+ := ⟨n - j, by omega⟩
    refine ⟨jp, kp, hj'.2.2, by simp [jp, kp]; omega, ?_⟩
    have haj' :
        Finsupp.single jp 1 + Finsupp.single kp 1 = a ∧
          s c (n - 2 * j) ≠ 0 := by
      simpa [x, hj'.2.1, show 0 < n - j by omega, X, C_mul_monomial,
        MvPolynomial.monomial_mul_monomial, jp, kp] using haj
    exact haj'.1.symm
  · right; right
    by_cases heven : 2 ∣ n
    · rw [if_pos heven] at ha₂
      let mid : ℕ+ := ⟨n / 2, Nat.div_pos hn (by norm_num)⟩
      refine ⟨heven, ?_⟩
      change a = Finsupp.single mid 2
      have ha₂' :
          Finsupp.single mid 1 + Finsupp.single mid 1 = a := by
        simpa [x, Nat.div_pos hn (by norm_num), X, pow_two,
          MvPolynomial.monomial_mul_monomial, mid] using ha₂
      rw [← ha₂']
      rw [← Finsupp.single_add]
    · rw [if_neg heven] at ha₂
      simp at ha₂

def IsGapStandard (a : ℕ+ →₀ ℕ) : Prop :=
  ∀ i : ℕ+, a i ≤ 1 ∧ (a i ≠ 0 → a (next i) = 0)

lemma single_isGapStandard (i : ℕ+) : IsGapStandard (Finsupp.single i 1) := by
  intro t
  constructor
  · simp only [Finsupp.single_apply]
    split_ifs <;> omega
  · intro ht
    have hti : t = i := by
      by_contra h
      simp [Finsupp.single_apply, h] at ht
    subst t
    simp [Finsupp.single_apply, next_ne_self]

lemma pair_isGapStandard {j k : ℕ+} (hjk : (j : ℕ) < (k : ℕ))
    (hgap : next j ≠ k) :
    IsGapStandard (Finsupp.single j 1 + Finsupp.single k 1) := by
  intro t
  have hjk' : j ≠ k := by
    exact ne_of_lt hjk
  constructor
  · by_cases htj : t = j
    · subst t
      simp [Finsupp.single_apply, hjk']
    by_cases htk : t = k
    · subst t
      simp [Finsupp.single_apply, hjk']
    simp [Finsupp.single_apply, htj, htk]
  · intro ht
    have htjk : t = j ∨ t = k := by
      by_contra h
      push_neg at h
      simp [Finsupp.single_apply, h.1, h.2] at ht
    rcases htjk with htj | htk
    · have hnextt_ne_j : next t ≠ j := by simpa [htj] using next_ne_self j
      have hnextt_ne_k : next t ≠ k := by simpa [htj] using hgap
      simp [Finsupp.single_apply, hnextt_ne_j, hnextt_ne_k]
    · have hnextt_ne_j : next t ≠ j := by
        intro h
        have htkv := congrArg Subtype.val htk
        have hv := congrArg Subtype.val h
        change (t : ℕ) = (k : ℕ) at htkv
        change (t : ℕ) + 1 = (j : ℕ) at hv
        omega
      have hnextt_ne_k : next t ≠ k := by simpa [htk] using next_ne_self k
      simp [Finsupp.single_apply, hnextt_ne_j, hnextt_ne_k]

lemma support_g_even_eq_top_or_gap (c : ℂ) (i : ℕ+) {a : ℕ+ →₀ ℕ}
    (ha : a ∈ (g c (2 * (i : ℕ))).support) :
    a = Finsupp.single i 2 ∨ IsGapStandard a := by
  rcases support_g_cases c (n := 2 * (i : ℕ))
      (by have hi : 1 ≤ (i : ℕ) := i.prop; omega) ha with
    hlinear | ⟨j, k, hjk, hsum, rfl⟩ | ⟨heven, hsquare⟩
  · right
    rw [hlinear]
    exact single_isGapStandard _
  · right
    apply pair_isGapStandard (by omega)
    intro hnext
    have hv := congrArg Subtype.val hnext
    change (j : ℕ) + 1 = (k : ℕ) at hv
    omega
  · left
    have hhalf : (2 * (i : ℕ)) / 2 = (i : ℕ) := by omega
    have hmid : (⟨(2 * (i : ℕ)) / 2,
        Nat.div_pos (by have hi : 1 ≤ (i : ℕ) := i.prop; omega) (by norm_num)⟩ : ℕ+) = i :=
      Subtype.ext hhalf
    simpa only [hmid] using hsquare

lemma support_g_odd_eq_top_or_gap (c : ℂ) (i : ℕ+) {a : ℕ+ →₀ ℕ}
    (ha : a ∈ (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S).support) :
    a = Finsupp.single i 1 + Finsupp.single (next i) 1 ∨ IsGapStandard a := by
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at ha
  have ha' : a ∈ (g c (2 * (i : ℕ) + 1)).support := by
    rw [mem_support_iff] at ha ⊢
    simpa [hc0] using ha
  rcases support_g_cases c (n := 2 * (i : ℕ) + 1)
      (by have hi : 1 ≤ (i : ℕ) := i.prop; omega) ha' with
    hlinear | ⟨j, k, hjk, hsum, hpair⟩ | ⟨heven, hsquare⟩
  · right
    rw [hlinear]
    exact single_isGapStandard _
  · by_cases hgap : next j = k
    · left
      have hj : (j : ℕ) = (i : ℕ) := by
        have hv := congrArg Subtype.val hgap
        change (j : ℕ) + 1 = (k : ℕ) at hv
        omega
      have hj' : j = i := Subtype.ext hj
      have hk' : k = next i := by simpa [hj'] using hgap.symm
      simpa [hj', hk'] using hpair
    · right
      rw [hpair]
      exact pair_isGapStandard (by omega) hgap
  · exfalso
    rcases heven with ⟨d, hd⟩
    omega

lemma generator_degree_not_le_gap (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) {a : ℕ+ →₀ ℕ}
    (ha : IsGapStandard a) {q : S} (hq : q ∈ G c) : ¬m.degree q ≤ a := by
  rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [degree_g_even c m hm i]
    intro hle
    have h := hle i
    have hai := (ha i).1
    simp at h
    omega
  · rw [degree_normalized_g_odd c hc m hm i]
    intro hle
    have hi := hle i
    have hnext := hle (next i)
    have hi0 : a i ≠ 0 := by
      simp [Finsupp.single_apply, next_ne_self] at hi
      omega
    have hnext0 : a (next i) ≠ 0 := by
      simp [Finsupp.single_apply, next_ne_self] at hnext
      omega
    exact hnext0 ((ha i).2 hi0)

lemma generator_eq_of_degree_le_square (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) {q : S}
    (hq : q ∈ G c) (hle : m.degree q ≤ Finsupp.single i 2) :
    q = g c (2 * (i : ℕ)) := by
  rcases hq with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [degree_g_even c m hm j] at hle
    have hji : j = i := by
      by_contra hne
      have h := hle j
      simp [Finsupp.single_apply, hne] at h
    subst j
    rfl
  · rw [degree_normalized_g_odd c hc m hm j] at hle
    have hji : j = i := by
      by_contra hne
      have h := hle j
      simp [Finsupp.single_apply, next_ne_self, hne] at h
    have hnext := hle (next j)
    simp [Finsupp.single_apply, hji, next_ne_self] at hnext

lemma generator_eq_of_degree_le_adjacent (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (i : ℕ+) {q : S}
    (hq : q ∈ G c)
    (hle : m.degree q ≤ Finsupp.single i 1 + Finsupp.single (next i) 1) :
    q = (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S) := by
  rcases hq with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [degree_g_even c m hm j] at hle
    have h := hle j
    by_cases hji : j = i
    · simp [Finsupp.single_apply, hji, next_ne_self] at h
    by_cases hjnext : j = next i
    · simp [Finsupp.single_apply, hjnext, next_ne_self] at h
    simp [Finsupp.single_apply, hji, hjnext] at h
  · rw [degree_normalized_g_odd c hc m hm j] at hle
    have hjcase : j = i ∨ j = next i := by
      by_contra h
      push_neg at h
      have hj := hle j
      simp [Finsupp.single_apply, next_ne_self, h.1, h.2] at hj
    rcases hjcase with hji | hji
    · subst j
      rfl
    · have hnext := hle (next j)
      have hnextnext_ne_i : next (next i) ≠ i := by
        intro h
        have hv := congrArg Subtype.val h
        change (i : ℕ) + 2 = (i : ℕ) at hv
        omega
      have hnextnext_ne_next : next (next i) ≠ next i := next_ne_self (next i)
      simp [Finsupp.single_apply, hji, next_ne_self, hnextnext_ne_i,
        hnextnext_ne_next] at hnext

lemma G_isReduced (c : ℂ) (hc : c ^ 2 + c = 1) :
    (G_isGroebnerBasis c hc).IsReduced := by
  rw [MonomialOrder.IsGroebnerBasis.IsReduced.isReduced_def]
  constructor
  · exact G_monic c hc caseIMonomialOrder isCaseIMonomialOrder_caseIMonomialOrder
  · intro p hp a ha q hq hqp
    rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases support_g_even_eq_top_or_gap c i ha with rfl | hgap
      · intro hle
        exact hqp (generator_eq_of_degree_le_square c hc caseIMonomialOrder
          isCaseIMonomialOrder_caseIMonomialOrder i hq hle)
      · exact generator_degree_not_le_gap c hc caseIMonomialOrder
          isCaseIMonomialOrder_caseIMonomialOrder hgap hq
    · rcases support_g_odd_eq_top_or_gap c i ha with rfl | hgap
      · intro hle
        exact hqp (generator_eq_of_degree_le_adjacent c hc caseIMonomialOrder
          isCaseIMonomialOrder_caseIMonomialOrder i hq hle)
      · exact generator_degree_not_le_gap c hc caseIMonomialOrder
          isCaseIMonomialOrder_caseIMonomialOrder hgap hq

/--
Theorem 1.1.  Here the leading monomial is represented by its exponent vector
`m.degree`, and the assertion that the allowed residue classes freely generate the quotient is
represented by bijectivity of the canonical evaluation map `allowedToQuotient`.
-/
theorem theorem_1_1 (c : ℂ) (hc : c ^ 2 + c = 1) :
    ∃ hG : caseIMonomialOrder.IsGroebnerBasis (G c) (I c),
      hG.IsReduced ∧
        Ideal.span (caseIMonomialOrder.leadingTerm '' (I c : Set S)) = J ∧
        (∀ i : ℕ+, caseIMonomialOrder.degree (g c (2 * (i : ℕ))) = Finsupp.single i 2) ∧
        (∀ i : ℕ+, caseIMonomialOrder.degree (g c (2 * (i : ℕ) + 1)) =
          Finsupp.single i 1 + Finsupp.single (next i) 1) ∧
        Function.Bijective (allowedToQuotient c) := by
  refine ⟨G_isGroebnerBasis c hc, G_isReduced c hc,
    initialIdeal_eq_J_of_isGroebnerBasis c hc (G_isGroebnerBasis c hc), ?_, ?_,
    allowedToQuotient_bijective c hc⟩
  · exact degree_g_even c caseIMonomialOrder isCaseIMonomialOrder_caseIMonomialOrder
  · exact degree_g_odd c hc caseIMonomialOrder isCaseIMonomialOrder_caseIMonomialOrder

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

noncomputable instance partitionFintype (n : ℕ) : Fintype (Partition n) := by
  exact (finite_weightedDegree_fiber n).fintype

noncomputable instance pFintype (n : ℕ) : Fintype (P n) := by
  letI : Fintype (Partition n) := partitionFintype n
  letI : Finite (P n) := Finite.of_injective (fun a : P n ↦ a.val) Subtype.val_injective
  exact Fintype.ofFinite (P n)

noncomputable instance qFintype (n : ℕ) : Fintype (Q n) := by
  letI : Fintype (Partition n) := partitionFintype n
  letI : Finite (Q n) := Finite.of_injective (fun a : Q n ↦ a.val) Subtype.val_injective
  exact Fintype.ofFinite (Q n)

lemma adjacent_le_iff (a : ℕ+ →₀ ℕ) (i : ℕ+) :
    Finsupp.single i 1 + Finsupp.single (next i) 1 ≤ a ↔
      a i ≠ 0 ∧ a (next i) ≠ 0 := by
  constructor
  · intro h
    constructor
    · apply Nat.ne_of_gt
      apply lt_of_lt_of_le Nat.zero_lt_one
      exact Finsupp.single_le_iff.mp <|
        le_trans (show Finsupp.single i 1 ≤
          Finsupp.single i 1 + Finsupp.single (next i) 1 from le_add_right le_rfl) h
    · apply Nat.ne_of_gt
      apply lt_of_lt_of_le Nat.zero_lt_one
      exact Finsupp.single_le_iff.mp <|
        le_trans (show Finsupp.single (next i) 1 ≤
          Finsupp.single i 1 + Finsupp.single (next i) 1 from le_add_left le_rfl) h
  · rintro ⟨hi, hnext⟩ j
    simp only [Finsupp.add_apply]
    by_cases hji : j = i
    · subst j
      simp [next_ne_self, Nat.one_le_iff_ne_zero.mpr hi]
    by_cases hjnext : j = next i
    · subst j
      simp [hji, Nat.one_le_iff_ne_zero.mpr hnext]
    simp [hji, hjnext]

lemma monomial_mem_J_iff (a : ℕ+ →₀ ℕ) :
    monomial a (1 : ℂ) ∈ J ↔
      (∃ i : ℕ+, 2 ≤ a i) ∨
        ∃ i : ℕ+, a i ≠ 0 ∧ a (next i) ≠ 0 := by
  let generators : Set (ℕ+ →₀ ℕ) :=
    Set.range (fun i : ℕ+ ↦ Finsupp.single i 2) ∪
      Set.range (fun i : ℕ+ ↦ Finsupp.single i 1 + Finsupp.single (next i) 1)
  have hJ : J = Ideal.span ((fun e ↦ monomial e (1 : ℂ)) '' generators) := by
    unfold J generators
    congr 1
    ext p
    simp only [Set.mem_image, Set.mem_union, Set.mem_range]
    aesop
  rw [hJ, MvPolynomial.mem_ideal_span_monomial_image]
  simp only [support_monomial, one_ne_zero, if_false, Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨e, he, hea⟩
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨i, Finsupp.single_le_iff.mp hea⟩
    · exact Or.inr ⟨i, (adjacent_le_iff a i).mp hea⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Finsupp.single i 2, Or.inl ⟨i, rfl⟩, Finsupp.single_le_iff.mpr hi⟩
    · exact ⟨Finsupp.single i 1 + Finsupp.single (next i) 1,
        Or.inr ⟨i, rfl⟩, (adjacent_le_iff a i).mpr hi⟩

lemma partition_condition_iff_monomial_notMem_J {n : ℕ} (a : Partition n) :
    (∀ i : ℕ+, Partition.multiplicities a i ≤ 1 ∧
        (Partition.multiplicities a i ≠ 0 →
          Partition.multiplicities a (next i) = 0)) ↔
      monomial (Partition.multiplicities a) (1 : ℂ) ∉ J := by
  simp only [monomial_mem_J_iff, not_or, not_exists]
  constructor
  · intro h
    constructor
    · intro i
      have hi := (h i).1
      omega
    · intro i hi
      exact hi.2 ((h i).2 hi.1)
  · rintro ⟨hsquare, hadjacent⟩
    let h : ∀ i : ℕ+, Partition.multiplicities a i ≤ 1 ∧
        (Partition.multiplicities a i ≠ 0 →
          Partition.multiplicities a (next i) = 0) := by
      intro i
      constructor
      · have hi := hsquare i
        omega
      · intro hi
        by_contra hnext
        exact hadjacent i ⟨hi, hnext⟩
    exact h

/-- Partitions whose monomials are standard modulo `J`. -/
def StandardPartition (n : ℕ) :=
  {a : Partition n // monomial (Partition.multiplicities a) (1 : ℂ) ∉ J}

/-- The difference-two condition is exactly the standard-monomial condition for `J`. -/
noncomputable def qEquivStandardPartition (n : ℕ) : Q n ≃ StandardPartition n where
  toFun a := ⟨a.val, (partition_condition_iff_monomial_notMem_J a.val).mp a.prop⟩
  invFun a := ⟨a.val, (partition_condition_iff_monomial_notMem_J a.val).mpr a.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The monomial corresponding to a partition. -/
noncomputable def partitionMonomial {n : ℕ} (a : Partition n) : S :=
  monomial (Partition.multiplicities a) 1

/-- The unique normal form supplied by a reduced Gröbner basis. -/
noncomputable def normalForm {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) (p : S) : S :=
  Classical.choose <| hB.existsUnique_isRemainder (fun b hb ↦ by
    rw [hred.1 b hb]
    exact isUnit_one) p

lemma normalForm_isRemainder {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) (p : S) :
    m.IsRemainder p B (normalForm hB hred p) :=
  (Classical.choose_spec <| hB.existsUnique_isRemainder (fun b hb ↦ by
    rw [hred.1 b hb]
    exact isUnit_one) p).1

def IsStandardExponent (m : MonomialOrder ℕ+) (B : Set S) (a : ℕ+ →₀ ℕ) : Prop :=
  ∀ q ∈ B, q ≠ 0 → ¬m.degree q ≤ a

noncomputable def StandardPolynomial (m : MonomialOrder ℕ+) (B : Set S) : Submodule ℂ S :=
  MvPolynomial.restrictSupport ℂ {a | IsStandardExponent m B a}

lemma normalForm_mem_standardPolynomial {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) (p : S) :
    normalForm hB hred p ∈ StandardPolynomial m B := by
  rw [StandardPolynomial, MvPolynomial.restrictSupport, AddMonoidAlgebra.mem_supported]
  intro a ha
  exact (normalForm_isRemainder hB hred p).2 a ha

noncomputable def standardToQuotient {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) : StandardPolynomial m B →ₗ[ℂ] S ⧸ K :=
  (Ideal.Quotient.mkₐ ℂ K).toLinearMap.domRestrict (StandardPolynomial m B)

lemma normalForm_quotient_eq {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) (p : S) :
    Ideal.Quotient.mk K (normalForm hB hred p) = Ideal.Quotient.mk K p := by
  have hr := normalForm_isRemainder hB hred p
  rcases hr.1 with ⟨f, heq, hdegree⟩
  have hsum : Ideal.Quotient.mk K (Finsupp.linearCombination S (fun x : B ↦ x.1) f) = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left K _ (hB.subset x.2)
  calc
    Ideal.Quotient.mk K (normalForm hB hred p) =
        0 + Ideal.Quotient.mk K (normalForm hB hred p) := by simp
    _ = Ideal.Quotient.mk K
        (Finsupp.linearCombination S (fun x : B ↦ x.1) f + normalForm hB hred p) := by
      rw [map_add, hsum]
    _ = Ideal.Quotient.mk K p := congrArg (Ideal.Quotient.mk K) heq.symm

lemma standardToQuotient_bijective {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) :
    Function.Bijective (standardToQuotient hB) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    by_contra hpq'
    have hmem : (p.1 - q.1 : S) ∈ K := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [standardToQuotient] using congrArg (fun z ↦ z - standardToQuotient hB q) hpq
    have hmonic : ∀ b ∈ B, IsUnit (m.leadingCoeff b) := by
      intro b hb
      rw [hred.1 b hb]
      exact isUnit_one
    have hcriterion :=
      (MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_subset_and_degree_le_eq_and_degree_le
        K hmonic).mp hB
    have hsubne : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hpq'
    obtain ⟨b, hbB, hb⟩ := hcriterion.2 (p.1 - q.1) hmem hsubne
    have hdegreeMem : m.degree (p.1 - q.1) ∈ (p.1 - q.1).support :=
      (m.degree_mem_support_iff _).mpr hsubne
    have hstandard : IsStandardExponent m B (m.degree (p.1 - q.1)) := by
      have hsub := (p - q).2
      exact (AddMonoidAlgebra.mem_supported.mp hsub) hdegreeMem
    exact hstandard b hbB (hred.1 b hbB).ne_zero hb
  · intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    let r : StandardPolynomial m B :=
      ⟨normalForm hB hred p, normalForm_mem_standardPolynomial hB hred p⟩
    refine ⟨r, ?_⟩
    exact normalForm_quotient_eq hB hred p

noncomputable def standardQuotientEquiv {m : MonomialOrder ℕ+} {B : Set S} {K : Ideal S}
    (hB : m.IsGroebnerBasis B K) (hred : hB.IsReduced) :
    StandardPolynomial m B ≃ₗ[ℂ] S ⧸ K :=
  LinearEquiv.ofBijective (standardToQuotient hB) (standardToQuotient_bijective hB hred)

lemma isStandardExponent_iff_gap (c : ℂ) (hc : c ^ 2 + c = 1)
    (m : MonomialOrder ℕ+) (hm : IsCaseIMonomialOrder m) (a : ℕ+ →₀ ℕ) :
    IsStandardExponent m (G c) a ↔ IsGapStandard a := by
  constructor
  · intro h i
    constructor
    · have hq := h (g c (2 * (i : ℕ))) (Or.inl ⟨i, rfl⟩)
        (monic_g_even c m hm i).ne_zero
      rw [degree_g_even c m hm i] at hq
      have hi : ¬2 ≤ a i := by
        intro hai
        exact hq (Finsupp.single_le_iff.mpr hai)
      omega
    · intro hi
      by_contra hnext
      have hq := h (C c⁻¹ * g c (2 * (i : ℕ) + 1) : S) (Or.inr ⟨i, rfl⟩)
        (monic_normalized_g_odd c hc m hm i).ne_zero
      rw [degree_normalized_g_odd c hc m hm i] at hq
      apply hq
      intro j
      simp only [Finsupp.add_apply]
      by_cases hji : j = i
      · subst j
        simp [next_ne_self, Nat.one_le_iff_ne_zero.mpr hi]
      by_cases hjnext : j = next i
      · subst j
        simp [hji, Nat.one_le_iff_ne_zero.mpr hnext]
      simp [hji, hjnext]
  · intro ha q hq hq0
    exact generator_degree_not_le_gap c hc m hm ha hq

lemma finsupp_weight_eq_weightedDegree (a : ℕ+ →₀ ℕ) :
    Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) a = weightedDegree a := by
  simp [Finsupp.weight_apply, weightedDegree, mul_comm]

lemma g_isWeightedHomogeneous (c : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ+ ↦ (i : ℕ)) (g c n) n := by
  intro a ha
  rw [finsupp_weight_eq_weightedDegree]
  rcases support_g_cases c hn (mem_support_iff.mpr ha) with
    hlinear | ⟨j, k, hjn, hsum, hpair⟩ |
    ⟨heven, hsquare⟩
  · rw [hlinear]
    simp [weightedDegree]
  · rw [hpair]
    simp [weightedDegree, hsum]
  · rw [hsquare]
    rcases heven with ⟨d, rfl⟩
    simp [weightedDegree]
    omega

attribute [local instance] MvPolynomial.weightedGradedAlgebra

lemma I_isWeightedHomogeneous (c : ℂ) (hc : c ^ 2 + c = 1) :
    (I c).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (fun i : ℕ+ ↦ (i : ℕ))) := by
  rw [I]
  apply Ideal.homogeneous_span
  rintro p ⟨n, hn, rfl⟩
  exact ⟨n, g_isWeightedHomogeneous c hn.1⟩

lemma exists_basis_matching {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]
    (bι : Module.Basis ι ℂ V) (bκ : Module.Basis κ ℂ V) :
    ∃ e : ι ≃ κ, ∀ i, bκ.repr (bι i) (e i) ≠ 0 := by
  classical
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis bι, ← Module.finrank_eq_card_basis bκ]
  let e₀ : ι ≃ κ := Fintype.equivOfCardEq hcard
  let bκ' : Module.Basis ι ℂ V := bκ.reindex e₀.symm
  have hdet : bκ'.det bι ≠ 0 := (bκ'.isUnit_det bι).ne_zero
  rw [Module.Basis.det_apply, Matrix.det_apply] at hdet
  obtain ⟨σ, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hprod : ∏ i, bκ'.toMatrix bι (σ i) i ≠ 0 := by
    intro hzero
    apply hσ.2
    simp [hzero]
  refine ⟨σ.trans e₀, ?_⟩
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  simpa [Module.Basis.toMatrix_apply, bκ', e₀] using hi

/--
Proposition 6.1.  In every weighted degree, the support of the normal-form matrix contains a
perfect matching between `P(n)` and `Q(n)`.
-/
theorem proposition_6_1 (c : ℂ) (hc : c ^ 2 + c = 1) (m : MonomialOrder ℕ+)
    (hm : IsCaseIMonomialOrder m) (hG : m.IsGroebnerBasis (G c) (I c))
    (hred : hG.IsReduced) (n : ℕ) :
    ∃ π : P n ≃ Q n,
      ∀ lam : P n,
        (normalForm hG hred (partitionMonomial lam.val)).coeff
          (Partition.multiplicities (π lam).val) ≠ 0 := by
  sorry

end CaseI
