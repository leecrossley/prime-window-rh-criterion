import MobiusBlocks

/-! Transfer the normalized square-sample mean square from the dyadic tent
    with coefficients Λ−1 to the explicit remainder of the Möbius pairing. -/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt

namespace RiemannReduction.DivisorBand

/-- The centered prime sum used by the published unequal-pair test.
    The tent has support on [x/4,x]. -/
def centeredTentSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (vonMangoldt n - 1) * ThetaTransfer.tent ((x/4)/n)

private def latticeRamp (x : ℝ) : ℝ := x * (harmonic ⌊x⌋₊ : ℝ) - ⌊x⌋₊

private theorem sum_unit_ramp {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, max (y/n-1) 0) = latticeRamp y := by
  have ypos : 0 ≤ y := zero_le_one.trans hy
  have trunc : (∑ n ∈ Icc 1 ⌊x⌋₊, max (y/n-1) 0) =
      ∑ n ∈ Icc 1 ⌊y⌋₊, max (y/n-1) 0 := by
    symm
    apply sum_subset (Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy))
    intro n hn hn'
    have hn1 := (mem_Icc.mp hn).1
    have hgt : ⌊y⌋₊ < n := by
      by_contra! H
      exact hn' (mem_Icc.mpr ⟨hn1, H⟩)
    have hny : y < (n : ℝ) := (Nat.floor_lt' (by omega)).mp hgt
    exact max_eq_right (sub_nonpos.mpr ((div_le_one (Nat.cast_pos.mpr hn1)).mpr hny.le))
  rw [trunc]
  have plain : (∑ n ∈ Icc 1 ⌊y⌋₊, max (y/n-1) 0) =
      ∑ n ∈ Icc 1 ⌊y⌋₊, (y*(n : ℝ)⁻¹-1) := by
    apply sum_congr rfl
    intro n hn
    have npos : 0 < (n : ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
    have le : (n : ℝ) ≤ y := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le ypos)
    rw [max_eq_left (sub_nonneg.mpr ((one_le_div npos).mpr le)), div_eq_mul_inv]
  rw [plain, sum_sub_distrib, ← Finset.mul_sum]
  simp [latticeRamp, harmonic_eq_sum_Icc]

private def rampMain (x : ℝ) : ℝ := x*Real.log x+(Real.eulerMascheroniConstant-1)*x

private lemma scaled_harmonic_error {x : ℝ} (hx : 1 ≤ x) :
    |x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant)| ≤ 2 := by
  let n := ⌊x⌋₊
  have n1 : 1 ≤ n := Nat.le_floor (by simpa using hx)
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr n1
  have one : (1:ℝ) ≤ n := by exact_mod_cast n1
  have le : (n:ℝ) ≤ x := Nat.floor_le (by linarith)
  have lt : x < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have lo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have up := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq] at lo
  rw [Real.eulerMascheroniSeq',if_neg (by omega : n ≠ 0)] at up
  have loglo := Real.log_le_log np le
  have loghi := Real.log_le_log (by linarith : 0<x) lt.le
  have gap : Real.log ((n:ℝ)+1)-Real.log n ≤ 1/n := by
    rw [← Real.log_div (by positivity) np.ne']
    apply (Real.log_le_sub_one_of_pos (by positivity)).trans
    field_simp; linarith
  have err : |(harmonic n:ℝ)-Real.log x-Real.eulerMascheroniConstant| ≤ 1/n :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ x)]
  exact (mul_le_mul_of_nonneg_left err (by linarith)).trans (by
    rw [← mul_div_assoc,mul_one]
    exact (div_le_iff₀ np).mpr (by linarith))

private theorem lattice_ramp_error {x : ℝ} (hx : 1 ≤ x) : |latticeRamp x-rampMain x| ≤ 3 := by
  have h := abs_le.mp (scaled_harmonic_error hx)
  have lo := Nat.floor_le (zero_le_one.trans hx)
  have hi := Nat.lt_floor_add_one x
  unfold latticeRamp rampMain
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem lattice_tent {x : ℝ} (hx : 4 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, ThetaTransfer.tent ((x/4)/n)) =
      latticeRamp x - 3*latticeRamp (x/2) + 2*latticeRamp (x/4) := by
  rw [← sum_unit_ramp (by linarith : 1 ≤ x) (le_refl x),
    ← sum_unit_ramp (by linarith : 1 ≤ x/2) (by linarith : x/2 ≤ x),
    ← sum_unit_ramp (by linarith : 1 ≤ x/4) (by linarith : x/4 ≤ x)]
  simp only [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  unfold ThetaTransfer.tent
  rw [show 4*((x/4)/(n : ℝ)) = x/n by ring, show 2*((x/4)/(n : ℝ)) = (x/2)/n by ring]

/-- Uniform comparison of discrete and continuous centering. The sharper
    constant 2 in the public analytic argument is unnecessary here. -/
theorem centered_tent_margin {x : ℝ} (hx : 4 ≤ x) :
    |centeredTentSum x + D x| ≤ 18 := by
  have primeSum := band_dilate x
  have eq : centeredTentSum x =
      ThetaTransfer.primePowerSum (x/4) - ∑ n ∈ Icc 1 ⌊x⌋₊, ThetaTransfer.tent ((x/4)/n) := by
    rw [← primeSum]
    unfold centeredTentSum dilate
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    unfold window
    rw [show (x/n)/4=(x/4)/n by ring]
    ring
  have center : rampMain x - 3*rampMain (x/2) + 2*rampMain (x/4) = c*x := by
    have x0 : x ≠ 0 := by linarith
    have l4 : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    simp only [rampMain, Real.log_div x0 (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div x0 (by norm_num : (4 : ℝ) ≠ 0), l4, c]
    ring
  rw [eq, lattice_tent hx, D, ← center]
  obtain ⟨x1, x2⟩ := abs_le.mp (lattice_ramp_error (by linarith : 1 ≤ x))
  obtain ⟨y1, y2⟩ := abs_le.mp (lattice_ramp_error (by linarith : 1 ≤ x/2))
  obtain ⟨z1, z2⟩ := abs_le.mp (lattice_ramp_error (by linarith : 1 ≤ x/4))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Removing the explicit paired part changes the normalized discrepancy by at
    most 118. The centered prime sum and the Möbius remainder have opposite signs. -/
theorem centered_plus_unpaired {k : ℕ} (hk : 108^2 ≤ k) :
    |centeredTentSum ((k : ℝ)^2)/k + unpairedTail k (k*k.sqrt)/k| ≤ 118 := by
  have high : (11664 : ℝ) ≤ k := by exact_mod_cast hk
  have kp : 0 < (k : ℝ) := by linarith
  have center := abs_le.mp (centered_tent_margin (x := (k : ℝ)^2) (by nlinarith))
  obtain ⟨low, up⟩ := remainder_margin_comparison hk
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  rw [← id] at low up
  rw [← add_div, abs_div, abs_of_pos kp, div_le_iff₀ kp]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A finite block estimate with a tunable relative loss and an absolute
    additive cost per sample. This applies to the actual centered prime sum. -/
theorem centered_square_budget (I : Finset ℕ) (hi : ∀ k ∈ I, 108^2 ≤ k)
    {a : ℝ} (ha : 0 < a) :
    ∑ k ∈ I, (centeredTentSum ((k : ℝ)^2)/k)^2 ≤
      (1+a) * (∑ k ∈ I, (unpairedTail k (k*k.sqrt)/k)^2) + (I.card : ℝ)*(1+1/a)*118^2 := by
  calc _ ≤ ∑ k ∈ I, ((1+a)*(unpairedTail k (k*k.sqrt)/k)^2+(1+1/a)*118^2) := by
        apply sum_le_sum
        intro k hk
        let s := centeredTentSum ((k : ℝ)^2)/k
        let r := unpairedTail k (k*k.sqrt)/k
        have h : |s+r| ≤ 118 := centered_plus_unpaired (hi k hk)
        have hsq : (s+r)^2 ≤ 118^2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
        have key : s^2 ≤ (1+a)*r^2+(1+1/a)*(s+r)^2 := by
          have pos := sq_nonneg (a*r+(s+r))
          field_simp [ha.ne']
          nlinarith
        apply key.trans
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 1+1/a))
    _ = _ := by rw [sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring

/-- The weighted diagonal at one prime-power scale. -/
def centeredTentDiagonal (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((vonMangoldt n-1)*ThetaTransfer.tent ((x/4)/n))^2

/-- An eight-ninths budget for the unpaired Möbius terms suffices for
    nonpositivity of the public block statistic once its diagonal is large enough. -/
theorem unequal_pair_sign_of_remainder_budget (I : Finset ℕ) (hi : ∀ k ∈ I, 108^2 ≤ k)
    (hr : ∑ k ∈ I, (unpairedTail k (k*k.sqrt)/k)^2 ≤ (8/9 : ℝ) *
      ∑ k ∈ I, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2)
    (hd : 4260744 * (I.card : ℝ) ≤
      ∑ k ∈ I, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2) :
    ∑ k ∈ I, ((centeredTentSum ((k : ℝ)^2))^2-centeredTentDiagonal ((k : ℝ)^2))/(k : ℝ)^2 ≤ 0 := by
  have bound := centered_square_budget I hi (a := 1/16) (by norm_num)
  simp_rw [sub_div, ← div_pow, Finset.sum_sub_distrib]
  linarith

#print axioms unequal_pair_sign_of_remainder_budget
#print axioms centered_tent_margin
#print axioms centered_plus_unpaired
#print axioms centered_square_budget

end RiemannReduction.DivisorBand
