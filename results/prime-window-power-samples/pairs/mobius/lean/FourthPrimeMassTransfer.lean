import SquarePairSharpEnergy
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Compare the positive ordinary-prime deficit at fourth powers with the
    signed paired remainder on exactly the same block and normalization as
    Sanftenberg's fixed-band logarithmic criterion. -/

open Finset
namespace RiemannReduction.DivisorBand.FourthMass
noncomputable section

def ordinary (n : ℕ) : ℝ := c*(n:ℝ)^4 - ThetaTransfer.primeSum ((n:ℝ)^4/4)
def remainder (n : ℕ) : ℝ := unpairedTail (n^2) (n^2*(n^2).sqrt)
def mass (v : ℕ → ℝ) (m : ℕ) : ℝ := ∑ n ∈ Icc m (m^2), max (v n) 0 / (n:ℝ)^3
def cofinalLogBound (v : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, mass v m ≤ C*(1+2*Real.log m)

/-- Equality with the three positive ramps used in the fixed-band prime weight. -/
theorem tent_at_prime (x p : ℝ) :
    ThetaTransfer.tent (x/4/p) =
      max (x/p-1) 0-3*max ((x/2)/p-1) 0+2*max ((x/4)/p-1) 0 := by
  unfold ThetaTransfer.tent
  rw [show 4*(x/4/p)=x/p by ring,show 2*(x/4/p)=(x/2)/p by ring]

/-- The local ordinary statistic equals the external finite expression, including
    its prime filter and the fourth-power sample. -/
theorem ordinary_eq_fixed_band (n : ℕ) :
    ordinary n = (n:ℝ)^4*Real.log 2/2 -
      ∑ p ∈ (Ioc 0 ⌊(n:ℝ)^4⌋₊).filter Nat.Prime, Real.log p *
        (max ((n:ℝ)^4/p-1) 0-3*max (((n:ℝ)^4/2)/p-1) 0+2*max (((n:ℝ)^4/4)/p-1) 0) := by
  let x : ℝ := (n:ℝ)^4
  have eq : (range (⌊x⌋₊+1)).filter Nat.Prime = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [mem_filter,mem_range,mem_Ioc]
    constructor
    · rintro ⟨hp,prime⟩
      exact ⟨⟨prime.pos,by omega⟩,prime⟩
    · rintro ⟨⟨_,hp⟩,prime⟩
      exact ⟨by omega,prime⟩
  unfold ordinary ThetaTransfer.primeSum
  change c*x- (∑ p ∈ (range (⌊4*(x/4)⌋₊+1)).filter Nat.Prime,
    Real.log p*ThetaTransfer.tent (x/4/p)) = _
  rw [show 4*(x/4)=x by ring,eq]
  simp only [tent_at_prime]
  change c*x-_ = x*Real.log 2/2-_
  unfold c
  ring

private theorem prime_power_cost {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ ThetaTransfer.primePowerSum (x/4)-ThetaTransfer.primeSum (x/4) ∧
    ThetaTransfer.primePowerSum (x/4)-ThetaTransfer.primeSum (x/4) ≤ 17*Real.sqrt x := by
  refine ⟨sub_nonneg.mpr (ThetaTransfer.primeSum_le_primePowerSum _),?_⟩
  have gap := ThetaTransfer.primePowerGap_le (x/4)
  rw [show 4*(x/4)=x by ring] at gap
  have cp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have pos : 0 < x := by linarith
  have major (j : ℕ) (hj : 2 ≤ j) :
      Chebyshev.psi (x ^ (1/(j:ℝ))) ≤ (Real.log 4+4)*Real.sqrt x := by
    grw [Chebyshev.psi_le_const_mul_self (by positivity),Real.sqrt_eq_rpow]
    gcongr
    norm_cast
  have lg : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  have cost : 3*(Real.log 4+4) ≤ 17 := by linarith [Real.log_two_lt_d9]
  have total := mul_le_mul_of_nonneg_right cost (Real.sqrt_nonneg x)
  linarith [major 2 (by decide),major 3 (by decide),major 5 (by decide)]

theorem ordinary_remainder_error {n : ℕ} (late : 10^8 ≤ n) :
    |ordinary n - remainder n| ≤ 19*(n:ℝ)^2 := by
  have r : (10^8:ℝ) ≤ n := by exact_mod_cast late
  have h : 10^16 ≤ n^2 := calc
    10^16 = (10^8)^2 := by norm_num
    _ ≤ n^2 := Nat.pow_le_pow_left late _
  have dyad := deficit_pair_error_two h
  have cast : (((n^2:ℕ):ℝ))^2 = (n:ℝ)^4 := by push_cast; ring
  rw [cast, Nat.cast_pow] at dyad
  have high : (1:ℝ) ≤ (n:ℝ)^4 := one_le_pow₀ (by linarith)
  have g := prime_power_cost high
  have sqr : Real.sqrt ((n:ℝ)^4) = (n:ℝ)^2 := by
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [sqr] at g
  unfold ordinary remainder
  unfold D at dyad
  exact abs_le.mpr ⟨by linarith [(abs_le.mp dyad).1,g.1,sq_nonneg (n:ℝ)],
                      by linarith [(abs_le.mp dyad).2,g.2]⟩

private theorem reciprocals (m : ℕ) (mp : 1 ≤ m) :
    ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ ≤ 1+2*Real.log m := by
  have ext := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc mp (le_refl (m^2)))
    (f := fun n : ℕ => (n:ℝ)⁻¹) (fun i _ _ => by positivity)
  have h := harmonic_le_one_add_log (m^2)
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
             Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at h
  exact ext.trans h

/-- The accumulated positive parts differ by at most 19 times the logarithmic budget. -/
theorem fourth_mass_error {m : ℕ} (late : 10^8 ≤ m) :
    |mass ordinary m-mass remainder m| ≤ 19*(1+2*Real.log m) := by
  unfold mass
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    ∑ n ∈ Icc m (m^2), |max (ordinary n) 0/(n:ℝ)^3-max (remainder n) 0/(n:ℝ)^3| ≤
        ∑ n ∈ Icc m (m^2), 19*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have large := late.trans (mem_Icc.mp hn).1
      have pos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      rw [←sub_div,abs_div,abs_of_pos (pow_pos pos _)]
      apply (div_le_iff₀ (pow_pos pos 3)).mpr
      calc
        _ ≤ |ordinary n-remainder n| := abs_max_sub_max_le_abs _ _ _
        _ ≤ 19*(n:ℝ)^2 := ordinary_remainder_error large
        _ = 19*(n:ℝ)⁻¹*(n:ℝ)^3 := by field_simp
    _ = 19 * ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocals m (by omega)) (by norm_num)

theorem cofinal_mass_iff : cofinalLogBound ordinary ↔ cofinalLogBound remainder := by
  constructor <;> rintro ⟨C,nonnegative,h⟩ <;> refine ⟨C+19,by linarith,?_⟩ <;> intro A
  all_goals
    obtain ⟨m,large,budget⟩ := h (max (10^8) A)
    refine ⟨m,(le_max_right _ _).trans large,?_⟩
    have discrepancy := abs_le.mp (fourth_mass_error ((le_max_left _ _).trans large))
    rw [add_mul]
    linarith

end
end RiemannReduction.DivisorBand.FourthMass
