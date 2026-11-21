import DyadicArithmetic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds

open Filter Finset
open scoped ArithmeticFunction.vonMangoldt

namespace RiemannReduction

/-- Elementary Chebyshev bounds, with room to spare for the logarithmic remainders. -/
private lemma theta_bounds_eventually :
    ∀ᶠ t : ℝ in atTop, (9/10)*t ≤ Chebyshev.theta t ∧ Chebyshev.theta t ≤ (9/8)*t := by
  obtain ⟨C, gap⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have logs := Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1/500)
  have logs2 := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ) < 1)).bound
    (by norm_num : (0:ℝ) < 1/100)
  filter_upwards [logs, logs2, eventually_ge_atTop (30:ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (100*C)] with t hlog hlog2 ht hbig
  have pos : 0 ≤ t := by linarith
  have logpos := Real.log_nonneg (show 1 ≤ t by linarith)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg pos, abs_of_nonneg logpos] at hlog
  simp only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg pos,
    abs_of_nonneg (sq_nonneg (Real.log t))] at hlog2
  have sqrtErr := mul_le_mul_of_nonneg_right hbig (Real.sqrt_nonneg t)
  have sq := Real.mul_self_sqrt pos
  have lower := PI.PC.psiLowerBound_holds t ht
  have upper := PI.PC.psiUpperBound_holds t (by linarith)
  constructor
  · nlinarith [gap t]
  · linarith [Chebyshev.theta_le_psi t]

private lemma square_weight {t : ℝ} (ht : 0 < t) {p : ℕ}
    (lo : (5/8)*t < (p:ℝ)) (hi : (p:ℝ) ≤ (7/8)*t) :
    1/4 ≤ ThetaTransfer.tent ((t^2/4)/(↑(p^2 : ℕ):ℝ)) := by
  have pos : 0 < (p:ℝ) := by linarith
  have lo2 := mul_self_le_mul_self (by positivity : 0 ≤ (5/8)*t) lo.le
  have hi2 := mul_self_le_mul_self pos.le hi
  push_cast
  have zlo : 5/16 ≤ (t^2/4)/(p:ℝ)^2 :=
    (le_div_iff₀ (sq_pos_of_pos pos)).mpr (by nlinarith [sq_nonneg t])
  have zhi : (t^2/4)/(p:ℝ)^2 ≤ 3/4 :=
    (div_le_iff₀ (sq_pos_of_pos pos)).mpr (by nlinarith [sq_nonneg t])
  rw [ThetaTransfer.tent_pieces]
  split_ifs <;> linarith

private lemma squares_in_band {t : ℝ} (ht : 0 < t) :
    (1/4)*(Chebyshev.theta ((7/8)*t) - Chebyshev.theta ((5/8)*t)) ≤
      ThetaTransfer.primePowerSum (t^2/4) - ThetaTransfer.primeSum (t^2/4) := by
  let S := Nat.primesLE ⌊(7/8)*t⌋₊ \ Nat.primesLE ⌊(5/8)*t⌋₊
  have bounds {p : ℕ} (hp : p ∈ S) :
      p.Prime ∧ (5/8)*t < (p:ℝ) ∧ (p:ℝ) ≤ (7/8)*t := by
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨ph,pr⟩ := Nat.mem_primesLE.mp h1
    refine ⟨pr, ?_, (Nat.le_floor_iff (by positivity)).mp ph⟩
    exact lt_of_not_ge fun h => h2 (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by positivity)).mpr h,pr⟩)
  have dif : Chebyshev.theta ((7/8)*t) - Chebyshev.theta ((5/8)*t) = ∑ p ∈ S, Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    exact (Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_le_floor (by linarith)))).symm
  let T := Finset.range (⌊t^2⌋₊ + 1)
  let f (n : ℕ) := Λ n * ThetaTransfer.tent ((t^2/4)/n)
  have incl : S.image (fun p : ℕ => p^2) ⊆ T.filter (fun n => ¬n.Prime) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨pr, _, h⟩ := bounds hp
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range_succ_iff.mpr
      apply (Nat.le_floor_iff (sq_nonneg t)).mpr
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
    · exact Nat.Prime.not_prime_pow le_rfl
  have square : (∑ p ∈ S, f (p^2)) ≤ ∑ n ∈ T.filter (fun n => ¬n.Prime), f n := by
    rw [← Finset.sum_image (f := fun n => f n) (g := fun p : ℕ => p^2)
      (by intro a _ b _ h; exact Nat.pow_left_injective (by decide : 2 ≠ 0) h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg incl fun n _ _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (ThetaTransfer.tent_nonneg _)
  have ordinary : ThetaTransfer.primeSum (t^2/4) = ∑ n ∈ T.filter Nat.Prime, f n := by
    rw [ThetaTransfer.primeSum, show 4*(t^2/4) = t^2 by ring]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [f, ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  rw [ordinary, ThetaTransfer.primePowerSum, show 4*(t^2/4) = t^2 by ring, dif, Finset.mul_sum]
  change _ ≤ (∑ n ∈ T, f n) - ∑ n ∈ T.filter Nat.Prime, f n
  rw [← Finset.sum_filter_add_sum_filter_not T Nat.Prime f, add_sub_cancel_left]
  apply le_trans (Finset.sum_le_sum ?_) square
  intro p hp
  obtain ⟨pr, lo, hi⟩ := bounds hp
  simpa [f, ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime pr, mul_comm] using
    mul_le_mul_of_nonneg_right (square_weight ht lo hi) (Real.log_natCast_nonneg p)

/-- The omitted squares alone give a uniform, unconditional square-root advantage. -/
theorem square_gap_eventually :
    ∀ᶠ t : ℝ in atTop, t/64 ≤
      ThetaTransfer.primePowerSum (t^2/4) - ThetaTransfer.primeSum (t^2/4) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp theta_bounds_eventually
  filter_upwards [eventually_ge_atTop (max 1 (2*T))] with t ht
  have h1 := (le_max_left _ _).trans ht
  have h2 := (le_max_right _ _).trans ht
  have low := (hT ((7/8)*t) (by linarith)).1
  have high := (hT ((5/8)*t) (by linarith)).2
  linarith [squares_in_band (by linarith : 0 < t)]

#print axioms square_gap_eventually
end RiemannReduction

namespace RiemannReduction

/-- Logarithmic mass of the primes in the first quotient interval used for Möbius pairing. -/
theorem first_bin_theta_bounds :
    ∀ᶠ x : ℝ in atTop, 3*x/80 ≤ Chebyshev.theta (2*x/3)-Chebyshev.theta (x/2) ∧
      Chebyshev.theta (2*x/3)-Chebyshev.theta (x/2) ≤ 3*x/10 := by
  obtain ⟨T,est⟩ := eventually_atTop.mp theta_bounds_eventually
  filter_upwards [eventually_ge_atTop (max 0 (2*T))] with x hx
  have x0 := (le_max_left _ _).trans hx
  have xT := (le_max_right _ _).trans hx
  obtain ⟨a,b⟩ := est (2*x/3) (by linarith)
  obtain ⟨c,d⟩ := est (x/2) (by linarith)
  constructor <;> linarith

end RiemannReduction
