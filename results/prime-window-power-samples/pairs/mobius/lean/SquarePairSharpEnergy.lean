import FineSmallDivisors
import FinePairOffsets
import SquarePairGrowth

/-! Transfer the refined small-divisor and odd-pair estimates to actual
    complete blocks. The numerical finite corollaries expose the analytic
    energy estimates as hypotheses. -/

noncomputable section
open Finset
namespace RiemannReduction.DivisorBand

theorem deficit_pair_error_explicit {k : ℕ} (late : 10^16 ≤ k) :
    |D ((k:ℝ)^2) - unpairedTail k (k*k.sqrt)| ≤ (47/24)*(k:ℝ)+1 := by
  have large : (10^16 : ℝ) ≤ k := by exact_mod_cast late
  have kp : 0 < (k:ℝ) := by linarith
  have old : 108^2 ≤ k := by omega
  have c0 : 1/3 ≤ c := by unfold c; linarith [Real.log_two_gt_d9]
  have c1 : c ≤ 7/20 := by unfold c; linarith [Real.log_two_lt_d9]
  have slope : mainSlope = c*(Real.eulerMascheroniConstant+1-c) := by
    unfold mainSlope c logMoment
    ring
  have lowSlope : 0 ≤ mainSlope := by
    rw [slope]
    exact mul_nonneg (by linarith) (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have highSlope : mainSlope ≤ 1 := by
    rw [slope]
    calc _ ≤ (7/20:ℝ)*(4/3) := mul_le_mul c1 (by linarith [Real.eulerMascheroniConstant_lt_two_thirds])
            (by linarith [Real.one_half_lt_eulerMascheroniConstant]) (by norm_num)
         _ ≤ _ := by norm_num
  have small := abs_le.mp (FineSmall.small_divisors_cost_five_sixths late)
  have pair := abs_le.mp (FinePair.paired_cost_nine_eighths old)
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  rw [← id] at small
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem deficit_pair_error_two {k : ℕ} (late : 10^16 ≤ k) :
    |D ((k:ℝ)^2) - unpairedTail k (k*k.sqrt)| ≤ 2*(k:ℝ) := by
  have large : (10^16 : ℝ) ≤ k := by exact_mod_cast late
  exact (deficit_pair_error_explicit late).trans (by linarith)

theorem square_blocks_of_remainder_plus_two {B : ℝ} (bounds : RemainderBoundBlocks B) :
    PrimeGrid.SquareBoundBlocks (B+2) := by
  intro m
  obtain ⟨K, start, good⟩ := bounds (max (10^16) m)
  refine ⟨K,(le_max_right _ _).trans start,fun k hk => ?_⟩
  have late := ((le_max_left (10^16) m).trans start).trans (mem_Icc.mp hk).1
  have err := (abs_le.mp (deficit_pair_error_two late)).1
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  linarith [good k hk]

theorem centered_pair_error_two {k : ℕ} (late : 10^16 ≤ k) :
    |centeredTentSum ((k:ℝ)^2)/k + unpairedTail k (k*k.sqrt)/k| ≤ 2 := by
  have large : (10^16 : ℝ) ≤ k := by exact_mod_cast late
  have kp : 0 < (k:ℝ) := by linarith
  have center := abs_le.mp (centered_tent_margin (x := (k:ℝ)^2) (by nlinarith))
  have pair := abs_le.mp (deficit_pair_error_explicit late)
  rw [← add_div,abs_div,abs_of_pos kp,div_le_iff₀ kp]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem root_energy_le (I : Finset ℕ) (f g : ℕ → ℝ)
    (bound : ∀ k ∈ I, |f k| ≤ |g k|+2) :
    Real.sqrt (∑ k ∈ I, (f k)^2) ≤ Real.sqrt (∑ k ∈ I, (g k)^2) + 2*Real.sqrt I.card := by
  let A := ∑ k ∈ I, (g k)^2
  have a0 : 0 ≤ A := sum_nonneg (fun k _ => sq_nonneg (g k))
  have card0 : 0 ≤ (I.card : ℝ) := Nat.cast_nonneg _
  have cross : ∑ k ∈ I, |g k| ≤ Real.sqrt A * Real.sqrt I.card := by
    simpa only [A, mul_one, sq_abs, one_pow, sum_const, nsmul_eq_mul]
      using Real.sum_mul_le_sqrt_mul_sqrt I (fun k => |g k|) (fun _ => 1)
  have major : ∑ k ∈ I, (f k)^2 ≤ A + 4 * (∑ k ∈ I, |g k|) + I.card*2^2 := by
    calc _ ≤ ∑ k ∈ I, ((g k)^2 + 4 * |g k| + 2^2) := by
          apply sum_le_sum
          intro k hk
          have h := pow_le_pow_left₀ (abs_nonneg (f k)) (bound k hk) 2
          rw [sq_abs] at h
          nlinarith only [h, sq_abs (g k)]
      _ = _ := by simp only [A, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  change _ ≤ (Real.sqrt A + 2 * Real.sqrt I.card)^2
  nlinarith only [major, cross, Real.sq_sqrt a0, Real.sq_sqrt card0]

theorem short_remainder_root_two {K : ℕ} (late : 10^16 ≤ K) :
    Real.sqrt (shortRemainderEnergy K) ≤
      Real.sqrt (shortCenteredEnergy K) + 2*Real.sqrt (squarePairBlock K).card := by
  let s := fun k : ℕ => centeredTentSum ((k:ℝ)^2)/k
  let r := fun k : ℕ => unpairedTail k (k*k.sqrt)/k
  apply root_energy_le (squarePairBlock K) r s
  intro k hk
  have diff : |s k + r k| ≤ 2 := centered_pair_error_two (late.trans (mem_Icc.mp hk).1)
  calc |r k| = |(s k+r k) + (-s k)| := by ring_nf
       _ ≤ |s k+r k| + |-s k| := abs_add_le _ _
       _ ≤ _ := by rw [abs_neg]; linarith

theorem short_root_energy_distance_two {K : ℕ} (late : 10^16 ≤ K) :
    |Real.sqrt (shortCenteredEnergy K) - Real.sqrt (shortRemainderEnergy K)| ≤
      2*Real.sqrt (squarePairBlock K).card := by
  let s := fun k : ℕ => centeredTentSum ((k:ℝ)^2)/k
  let r := fun k : ℕ => unpairedTail k (k*k.sqrt)/k
  have up : Real.sqrt (shortCenteredEnergy K) ≤
      Real.sqrt (shortRemainderEnergy K) + 2*Real.sqrt (squarePairBlock K).card := by
    apply root_energy_le (squarePairBlock K) s r
    intro k hk
    have diff : |s k + r k| ≤ 2 := centered_pair_error_two (late.trans (mem_Icc.mp hk).1)
    calc |s k| = |(s k+r k) + (-r k)| := by ring_nf
         _ ≤ |s k+r k| + |-r k| := abs_add_le _ _
         _ ≤ _ := by rw [abs_neg]; linarith
  have lo := short_remainder_root_two late
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem remainder_energy_of_two_unit_error {K : ℕ} (late : 10^16 ≤ K)
    {u v B : ℝ} (upos : 0 ≤ u) (bpos : 0 ≤ B)
    (energy : shortCenteredEnergy K ≤ u^2 * (squarePairBlock K).card)
    (diagonal : v * (squarePairBlock K).card ≤ shortDiagonal K)
    (comparison : (u+2)^2 ≤ B*v) :
    shortRemainderEnergy K ≤ B*shortDiagonal K := by
  let n : ℝ := (squarePairBlock K).card
  have n0 : 0 ≤ n := Nat.cast_nonneg _
  have upper : Real.sqrt (shortCenteredEnergy K) ≤ u*Real.sqrt n := by
    apply Real.sqrt_le_iff.mpr ⟨mul_nonneg upos (Real.sqrt_nonneg _), ?_⟩
    rwa [mul_pow, Real.sq_sqrt n0]
  have bound : Real.sqrt (shortRemainderEnergy K) ≤ (u+2)*Real.sqrt n := by
    rw [add_mul]
    exact (short_remainder_root_two late).trans (by linarith)
  have r0 : 0 ≤ shortRemainderEnergy K := sum_nonneg (fun k _ => sq_nonneg _)
  have sqr := pow_le_pow_left₀ (Real.sqrt_nonneg _) bound 2
  rw [Real.sq_sqrt r0, mul_pow, Real.sq_sqrt n0] at sqr
  have transfer := sqr.trans (mul_le_mul_of_nonneg_right comparison n0)
  simpa only [mul_assoc] using transfer.trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left diagonal bpos)

theorem remainder_energy_eleven_sixths {K : ℕ} (late : 10^16 ≤ K)
    (energy : shortCenteredEnergy K ≤ (2083/100) * (squarePairBlock K).card)
    (diagonal : (23914/1000) * (squarePairBlock K).card ≤ shortDiagonal K) :
    shortRemainderEnergy K ≤ (11/6)*shortDiagonal K := by
  apply remainder_energy_of_two_unit_error (u := 23/5) late (by norm_num) (by norm_num) _ diagonal (by norm_num)
  exact energy.trans (mul_le_mul_of_nonneg_right (by norm_num : (2083/100 : ℝ) ≤ (23/5)^2) (Nat.cast_nonneg _))

theorem remainder_energy_five_hundred_twenty_four {K : ℕ} (late : 10^16 ≤ K)
    (energy : shortCenteredEnergy K ≤ (457/4)^2 * (squarePairBlock K).card)
    (diagonal : (129/5) * (squarePairBlock K).card ≤ shortDiagonal K) :
    shortRemainderEnergy K ≤ 524*shortDiagonal K :=
  remainder_energy_of_two_unit_error (u := 457/4) late (by norm_num) (by norm_num) energy diagonal (by norm_num)

#print axioms centered_pair_error_two
#print axioms square_blocks_of_remainder_plus_two
#print axioms remainder_energy_five_hundred_twenty_four
end RiemannReduction.DivisorBand
