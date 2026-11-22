import Mathlib

/-! The elementary summation used in the prime-to-degree part of the
    Bernoulli residue estimate. The normalization is the one in
    OddResidueBounds.ThmBcOfPsiBound. -/

noncomputable section

namespace RiemannReduction.ConductorOne

private theorem bernoulli_log_cap {N t k : ℕ} (hN : 0 < N) (ht : 2 ≤ t) (hk : k ≤ t) :
    Real.log (16 * (N : ℝ) ^ (k+1) * (k.factorial : ℝ)) ≤
      (2 * (t : ℝ) + 5) * Real.log ((t : ℝ)*N) := by
  let M := t*N
  have tm : t ≤ M := Nat.le_mul_of_pos_right t hN
  have nm : N ≤ M := Nat.le_mul_of_pos_left N (by omega)
  have m2 : 2 ≤ M := ht.trans tm
  have ff : k.factorial ≤ M^t := (Nat.factorial_le_pow k).trans <|
    (Nat.pow_le_pow_left (hk.trans tm) k).trans (Nat.pow_le_pow_right (by omega) hk)
  have nn : N^(k+1) ≤ M^(t+1) := (Nat.pow_le_pow_left nm _).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have c : 16 ≤ M^4 := Nat.pow_le_pow_left m2 4
  have total : 16 * N^(k+1) * k.factorial ≤ M^(2*t+5) := by
    calc _ ≤ M^4 * M^(t+1) * M^t := Nat.mul_le_mul (Nat.mul_le_mul c nn) ff
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have mcast : (M : ℝ) = (t : ℝ)*N := by simp [M]
  have r : 16 * (N : ℝ) ^ (k+1) * (k.factorial : ℝ) ≤ (M : ℝ)^(2*t+5) := by
    exact_mod_cast total
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  calc _ ≤ Real.log ((M : ℝ)^(2*t+5)) := Real.log_le_log (by positivity) r
    _ = _ := by rw [Real.log_pow, mcast]; push_cast; ring

/-- Sum a bound for each twist index over the full interval of twists. -/
theorem sum_bernoulli_budgets {N t : ℕ} (hN : 0 < N) (ht : 2 ≤ t)
    {degree : ℝ} (hd : 0 ≤ degree) (s : ℕ → ℝ)
    (hs : ∀ e ∈ Finset.Ico 1 t, s e ≤ degree *
      Real.log (16 * (N : ℝ) ^ (e+1+1) * ((e+1).factorial : ℝ))) :
    ∑ e ∈ Finset.Ico 1 t, s e ≤ 3 * degree * (t : ℝ)^2 * Real.log ((t : ℝ)*N) := by
  have hnt : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have lg : 0 ≤ Real.log ((t : ℝ)*N) := Real.log_nonneg (by nlinarith)
  calc _ ≤ ∑ _e ∈ Finset.Ico 1 t, degree * ((2*(t : ℝ)+5)*Real.log ((t : ℝ)*N)) := by
          apply Finset.sum_le_sum
          intro e he
          apply (hs e he).trans
          exact mul_le_mul_of_nonneg_left (bernoulli_log_cap hN ht ((Finset.mem_Ico.mp he).2)) hd
    _ = ((t-1 : ℕ) : ℝ) * (degree * ((2*(t : ℝ)+5)*Real.log ((t : ℝ)*N))) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ _ := by
          rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
          have k : ((t : ℝ)-1) * (2*t+5) ≤ 3 * (t : ℝ)^2 := by nlinarith
          nlinarith only [mul_le_mul_of_nonneg_right k (mul_nonneg hd lg)]

end RiemannReduction.ConductorOne
