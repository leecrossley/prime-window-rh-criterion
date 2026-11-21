import SquareMeanRemainder
import DivisorSieveDensity

/-! The diagonal of the centered tent grows on all ordinary square samples.
    This removes a numerical side condition from the Möbius remainder test. -/

noncomputable section
open Finset Filter
open RiemannReduction.DivisorSieve

namespace RiemannReduction.DivisorBand

private theorem weight_on_box {X s p : ℝ} (hs : 0 < s) (hx : 8*s ≤ X) (hup : X ≤ 9*s)
    (hp : 4*s ≤ p) (hcap : p ≤ 5*s) : 1/2 ≤ ThetaTransfer.tent ((X/4)/p) := by
  have pp : 0 < p := by linarith
  have lo : 3/8 ≤ (X/4)/p := (le_div_iff₀ pp).mpr (by linarith)
  have hi : (X/4)/p ≤ 3/4 := (div_le_iff₀ pp).mpr (by linarith)
  rw [ThetaTransfer.tent_pieces]
  split_ifs <;> linarith

/-- The normalized diagonal exceeds every fixed threshold on every sufficiently
    late square. Only the prime number theorem for a fixed-ratio interval is used. -/
theorem square_diagonal_diverges (B : ℝ) :
    ∃ k0 : ℕ, ∀ k ≥ k0, B ≤ centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2 := by
  obtain ⟨u, supply⟩ := Filter.eventually_atTop.mp box_supply
  obtain ⟨v, logs⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (max 6 (4608*B)))
  let w := max 7 (max u v)
  refine ⟨8*w, ?_⟩
  intro k hk
  let s := k^2/8
  let x := (k : ℝ)^2
  have k2 : k ≤ k^2 := Nat.le_self_pow (by decide) k
  have sw : w ≤ s := Nat.le_div_iff_mul_le (by decide) |>.mpr (by omega)
  have s7 : 7 ≤ s := (le_max_left _ _).trans sw
  have su : u ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans sw
  have sv : v ≤ s := ((le_max_right _ _).trans (le_max_right _ _)).trans sw
  have sp : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have kp : 0 < (k : ℝ) := by exact_mod_cast (by dsimp [w] at hk; omega : 0 < k)
  have hlow : 8*s ≤ k^2 := by dsimp [s]; omega
  have htop : k^2 ≤ 9*s := by dsimp [s] at *; omega
  have low : 8*(s : ℝ) ≤ x := by dsimp only [x]; exact_mod_cast hlow
  have top : x ≤ 9*(s : ℝ) := by dsimp only [x]; exact_mod_cast htop
  have x0 : 0 < x := sq_pos_of_pos kp
  let L := packetLog s
  have largeLog : 6 ≤ Real.log (s : ℝ) ∧ 4608*B ≤ Real.log (s : ℝ) := max_le_iff.mp (logs s sv)
  have Lpos : 0 < L := by dsimp [L, packetLog]; linarith [largeLog.1]
  let P := box (4*s) (5*s)
  have count : (s : ℝ) ≤ 32*L*(P.card : ℝ) := supply s su 4 5 (by decide) (by decide) (by decide)
  have sub : P ⊆ Icc 1 ⌊x⌋₊ := by
    intro p he
    obtain ⟨band, prime⟩ := mem_filter.mp he
    obtain ⟨_, upper⟩ := mem_Ioc.mp band
    exact mem_Icc.mpr ⟨prime.one_le, Nat.le_floor (by
      have : (p : ℝ) ≤ 5*(s : ℝ) := by exact_mod_cast upper
      linarith)⟩
  let term (p : ℕ) : ℝ := ((ArithmeticFunction.vonMangoldt p-1)*ThetaTransfer.tent ((x/4)/p))^2
  have each (p : ℕ) (he : p ∈ P) : L^2/16 ≤ term p := by
    obtain ⟨band, prime⟩ := mem_filter.mp he
    obtain ⟨pL, pH⟩ := mem_Ioc.mp band
    have lp : 4*(s : ℝ) ≤ p := by exact_mod_cast pL.le
    have up : (p : ℝ) ≤ 5*(s : ℝ) := by exact_mod_cast pH
    have logsP := Real.log_le_log sp (by linarith : (s : ℝ) ≤ p)
    have half : L/2 ≤ Real.log p - 1 := by
      dsimp [L, packetLog]; linarith [largeLog.1]
    have wt := weight_on_box sp low top lp up
    have prod := mul_le_mul half wt (by norm_num : (0 : ℝ) ≤ 1/2) (by linarith : 0 ≤ Real.log p-1)
    have posprod : L/4 ≤ (Real.log p-1)*ThetaTransfer.tent ((x/4)/p) := by linarith only [prod]
    have sqp := pow_le_pow_left₀ (show 0 ≤ L/4 by positivity) posprod 2
    dsimp [term]
    rw [ArithmeticFunction.vonMangoldt_apply_prime prime]
    linarith only [sqp]
  have diag : (P.card : ℝ)*(L^2/16) ≤ centeredTentDiagonal x := by
    calc _ = ∑ _p ∈ P, L^2/16 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ P, term p := sum_le_sum each
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => sq_nonneg _)
  have Lbound : 4608 * B ≤ L := by dsimp [L, packetLog]; linarith [largeLog.2]
  have lower : (s : ℝ)*L ≤ 512*centeredTentDiagonal x := by
    nlinarith only [mul_le_mul_of_nonneg_right count Lpos.le, diag]
  apply (le_div_iff₀ x0).mpr
  by_cases b0 : 0 ≤ B
  · have a := mul_le_mul_of_nonneg_left top b0
    have b := mul_le_mul_of_nonneg_left Lbound sp.le
    linarith only [a, b, lower]
  · have nonneg : 0 ≤ centeredTentDiagonal x := sum_nonneg (fun _ _ => sq_nonneg _)
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge b0) x0.le).trans nonneg

/-- On every sufficiently late finite set of roots, the sole remaining input
    is an eight-ninths mean-square bound for the explicit unpaired sum. -/
theorem late_pair_sign_of_remainder_budget :
    ∃ k0 : ℕ, ∀ I : Finset ℕ, (∀ k ∈ I, k0 ≤ k) →
      ∑ k ∈ I, (unpairedTail k (k*k.sqrt)/k)^2 ≤ (8/9 : ℝ) *
        ∑ k ∈ I, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2 →
      ∑ k ∈ I, ((centeredTentSum ((k : ℝ)^2))^2 - centeredTentDiagonal ((k : ℝ)^2))/(k : ℝ)^2 ≤ 0 := by
  obtain ⟨v, diag⟩ := square_diagonal_diverges 4260744
  refine ⟨max (108^2) v, ?_⟩
  intro I hI HR
  apply unequal_pair_sign_of_remainder_budget I (fun k hk => (max_le_iff.mp (hI k hk)).1) HR
  have h := sum_le_sum (s := I) (f := fun _ => (4260744 : ℝ))
    (fun k hk => diag k (max_le_iff.mp (hI k hk)).2)
  simpa [mul_comm] using h

#print axioms square_diagonal_diverges
#print axioms late_pair_sign_of_remainder_budget

end RiemannReduction.DivisorBand
