import DivisorBand

/-! Elementary endpoint reduction for equations (1) and (2) of the family's
finite-height prime-power certificate. The analytic enclosure and its Arb
endpoint comparison are explicit inputs. -/
open Finset
namespace RiemannReduction.DivisorBand.FiniteFifth
noncomputable section

def cap : ℕ := 69*10^19
def squareBaseCap : ℕ := 26*10^9

/-- Positive coefficients and monotonicity of log and square root allow one
interval calculation to certify every real point of the finite interval. -/
theorem all_real_of_majorant {a b e f d : ℝ}
    (hb : 0 ≤ b) (he : 0 ≤ e) (hf : 0 ≤ f) (hd : 0 ≤ d)
    (published : ∀ x : ℝ, 1024 ≤ x → x ≤ (cap:ℝ)^2 →
      |D x| / Real.sqrt x ≤ a+b*Real.sqrt x+(Real.log x+d)*(e*Real.sqrt x+f))
    (endpoint : a+b*cap+(Real.log ((cap:ℝ)^2)+d)*(e*cap+f) < 1/5) :
    ∀ x : ℝ, 1024 ≤ x → x ≤ (cap:ℝ)^2 → |D x| < Real.sqrt x/5 := by
  intro x hx hi
  have nonneg : (0:ℝ) ≤ cap := Nat.cast_nonneg _
  have upper : Real.sqrt x ≤ cap := (Real.sqrt_le_iff).mpr ⟨nonneg,hi⟩
  have xp : 0<x := by linarith
  have ep : 0 < Real.sqrt x := Real.sqrt_pos.mpr xp
  have logs := Real.log_le_log xp hi
  have fpos := add_nonneg (mul_nonneg he (Real.sqrt_nonneg x)) hf
  have lpos := add_nonneg (Real.log_nonneg (show 1 ≤ x by linarith)) hd
  have t := mul_le_mul (add_le_add logs (le_refl d))
    (add_le_add (mul_le_mul_of_nonneg_left upper he) (le_refl f)) fpos (lpos.trans (add_le_add logs (le_refl d)))
  have v := (published x hx hi).trans (add_le_add (add_le_add (le_refl a) (mul_le_mul_of_nonneg_left upper hb)) t)
  have bound := (div_lt_iff₀ ep).mp (v.trans_lt endpoint)
  linarith

/-- Both complete integer blocks follow from precisely the real range above. -/
theorem integer_and_square_blocks
    (bound : ∀ x : ℝ, 1024 ≤ x → x ≤ (cap:ℝ)^2 → |D x| < Real.sqrt x/5) :
    (∀ N : ℕ, 1024 ≤ N → N ≤ cap → ∀ j ∈ Icc N (N^2), |D j| < Real.sqrt j/5) ∧
    (∀ K : ℕ, 32 ≤ K → K ≤ squareBaseCap → ∀ k ∈ Icc K (K^2), |D ((k:ℝ)^2)| < k/5) := by
  constructor
  · intro N low high j hj
    have interval := mem_Icc.mp hj
    apply bound
    · exact_mod_cast low.trans interval.1
    · exact_mod_cast interval.2.trans (Nat.pow_le_pow_left high 2)
  · intro K low high k hk
    have interval := mem_Icc.mp hk
    have kl := low.trans interval.1
    have kc : k ≤ cap := interval.2.trans ((Nat.pow_le_pow_left high 2).trans
      (by decide +kernel : squareBaseCap^2 ≤ cap))
    have small : 1024 ≤ k^2 := (by norm_num : 1024 ≤ (32:ℕ)^2).trans (Nat.pow_le_pow_left kl 2)
    have result := bound ((k:ℝ)^2) (by exact_mod_cast small) (by exact_mod_cast Nat.pow_le_pow_left kc 2)
    simpa only [Real.sqrt_sq (Nat.cast_nonneg k)] using result

#print axioms all_real_of_majorant
#print axioms integer_and_square_blocks
end
end RiemannReduction.DivisorBand.FiniteFifth
