import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic

/-! Small integral ideals in a prime cyclotomic field, and the classical
class-number-one calculation in the seventh cyclotomic field. -/
noncomputable section
open NumberField Ideal Polynomial Nat Module Finset
open IsCyclotomicExtension InfinitePlace Real
open scoped nonZeroDivisors
namespace RiemannReduction.CyclotomicLayer

theorem top_of_small_norm {p : ℕ} [prime : Fact p.Prime] (odd : p ≠ 2)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (I : (Ideal (𝓞 K))⁰) (small : absNorm (I : Ideal (𝓞 K)) < p) : (I : Ideal (𝓞 K)) = ⊤ := by
  have : NeZero p := ⟨prime.out.ne_zero⟩
  let Q := 𝓞 K ⧸ (I : Ideal (𝓞 K))
  have size : Nat.card Q = absNorm (I : Ideal (𝓞 K)) := by
    rw [absNorm_apply, Submodule.cardQuot_apply]
  have : Finite Q := Nat.finite_of_card_ne_zero (size ▸ (absNorm_ne_zero_of_nonZeroDivisors I))
  let root := zeta_spec p ℚ K
  let x : Q := Ideal.Quotient.mk (I : Ideal (𝓞 K)) root.toInteger
  have hp : x^p=1 := by
    simp only [x, ← map_pow, root.toInteger_isPrimitiveRoot.pow_eq_one, map_one]
  have order := (Nat.dvd_prime prime.out).mp (orderOf_dvd_of_pow_eq_one hp)
  have ltP : orderOf x < p := orderOf_le_card.trans_lt (size ▸ small)
  have one : x = 1 := orderOf_eq_one_iff.mp (order.resolve_right ltP.ne)
  have zmem : root.toInteger - 1 ∈ (I : Ideal (𝓞 K)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, show Ideal.Quotient.mk (I : Ideal (𝓞 K)) root.toInteger = 1 from one, sub_self]
  have dvd := absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr zmem)
  rw [absNorm_span_singleton,root.norm_toInteger_sub_one_of_prime_ne_two' odd, Int.natAbs_natCast] at dvd
  exact absNorm_eq_one_iff.mp (((Nat.dvd_prime prime.out).mp dvd).resolve_right small.ne)

theorem class_number_seventh (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] :
    classNumber K = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le
  intro I bound
  suffices small : absNorm (I : Ideal (𝓞 K)) < 7 by
    rw [top_of_small_norm (p:=7) (by decide) K I small]
    infer_instance
  have hdeg : Module.finrank ℚ K = 6 := by
    rw [IsCyclotomicExtension.finrank (n:=7) K (cyclotomic.irreducible_rat (by decide)), Nat.totient_prime (by decide : Nat.Prime 7)]
  have hcomplex : nrComplexPlaces K = 3 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 7, Nat.totient_prime (by decide : Nat.Prime 7)]
  rw [hdeg,hcomplex,IsCyclotomicExtension.Rat.discr_prime 7 K] at bound
  norm_num [Nat.factorial] at bound
  have hp : 4 / π ≤ (4/3:ℝ) := by gcongr; exact Real.pi_gt_three.le
  have hs : Real.sqrt 16807 ≤ 130 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have upper : (4 / π) ^ 3 * (720 / (6 ^ 6 : ℝ) * Real.sqrt 16807) < 7 := by
    apply lt_of_le_of_lt (b:= (4/3:ℝ)^3*(720/(6^6:ℝ)*130))
    · gcongr
    · norm_num
  norm_num at upper
  have result : ((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℝ) < 7 := bound.trans_lt upper
  exact_mod_cast result
#print axioms top_of_small_norm
#print axioms class_number_seventh
end RiemannReduction.CyclotomicLayer
