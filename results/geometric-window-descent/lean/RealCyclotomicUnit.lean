import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! The product of the real cyclotomic unit 1 + ζ + ζ⁻¹ over the odd
exponents modulo inversion, uniformly at every dyadic level from eight on. -/
namespace RiemannReduction.CyclotomicUnits
open Finset
variable {R : Type*} [CommRing R]

def realUnitFactor (z : Rˣ) : R := 1 + (z : R) + (z⁻¹ : Rˣ)

def realOrbitProduct (z : Rˣ) (m : ℕ) : R :=
  ∏ j ∈ range m, realUnitFactor (z^(2*j+1))

private theorem conjugate_pair (t : Rˣ) :
    realUnitFactor t * realUnitFactor (-(t⁻¹)) = -realUnitFactor (t^2) := by
  have inv : ((t : R) * (↑t⁻¹ : R)) = 1 := Units.mul_inv t
  simp only [realUnitFactor,Units.val_neg,inv_neg,inv_inv,Units.val_pow_eq_pow_val,← inv_pow]
  linear_combination (-(2:R)) * inv

theorem orbit_step (z : Rˣ) (m : ℕ) (half : z^(4*m) = -1) :
    realOrbitProduct z (2*m) = (-1:R)^m * realOrbitProduct (z^2) m := by
  let f : ℕ → R := fun j => realUnitFactor (z^(2*j+1))
  change (∏ j ∈ range (2*m), f j) = _
  rw [two_mul,prod_range_add,← prod_range_reflect (fun j => f (m+j)) m,← prod_mul_distrib]
  calc
    ∏ j ∈ range m, f j * f (m+(m-1-j)) =
        ∏ j ∈ range m, (-1:R) * realUnitFactor ((z^2)^(2*j+1)) := by
      apply prod_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      have e : 2*(m+(m-1-j))+1 + (2*j+1) = 4*m := by omega
      have h : z^(2*(m+(m-1-j))+1) * z^(2*j+1) = -1 := by rw [← pow_add,e,half]
      have reflect : z^(2*(m+(m-1-j))+1) = -(z^(2*j+1))⁻¹ := by
        calc
          _ = (z^(2*(m+(m-1-j))+1) * z^(2*j+1)) * (z^(2*j+1))⁻¹ := by group
          _ = _ := by rw [h,neg_one_mul]
      simp only [f,reflect,conjugate_pair,neg_one_mul]
      rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ = _ := by rw [prod_mul_distrib]; simp [realOrbitProduct]

theorem orbit_product_eq_neg_one (z : Rˣ) (h : ℕ) (half : z^(4*2^h) = -1) :
    realOrbitProduct z (2^(h+1)) = -1 := by
  induction h generalizing z with
  | zero =>
    have hz : z^4 = -1 := by simpa using half
    have sq : z^2 * z^2 = -1 := by rw [← pow_add]; exact hz
    have inv : (z^2)⁻¹ = -(z^2) := by
      calc
        _ = (z^2)⁻¹ * (-(z^2 * z^2)) := by rw [sq,neg_neg,mul_one]
        _ = _ := by rw [mul_neg,inv_mul_cancel_left]
    rw [show 2^(0+1) = 2*1 by decide,orbit_step z 1 (by simpa using hz)]
    simp [realOrbitProduct,realUnitFactor,inv]
  | succ h ih =>
    have ht : (z^2)^(4*2^h) = -1 := by
      rw [← pow_mul,show 2*(4*2^h) = 4*2^(h+1) by rw [pow_succ]; ring]
      exact half
    have even : Even (2^(h+1)) := by rw [pow_succ]; exact even_iff_two_dvd.mpr (dvd_mul_left _ _)
    have next : 2^(h+1+1) = 2 * 2^(h+1) := by rw [pow_succ, Nat.mul_comm]
    rw [next,orbit_step z _ half,even.neg_one_pow,one_mul,ih (z^2) ht]

/-- The hypothesis now refers only to the actual primitive dyadic root. -/
theorem primitive_real_orbit_product [IsDomain R] (z : Rˣ) (h : ℕ)
    (primitive : IsPrimitiveRoot (z : R) (2^(h+3))) :
    realOrbitProduct z (2^(h+1)) = -1 := by
  apply orbit_product_eq_neg_one
  apply Units.ext
  rw [Units.val_pow_eq_pow_val,Units.coe_neg_one]
  apply IsPrimitiveRoot.eq_neg_one_of_two_right
  apply primitive.pow (by positivity)
  rw [show 2^(h+3) = 2^h * 2^3 by rw [pow_add]]
  ring

theorem real_cyclotomic_factor_isUnit [IsDomain R] (z : Rˣ) (h : ℕ)
    (primitive : IsPrimitiveRoot (z : R) (2^(h+3))) : IsUnit (realUnitFactor z) := by
  have allFactors : IsUnit (realOrbitProduct z (2^(h+1))) := by
    rw [primitive_real_orbit_product z h primitive]
    exact isUnit_neg_one
  have factor := (IsUnit.prod_iff.mp allFactors) 0 (mem_range.mpr (by positivity))
  simpa using factor

#print axioms primitive_real_orbit_product
#print axioms real_cyclotomic_factor_isUnit
end RiemannReduction.CyclotomicUnits
