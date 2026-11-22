import RealUnitFrobenius

/-! Quadratic characters of the real unit, evaluated directly in residue fields. -/
noncomputable section
namespace RiemannReduction.UnitSigns
open UnitResidue

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def realUnit (z : F) : F := 1 + z + z⁻¹

omit [Fintype F] [DecidableEq F] in
private theorem geometric_ratio (z : F) (nz : z ≠ 0) :
    realUnit z * z * (1-z) = 1-z^3 := by
  unfold realUnit
  field_simp
  ring

omit [Fintype F] [DecidableEq F] in
private theorem two_ratios (z : F) (nz : z ≠ 0) :
    realUnit z * realUnit (z^3) * z^4 * (1-z) = 1-z^9 := by
  calc
    _ = realUnit (z^3) * z^3 * (realUnit z * z * (1-z)) := by ring
    _ = _ := by rw [geometric_ratio z nz,geometric_ratio (z^3) (pow_ne_zero _ nz),← pow_mul]

private theorem sign_frobenius {p : ℕ} [Fact p.Prime] [CharP F p] (odd : Odd p)
    (a : ℕ) (z : F) :
    quadraticChar F (1-z^(p^a)) = quadraticChar F (1-z) := by
  have hf := map_sub (iterateFrobenius F p a) 1 z
  rw [map_one,iterateFrobenius_def,iterateFrobenius_def] at hf
  rw [← hf,map_pow]
  by_cases zero : 1-z = 0
  · simp [zero, zero_pow (pow_pos (Fact.out : p.Prime).pos a).ne']
  obtain plus | minus := quadraticChar_dichotomy zero
  · simp [plus]
  · rw [minus, (odd.pow (n := a)).neg_one_pow]

omit [Fintype F] [DecidableEq F] in
private theorem orbit_power {p j : ℕ} {z : F} (root : IsPrimitiveRoot z (2^(j+4)))
    (nz : z ≠ 0) {a : ℕ} {t : ℤ} (h : (2^(j+4) : ℤ) ∣ (p:ℤ)^a-t) :
    z^(p^a) = z^t := by
  let u := Units.mk0 z nz
  have hu : IsPrimitiveRoot u (2^(j+4)) := IsPrimitiveRoot.coe_units_iff.mp root
  have hp : u^((p:ℤ)^a-t) = 1 := (hu.zpow_eq_one_iff_dvd _).mpr (by exact_mod_cast h)
  rw [zpow_sub, mul_inv_eq_one] at hp
  have eq : u^(p^a) = u^t := by
    rw [← zpow_natCast, Nat.cast_pow]; exact hp
  simpa only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, u] using congrArg Units.val eq

private theorem reverse_sign (z : F) (nz : z ≠ 0)
    (minus : quadraticChar F (-1) = 1) (ns : quadraticChar F z = -1) :
    quadraticChar F (1-z⁻¹) = -quadraticChar F (1-z) := by
  have eq : (-1 : F)*(1-z) = z*(1-z⁻¹) := by field_simp; ring
  have h := congrArg (quadraticChar F) eq
  simp only [map_mul,minus,ns] at h
  omega

/-- At q the real unit is a nonsquare for every primitive root of full dyadic order. -/
theorem at_q {q j : ℕ} [Fact q.Prime] [CharP F q] (hq : q % 8 = 3) {z : F}
    (root : IsPrimitiveRoot z (2^(j+4))) (ns : quadraticChar F z = -1) :
    quadraticChar F (realUnit z) = -1 := by
  have nz := root.ne_zero (by positivity)
  have ne := sub_ne_zero.mpr (root.ne_one (one_lt_pow₀ (by decide) (by omega))).symm
  obtain ⟨a,ha⟩ := cube_orbit hq j
  have h := sign_frobenius (F := F) (p := q) (show Odd q from ⟨q/2,by omega⟩) a z
  have pow3 := orbit_power root nz ha
  norm_num at pow3
  rw [pow3] at h
  have ratio := congrArg (quadraticChar F) (geometric_ratio z nz)
  simp only [map_mul,ns,h] at ratio
  rcases quadraticChar_dichotomy ne with pos | neg
  · rw [pos] at ratio; omega
  · rw [neg] at ratio; omega

/-- At d exactly one of the real unit and its cubic Galois conjugate is a square. -/
theorem at_d {d j : ℕ} [Fact d.Prime] [CharP F d] (hd : d % 16 = 7) {z : F}
    (root : IsPrimitiveRoot z (2^(j+4))) (ns : quadraticChar F z = -1)
    (minus : quadraticChar F (-1) = 1) :
    quadraticChar F (realUnit z) * quadraticChar F (realUnit (z^3)) = -1 := by
  have nz := root.ne_zero (by positivity)
  have ne := sub_ne_zero.mpr (root.ne_one (one_lt_pow₀ (by decide) (by omega))).symm
  obtain ⟨a,ha⟩ := ninth_orbit hd j
  have h := sign_frobenius (F := F) (p := d) (show Odd d from ⟨d/2,by omega⟩) a z
  have pow9 := orbit_power root nz ha
  rw [zpow_neg] at pow9
  norm_num at pow9
  rw [pow9, reverse_sign _ (pow_ne_zero _ nz) minus (by rw [map_pow,ns]; norm_num)] at h
  have ratio := congrArg (quadraticChar F) (two_ratios z nz)
  simp only [map_mul,map_pow,ns] at ratio
  rcases quadraticChar_dichotomy ne with pos | neg
  · rw [pos] at h ratio
    norm_num at ratio h ⊢
    omega
  · rw [neg] at h ratio
    norm_num at ratio h ⊢
    omega

end RiemannReduction.UnitSigns
