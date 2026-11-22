import MizusawaUnitResidue
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-! Frobenius orbits of the exponents used by the real cyclotomic units. -/
namespace RiemannReduction.UnitSigns
open UnitResidue

private theorem lift_exponent {p m : ℕ} {t : ℤ} (hp : Odd p)
    (old : ∃ a : ℕ, (m : ℤ) ∣ (p : ℤ)^a - t)
    (step : ∃ e k : ℕ, p^e = 1 + m*(2*k+1)) :
    ∃ a : ℕ, (2 * (m : ℤ)) ∣ (p : ℤ)^a - t := by
  obtain ⟨a,s,hs⟩ := old
  obtain ⟨e,k,hk⟩ := step
  by_cases even : 2 ∣ s
  · obtain ⟨v,hv⟩ := even
    exact ⟨a,v,by rw [hs,hv]; ring⟩
  · have powerOdd : Odd ((p : ℤ)^a) := by exact_mod_cast hp.pow
    have adjust : Odd ((p : ℤ)^a * (2*(k : ℤ)+1)) :=
      powerOdd.mul ⟨k,rfl⟩
    obtain ⟨r,hr⟩ := adjust
    obtain ⟨v,hv⟩ : 2 ∣ s + (p : ℤ)^a * (2*(k:ℤ)+1) := by omega
    have hi : (p : ℤ)^e = 1 + (m : ℤ)*(2*(k:ℤ)+1) := by exact_mod_cast hk
    refine ⟨a+e,v,?_⟩
    rw [pow_add,hi]
    linear_combination hs + (m : ℤ)*hv

/-- At every dyadic level, cubing is a Frobenius power above q. -/
theorem cube_orbit {q : ℕ} (hq : q % 8 = 3) (j : ℕ) :
    ∃ a : ℕ, (2^(j+4) : ℤ) ∣ (q : ℤ)^a - 3 := by
  have odd : Odd q := ⟨q/2, by omega⟩
  have initial : ∃ a : ℕ, (8 : ℤ) ∣ (q : ℤ)^a - 3 := by
    exact ⟨1,q/8,by simp only [pow_one]; omega⟩
  have hq2 : ExactTwoPart 3 (q^2) := by
    obtain ⟨k,hk⟩ : ∃ k, q = 8*k+3 := ⟨q/8,by omega⟩
    exact ⟨4*k^2+3*k,by rw [hk]; ring⟩
  induction j with
  | zero =>
    obtain ⟨k,hk⟩ := hq2
    exact lift_exponent odd initial ⟨2,k,hk⟩
  | succ j ih =>
    obtain ⟨k,hk⟩ := (two_parts hq (by decide : 7 % 16 = 7) j).1
    simpa only [Nat.succ_add, pow_succ, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using
      (lift_exponent (m := 2^(j+4)) odd (by exact_mod_cast ih) ⟨2^(j+2),k,hk⟩)

/-- Above d, inverse ninth power is a Frobenius power. -/
theorem ninth_orbit {d : ℕ} (hd : d % 16 = 7) (j : ℕ) :
    ∃ a : ℕ, (2^(j+4) : ℤ) ∣ (d : ℤ)^a - (-9) := by
  have odd : Odd d := ⟨d/2, by omega⟩
  induction j with
  | zero =>
    refine ⟨1,(d/16:ℕ)+1,?_⟩
    simp only [pow_one]
    omega
  | succ j ih =>
    obtain ⟨k,hk⟩ := (two_parts (by decide : 3 % 8 = 3) hd j).2
    simpa only [Nat.succ_add, pow_succ, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using
      (lift_exponent (m := 2^(j+4)) odd (by exact_mod_cast ih) ⟨2^(j+1),k,hk⟩)

end RiemannReduction.UnitSigns
