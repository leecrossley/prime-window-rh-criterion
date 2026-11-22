import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts

/-! Removing odd-order characters from the positive-part count at conductor one. -/

noncomputable section
open Formalism.HC UpperTheory.V UpperTheory.V.HV

namespace RiemannReduction.ConductorOne

variable {h : UpperTheory.V.HV.Host} {O : Type} [CommRing O] [IsDomain O]
variable {ψ : DirichletCharacter O h.N}

theorem host_character_order (one : h.chi = PChar.one) (hψ : h.IsChar ψ) :
    orderOf ψ ∣ 2 ^ (h.ex + 1) := by
  have ho : h.o = 1 := by
    change ordC h.chi = 1
    rw [one]
    exact orderOf_one
  simpa only [ho, mul_one] using (hostComp h O ψ hψ).1

theorem host_odd_order_trivial (one : h.chi = PChar.one) (hψ : h.IsChar ψ)
    (odd : Odd (orderOf ψ)) : ψ = 1 := by
  apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
  exact Nat.dvd_one.mp (by simpa [UpperTheory.V.HV.Host.q, one, PChar.one]
    using ((hostOdd h O ψ hψ).1 odd).2.2.2.2)

theorem host_odd_prime_parts (one : h.chi = PChar.one) (hψ : h.IsChar ψ)
    {l : ℕ} (hl : l.Prime) (hodd : l ≠ 2) : kap l ψ = 1 ∧ th0 l ψ = ψ := by
  have hn : ¬ l ∣ orderOf ψ := fun hd =>
    hodd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
      (hl.dvd_of_dvd_pow (hd.trans (host_character_order one hψ))))
  exact (partOrd _ l hl ψ (hostComp h O ψ hψ).2.1).2.2.2.2.2.1 hn

theorem case_three_empty (one : h.chi = PChar.one) (hψ : h.IsChar ψ) (l e : ℕ) :
    ¬ h.CaseIII l e ψ := fun hc => hc.2.2.2 (host_odd_order_trivial one hψ hc.2.2.1)

theorem case_four_is_trivial (one : h.chi = PChar.one) (hψ : h.IsChar ψ)
    {l e : ℕ} (hl : l.Prime) (hodd : l ≠ 2) (hq : l ≠ h.q1) (hd : l ≠ h.d)
    (hc : h.CaseIV l e ψ) : ψ = 1 := by
  apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
  exact Nat.dvd_one.mp (by simpa [UpperTheory.V.HV.Host.q, one, PChar.one]
    using ((hostOdd h O ψ hψ).2 l hl hodd hq hd hc.2.2).1)

end RiemannReduction.ConductorOne
