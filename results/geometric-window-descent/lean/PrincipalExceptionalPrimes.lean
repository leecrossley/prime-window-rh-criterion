import PrincipalHostCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! The exceptional odd primes in the conductor-one Selmer count. -/

noncomputable section
open NumberField Formalism.HC UpperTheory.V UpperTheory.V.HV

namespace RiemannReduction.ConductorOne

theorem first_auxiliary_prime : pK PChar.one = 7 := by
  let S := {p : ℕ | p.Prime ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime PChar.one.N}
  have a : 7 ∈ S := by norm_num [S, PChar.one]
  exact le_antisymm (Nat.sInf_le a) (Nat.sInf_mem (Set.nonempty_of_mem a)).2.2.1

theorem class_number_seven : classNumber (Kstar 7) = 1 := by
  obtain ⟨hd, himag, hquad, _⟩ := kstar 7 (by norm_num) (by norm_num)
  rw [classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  have h1 : InfinitePlace.nrComplexPlaces (Kstar 7) = 1 := by
    have := IsTotallyComplex.finrank (K := Kstar 7)
    omega
  rw [hd, h1, hquad]
  have hpi := Real.pi_gt_three
  norm_num [Nat.factorial]
  nlinarith

theorem second_auxiliary_prime : pOne PChar.one = 3 := by
  unfold pOne
  rw [first_auxiliary_prime]
  change sInf {p : ℕ | p.Prime ∧ p ≡ 1 [MOD ordCompl[2] (orderOf (1 : DirichletCharacter ℂ 1))] ∧ p.Coprime (2 * 1 * 7)} = 3
  simp only [orderOf_one, Nat.factorization_one, Finsupp.zero_apply, pow_zero, Nat.div_one, mul_one]
  let S := {p : ℕ | p.Prime ∧ p ≡ 1 [MOD 1] ∧ p.Coprime (2 * 7)}
  have a : 3 ∈ S := by decide
  refine le_antisymm (Nat.sInf_le a) ?_
  obtain ⟨hp, _, hcop⟩ := Nat.sInf_mem (Set.nonempty_of_mem a)
  change 3 ≤ sInf S
  have hl := hp.two_le
  have hn : sInf S ≠ 2 := by
    intro he
    rw [he] at hcop
    exact (by decide : ¬ Nat.Coprime 2 (2 * 7)) hcop
  omega

theorem exceptional_primes : Bchi PChar.one = {3, 7} := by
  have hstar : hStar PChar.one = 1 := by
    exact (congrArg (fun n : ℕ => classNumber (Kstar n)) first_auxiliary_prime).trans class_number_seven
  have ho : ordC PChar.one = 1 := orderOf_one
  rw [Bchi, hstar, first_auxiliary_prime, second_auxiliary_prime, ho]
  change insert 3 (((7 * 3 : ℕ).primeFactors).erase 2) = {3, 7}
  rw [Nat.primeFactors_mul (by decide) (by decide),
    Nat.Prime.primeFactors (by decide : Nat.Prime 7), Nat.Prime.primeFactors Nat.prime_three]
  decide

theorem case_five_support {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one) (l e : ℕ) :
    h.CaseV l e ↔ (l = 3 ∨ l = 7) ∧ e = 1 := by
  simp [UpperTheory.V.HV.Host.CaseV, one, exceptional_primes]

/-- The generic counting case persists at every sufficiently large prime in every positive twist. -/
theorem generic_case_above {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one) {l e : ℕ}
    (he : 0 < e) (hl : 7 < l) (hsize : 2*e + 1 < l) : h.CaseI l e := by
  refine ⟨?_, fun hdiv => ?_⟩
  · rw [one, exceptional_primes]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have := Nat.le_of_dvd (by omega : 0 < 2*e) hdiv
    omega

end RiemannReduction.ConductorOne
