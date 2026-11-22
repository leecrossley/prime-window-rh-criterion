import AtCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DataEx

/-! The second case of Alpöge's symplectic datum, with the unused third-case inputs removed. -/
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in #[`core,`even_of_odd,`pow_cond] do
    RiemannReduction.CharacterRestriction.nameHelper `Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DataEx n (`RiemannReduction.SymplecticTwo ++ n)

namespace RiemannReduction.SymplecticTwo

/-- The even-order case uses a single dyadic root-of-unity extension.
The auxiliary character of odd conductor has modulus and order one. -/
theorem data_of_case_two :
    X.CorX → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      (h : Host) (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → ∀ ψ ∈ h.X c e, h.CaseII l e ψ →
      HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) →
      ∃ D : Raw Ω c, D.Good ∧ Aut.OfChar D e ψ (h.nII l ψ) 1 1 := by
  intro hX Ω _ _ _ h l hl c e hl2 ψ hmem hc r2
  obtain ⟨hψ, hev⟩ := h.mem_X.1 hmem
  have hlp : l.Prime := hl.out
  have hq : 0 < h.q := NeZero.pos _
  obtain ⟨tψ, ⟨s, hs⟩, -, -, -, f3, -⟩ := X.th1Facts c.O h.N ψ l hlp hl2
  obtain ⟨-, t2, t3, -⟩ := hostTh1 h c.O ψ hψ l hlp hl2
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨b1, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  have hn : c2 ψ + 6 ≤ h.nII l ψ := (Nat.pow_le_pow_iff_right one_lt_two).1 (le_trans (by
    rw [mul_assoc, mul_assoc]
    exact Nat.le_mul_of_pos_right _ (by have := hlp.pos; positivity)) b2)
  obtain ⟨ξ, hξ, hξo⟩ := UpperTheory.exists_primitive_odd_dirichletCharacter_two_pow c.O _ (by omega) r2
  refine (core (Ω := Ω) hX h e hl2 hc.1 ψ hψ hev (fun h1 => by simpa [EV, h1] using hc.2.1) odd_one
    (1 : DirichletCharacter c.O 1) ξ hξ hξo (a := c2 ψ + 1 + h.o.factorization 2) (u := ordCompl[2] h.o * l ^ s)
    (fun v hv hd => ?_) (one_pow _) (even_of_odd (pow_one _) odd_one) (by omega) ?_ ?_ ?_ (one_pow _) fun v hv => ?_).imp
    fun D hD => ⟨hD.1, by simpa only [orderOf_one] using hD.2⟩
  · rw [Nat.dvd_one.1 hd] at hv
    rcases Finset.mem_insert.1 hv with h1 | h1
    · exact hlp.ne_one h1.symm
    · exact ((hostSb h c.O ψ hψ l hlp hl2).1 1 h1).1.ne_one rfl
  · rw [one_mul]
    exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.le_of_dvd h.N_pos (th1 l ψ).conductor_dvd_level))) b1
  · exact (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hlp.odd_of_ne_two hl2).pow
  · have e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s := by
      conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]
      ring
    have p1 := pow_cond (psi2 ψ) (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
    have p2 := orderOf_dvd_iff_pow_eq_one.1 t3
    rw [e1]
    generalize c2 ψ = k at p1 ⊢
    have p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1 := by
      rw [mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul,
        ← mul_assoc, mul_comm, pow_mul, hs, one_pow]
    rwa [← tψ] at p3
  · have v1 : v ≤ l * h.q := Nat.le_of_dvd (Nat.mul_pos hlp.pos hq) ((hostSb h c.O ψ hψ l hlp hl2).2.2.2.2 v hv)
    have v2 : 2 ^ h.o.factorization 2 ≤ h.o := Nat.ordProj_le 2 ho.ne'
    refine le_trans ?_ b2
    calc v ^ 2 * 2 ^ (c2 ψ + 1 + h.o.factorization 2) = v ^ 2 * 2 ^ h.o.factorization 2 * 2 ^ (c2 ψ + 1) * 1 := by ring
      _ ≤ (l * h.q) ^ 2 * h.o * 2 ^ (c2 ψ + 6) * l := by
        gcongr
        · norm_num
        · omega
        · exact hlp.one_le
      _ = _ := by ring

end RiemannReduction.SymplecticTwo
