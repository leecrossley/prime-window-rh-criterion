import AtCharacter
import PrincipalHostCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe

/-! A direct bound for the dyadic conductor used in the surviving symplectic case. -/

open NumberField Formalism.HC UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV
namespace RiemannReduction.SymplecticTwo

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in #[`two_pow_clog_le,`final_le] do
    RiemannReduction.CharacterRestriction.nameHelper
      `Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe n
      (`RiemannReduction.SymplecticTwo ++ n)

private theorem two_part_le_two {m : ℕ} (h : ¬ 4 ∣ m) :
    2 ^ m.factorization 2 ≤ 2 := by
  have exponent : m.factorization 2 ≤ 1 := by
    by_contra! bigger
    exact h ((show 4 ∣ 2 ^ m.factorization 2 from pow_dvd_pow 2 bigger).trans (Nat.ordProj_dvd m 2))
  simpa using Nat.pow_le_pow_right (by decide : 0 < 2) exponent

/-- Of two even integers two apart, at most one contributes a factor four. -/
private theorem dyadic_part_square_sub_one {l : ℕ} (hl : 2 ≤ l) :
    2 ^ (l ^ 2 - 1).factorization 2 ≤ 2*(l+1) := by
  have positive : l-1 ≠ 0 := by omega
  have eqn : l ^ 2 - 1 = (l-1)*(l+1) := by
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hl
    subst l
    rw [show 2+b-1 = b+1 by omega]
    exact Nat.sub_eq_of_eq_add (by ring)
  rw [eqn, Nat.factorization_mul positive (by omega), Finsupp.add_apply, pow_add]
  by_cases four : 4 ∣ l-1
  · have other : ¬ 4 ∣ l+1 := by omega
    calc _ ≤ (l-1)*2 := Nat.mul_le_mul (Nat.ordProj_le 2 positive) (two_part_le_two other)
         _ ≤ 2*(l+1) := by omega
  · exact Nat.mul_le_mul (two_part_le_two four) (Nat.ordProj_le 2 (by omega))

theorem principal_dyadic_part {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {O : Type} [CommRing O] [IsDomain O] {ψ : DirichletCharacter O h.N} (hψ : h.IsChar ψ)
    {l : ℕ} (pl : l.Prime) (odd : l ≠ 2) : 2 ^ n0 l ψ ≤ 2*(l+1) := by
  have ho : h.o = 1 := by change ordC h.chi = 1; rw [one]; exact orderOf_one
  have ht := (hostTh1 h O ψ hψ l pl odd).2.2.1
  rw [ho, mul_one] at ht
  have modulus : Nat.lcm 4 (orderOf (th1 l ψ)) = 4 :=
    Nat.lcm_eq_left (ht.trans (by decide : 2 ∣ 4))
  have two := pl.two_le
  have parity := pl.odd_of_ne_two odd
  have residues : l % 4 = 1 ∨ l % 4 = 3 := by
    obtain ⟨t, ht⟩ := parity
    omega
  have square : (l : ZMod 4)^2 = 1 := by
    rw [← ZMod.natCast_mod l 4]
    rcases residues with r | r <;> rw [r] <;> decide
  have divides : f0 l ψ ∣ 2 := by
    unfold f0
    rw [modulus]
    exact orderOf_dvd_of_pow_eq_one square
  rcases (Nat.dvd_prime Nat.prime_two).mp divides with f | f
  · unfold n0
    rw [f, pow_one]
    exact (Nat.ordProj_le 2 (by omega : l-1 ≠ 0)).trans (by omega)
  · simpa only [n0,f] using dyadic_part_square_sub_one two

/-- N is the host's integer modulus. No third-case auxiliary conductor appears. -/
theorem principal_two_conductor {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {O : Type} [CommRing O] [IsDomain O] {ψ : DirichletCharacter O h.N} (hψ : h.IsChar ψ)
    {l : ℕ} (pl : l.Prime) (odd : l ≠ 2) :
    2 ^ h.nII l ψ ≤ 128 * h.N * l^3 := by
  have ho : h.o = 1 := by change ordC h.chi = 1; rw [one]; exact orderOf_one
  have hq : h.q = 1 := by change h.chi.N = 1; rw [one]; rfl
  have hN := h.N_pos
  have lpos := pl.pos
  have hc : 2 ^ c2 ψ ≤ h.N := Nat.le_of_dvd hN (compCond O h.N ψ 2 Nat.prime_two).2.2.2.2.1
  have htwo : 2 ^ n0 l ψ ≤ 4*l := (principal_dyadic_part one hψ pl odd).trans (by omega)
  have hfour : 4 ^ n0 l ψ ≤ (4*l)^2 := by
    calc 4 ^ n0 l ψ = (2 ^ n0 l ψ)^2 := by
           change (2^2)^_ = _
           rw [← pow_mul, ← pow_mul, Nat.mul_comm 2]
         _ ≤ _ := Nat.pow_le_pow_left htwo 2
  have ha : l*h.N*4^n0 l ψ ≤ 64*h.N*l^3 := by
    calc _ ≤ l*h.N*(4*l)^2 := Nat.mul_le_mul_left _ hfour
         _ = 16*h.N*l^3 := by ring
         _ ≤ 64*h.N*l^3 := by gcongr; omega
  have hb : 2^(c2 ψ+6)*h.o*l^3*h.q^2 ≤ 64*h.N*l^3 := by
    rw [ho,hq,pow_add]
    norm_num
    calc _ ≤ h.N * 64 * l^3 := by gcongr
         _ = _ := by ring
  have positive : 1 ≤ max (l*h.N*4^n0 l ψ) (2^(c2 ψ+6)*h.o*l^3*h.q^2) :=
    (show 0 < l*h.N*4^n0 l ψ by positivity).trans_le (le_max_left _ _)
  exact (two_pow_clog_le _ positive).trans ((Nat.mul_le_mul_left 2 (max_le ha hb)).trans_eq (by ring))

theorem principal_two_exponent {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {O : Type} [CommRing O] [IsDomain O] {ψ : DirichletCharacter O h.N} (hψ : h.IsChar ψ)
    {l e : ℕ} (pl : l.Prime) (odd : l ≠ 2) (he : 0 < e) :
    2 ^ h.nII l ψ ≤ (l*h.N*e)^3 := by
  have hn : 16 ≤ h.N := Nat.le_of_dvd h.N_pos (hostIndex h).2.2.1
  have buffer : 128 ≤ h.N^2 := (by decide : 128 ≤ 16^2).trans (Nat.pow_le_pow_left hn 2)
  calc 2 ^ h.nII l ψ ≤ 128*h.N*l^3 := principal_two_conductor one hψ pl odd
       _ ≤ h.N^2*h.N*l^3 := by gcongr
       _ = (l*h.N)^3 := by ring
       _ ≤ _ := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ he) 3

/-- Explicit exponent paying for the even-order symplectic datum at conductor one. -/
theorem principal_level_budget (C A : ℕ) (h : UpperTheory.V.HV.Host) (one : h.chi = PChar.one)
    (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) (odd : l ≠ 2) (he : 0 < e)
    (ψ : DirichletCharacter c.O h.N) (hψ : h.IsChar ψ) :
    (2 * C * ((l-1)*2^h.nII l ψ*(2*h.o) : ℕ) *
      (((l*2^h.nII l ψ*h.N*1 : ℕ) : ℝ) * (e+1))^A * Real.log (pZero (l*h.N*1)) : ℝ)
      ≤ ((l:ℝ)*h.N*e)^(2*C+8*A+22) := by
  have ho : h.o = 1 := by change ordC h.chi = 1; rw [one]; exact orderOf_one
  have estimate := final_le C A 3 1 h.o l (h.nII l ψ) h.N 1 e
    (Fact.out : l.Prime).two_le h.N_pos he (le_refl _) (principal_two_exponent one hψ Fact.out odd he)
  convert estimate using 1
  rw [ho]
  ring

end RiemannReduction.SymplecticTwo
