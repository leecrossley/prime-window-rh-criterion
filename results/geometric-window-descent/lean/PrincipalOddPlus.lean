import SevenLayerVanishing
import PrincipalExceptionalPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith

/-! Polynomial control of the odd-prime plus cohomology for the principal host.
The positive mass of the entire sum is bounded for every eligible host, at every odd prime. -/
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV
namespace RiemannReduction.PrincipalLayer
open RiemannReduction.ConductorOne

theorem character_bounds_seven (second : SecondCaseAt PChar.one) (fifth : CountV) (fifthSmall : CountVs) :
    CharacterBounds 7 := by
  obtain ⟨A, ha⟩ := second
  obtain ⟨B, hb⟩ := fifth PChar.one
  obtain ⟨F, hf⟩ := fifthSmall PChar.one
  refine ⟨max A (max B F), ?_⟩
  intro h one t big Ω _ _ _ c e he het ψ hψ
  have member : 7 ∈ Bchi h.chi := by rw [one,exceptional_primes]; decide
  have hN := h.N_pos
  have base : (1:ℝ) ≤ 7 * h.N * e := by
    have x : (1:ℝ) ≤ h.N := by exact_mod_cast hN
    have y : (1:ℝ) ≤ e := by exact_mod_cast he
    nlinarith
  have lift {a : ℕ} (le : a ≤ max A (max B F)) (small : VLe Ω c e ψ ((7*h.N*e:ℝ)^a)) :
      VLe Ω c e ψ ((7*h.N*e:ℝ)^max A (max B F)) := ⟨small.1, small.2.trans (pow_le_pow_right₀ base le)⟩
  have casesAt := (UpperTheory.V.HV.cases h t big c.O ψ (h.mem_X.1 hψ).1 7 e (by decide : Nat.Prime 7) (by decide) he het).2 member
  rcases casesAt with h2 | h4 | h5
  · exact lift (le_max_left _ _) (ha h one t big Ω 7 c e (by decide) he het ψ hψ h2)
  · have zero := RiemannReduction.CyclotomicLayer.all_case_four_seven one big Ω c hψ h4
    refine ⟨by rw [zero]; simp, ?_⟩
    simp only [Vn, zero, Chr.nrm, ENat.toNat_zero, Nat.cast_zero, zero_div, zero_mul]
    positivity
  · by_cases q : h.R1 7 ψ ≤ 2 ^ c2 ψ
    · exact lift ((le_max_left _ _).trans (le_max_right _ _))
        (hb h one t big Ω 7 c e (by decide) he het ψ hψ ⟨h5,q⟩)
    · exact lift ((le_max_right _ _).trans (le_max_right _ _))
        (hf h one t big Ω 7 c e (by decide) he het ψ hψ ⟨h5,lt_of_not_ge q⟩)

theorem all_exceptional (second : SecondCaseAt PChar.one) (fifth : CountV) (small : CountVs)
    (l : Nat.Primes) (exceptional : (l:ℕ) ∈ Bchi PChar.one) : LocalPlusBound l := by
  rw [exceptional_primes,Finset.mem_insert,Finset.mem_singleton] at exceptional
  rcases exceptional with three | seven
  · obtain rfl : l = ⟨3,Nat.prime_three⟩ := Subtype.ext three
    exact inside_three_without_layer second fifth small
  · obtain rfl : l = ⟨7,by decide⟩ := Subtype.ext seven
    have h7 : (7:ℕ) ∈ Bchi PChar.one := by rw [exceptional_primes]; decide
    exact local_plus_of_character_bounds ⟨7,by decide⟩ h7 (character_bounds_seven second fifth small)

open Lean Elab Command in
run_cmd liftTermElabM do
  RiemannReduction.CharacterRestriction.nameHelper
    `Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith `point_arith
    `RiemannReduction.PrincipalLayer.point_arith

def OddPlusBound : Prop :=
  ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : UpperTheory.V.HV.Host, h.chi = PChar.one →
    r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField PChar.one h.ex h.q1 h.d E →
      VVplusLe E t (((h.N:ℝ)*t)^C)

theorem polynomial_odd_plus (first : CountI) (second : SecondCaseAt PChar.one)
    (fifth : CountV) (small : CountVs) (trivial : CountZ) : OddPlusBound := by
  classical
  have inside := all_exceptional second fifth small
  obtain ⟨C0,r₁,r₂,hr₁,hr₂,hO⟩ := RiemannReduction.LocalCases.sumOutside PChar.one (first _) (trivial _) second (by
    refine ⟨0, ?_⟩
    intro h one t _ Ω _ _ _ l _ co e _ _ _ ψ hψ impossible
    exact (case_three_empty one (h.mem_X.1 hψ).1 l e impossible).elim)
  obtain ⟨Cl, hCl⟩ : ∃ Cl : ℕ → ℕ, ∀ (l : Nat.Primes) (hl : (l:ℕ) ∈ Bchi PChar.one),
      Cl l = Classical.choose (inside l hl) :=
    ⟨fun n => if hn : n.Prime ∧ n ∈ Bchi PChar.one then Classical.choose (inside ⟨n, hn.1⟩ hn.2) else 0,
      fun l hl => dif_pos (show (l:ℕ).Prime ∧ (l:ℕ) ∈ Bchi PChar.one from ⟨l.2, hl⟩)⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ l ∈ Bchi PChar.one, Cl l ≤ D :=
    ⟨∑ l ∈ Bchi PChar.one, Cl l, fun l hl => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl⟩
  refine ⟨C0 + D + (Bchi PChar.one).card + (Bchi PChar.one).card * D, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1 h2 h3 h4 t ht hbig E _ _ _ hE Ω _ _ _ ld
  let B : ℝ := 0
  have hB : 0 ≤ B := le_rfl
  have hIn : ∀ l : Nat.Primes, (l:ℕ) ∈ Bchi PChar.one →
      PlusLe ld {l} t (((h.N:ℝ) * t) ^ (Cl l) + (Cl l : ℝ) * B) := by
    intro l hl
    rw [hCl l hl]
    have checked := Classical.choose_spec (inside l hl) h hχ t ht hbig E hE Ω ld
    simpa only [B,mul_zero,add_zero] using checked
  have hOut : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l:ℕ) ≠ 2 ∧ (l:ℕ) ∉ Bchi PChar.one) →
      PlusLe ld S t (((h.N:ℝ) * t) ^ C0) :=
    fun S hS => hO h hχ h1 h2 h3 h4 t ht hbig E hE Ω ld S hS
  have hx2 : (2:ℝ) ≤ (h.N:ℝ) * t := by
    have hN : (1:ℝ) ≤ h.N := by exact_mod_cast h.N_pos
    have ht' : (2:ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  refine ⟨?_, ?_⟩
  · intro p hpf e hp2 he1 he2
    by_cases hb : p ∈ Bchi PChar.one
    · exact (hIn ⟨p, hpf.out⟩ hb).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
    · refine (hOut {⟨p, hpf.out⟩} ?_).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
      intro l hl
      obtain rfl := Finset.mem_singleton.mp hl
      exact ⟨hp2, hb⟩
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l:ℕ) ∈ Bchi PChar.one)]
    have hout2 := (hOut (S.filter (fun l : Nat.Primes => (l:ℕ) ∉ Bchi PChar.one)) (by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨hS2 l hl.1, hl.2⟩)).2
    have hin2 : ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi PChar.one),
        Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
        ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi PChar.one), (((h.N:ℝ) * t) ^ D + (D:ℝ) * B) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_filter] at hl
      have h0 := (hIn l hl.2).2
      rw [Finset.sum_singleton] at h0
      have hle := hD l hl.2
      have hp1 : ((h.N:ℝ) * t) ^ (Cl l) ≤ ((h.N:ℝ) * t) ^ D := pow_le_pow_right₀ (by linarith) hle
      have hp2 : (Cl l : ℝ) * B ≤ (D:ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hB
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at hin2
    have hcard : (S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi PChar.one)).card ≤ (Bchi PChar.one).card :=
      Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l:ℕ))
        (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn
    have key := point_arith ((h.N:ℝ) * t) B hx2 hB _ (Bchi PChar.one).card D C0 hcard
    simp only [B,mul_zero,add_zero] at key hin2
    linarith

#print axioms polynomial_odd_plus
end RiemannReduction.PrincipalLayer
