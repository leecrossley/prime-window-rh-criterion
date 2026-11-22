import PrincipalLocalCounts
import PrincipalTrivialLayer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalLe

/-! The reduction and normalization in the inside-prime estimate follow FinalLe.lean.
A pointwise estimate on the host characters suffices whenever its fourth case vanishes. -/
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

namespace RiemannReduction.PrincipalLayer
open RiemannReduction.ConductorOne

def CharacterBounds (l : ℕ) [Fact l.Prime] : Prop :=
  ∃ C : ℕ, ∀ h : UpperTheory.V.HV.Host, h.chi = PChar.one → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (c : Coef l)
      (e : ℕ), 0 < e → e < t → ∀ ψ ∈ h.X c e, VLe Ω c e ψ (((l : ℝ) * h.N * e)^C)

theorem character_bounds_three (second : SecondCaseAt PChar.one) (fifth : CountV) (fifthSmall : CountVs) :
    CharacterBounds 3 := by
  obtain ⟨A, ha⟩ := second
  obtain ⟨B, hb⟩ := fifth PChar.one
  obtain ⟨F, hf⟩ := fifthSmall PChar.one
  refine ⟨max A (max B F), ?_⟩
  intro h one t big Ω _ _ _ c e he het ψ hψ
  have member : 3 ∈ Bchi h.chi := by unfold Bchi; exact Finset.mem_insert_self _ _
  have hN := h.N_pos
  have base : (1:ℝ) ≤ 3 * h.N * e := by
    have x : (1:ℝ) ≤ h.N := by exact_mod_cast hN
    have y : (1:ℝ) ≤ e := by exact_mod_cast he
    nlinarith
  have lift {a : ℕ} (le : a ≤ max A (max B F)) (small : VLe Ω c e ψ ((3*h.N*e:ℝ)^a)) :
      VLe Ω c e ψ ((3*h.N*e:ℝ)^max A (max B F)) := ⟨small.1, small.2.trans (pow_le_pow_right₀ base le)⟩
  have casesAt := (UpperTheory.V.HV.cases h t big c.O ψ (h.mem_X.1 hψ).1 3 e Nat.prime_three (by decide) he het).2 member
  rcases casesAt with h2 | h4 | h5
  · exact lift (le_max_left _ _) (ha h one t big Ω 3 c e (by decide) he het ψ hψ h2)
  · have zero := case_four_at_three one big Ω c hψ h4
    refine ⟨by rw [zero]; simp, ?_⟩
    simp only [Vn, zero, Chr.nrm, ENat.toNat_zero, Nat.cast_zero, zero_div, zero_mul]
    positivity
  · by_cases q : h.R1 3 ψ ≤ 2 ^ c2 ψ
    · exact lift ((le_max_left _ _).trans (le_max_right _ _))
        (hb h one t big Ω 3 c e (by decide) he het ψ hψ ⟨h5,q⟩)
    · exact lift ((le_max_right _ _).trans (le_max_right _ _))
        (hf h one t big Ω 3 c e (by decide) he het ψ hψ ⟨h5,lt_of_not_ge q⟩)

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in #[`sum_split,`final_le] do
    RiemannReduction.CharacterRestriction.nameHelper
      `Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalLe n
      (`RiemannReduction.PrincipalLayer ++ n)

def LocalPlusBound (l : Nat.Primes) : Prop :=
  ∃ C : ℕ, ∀ h : UpperTheory.V.HV.Host, h.chi = PChar.one → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField PChar.one h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
        PlusLe ld {l} t (((h.N : ℝ) * t)^C)

theorem local_plus_of_character_bounds (l : Nat.Primes) [Fact (l:ℕ).Prime]
    (hl : (l:ℕ) ∈ Bchi PChar.one) (pointwise : CharacterBounds l) : LocalPlusBound l := by
  obtain ⟨C, bound⟩ := pointwise
  refine ⟨2*C+9, ?_⟩
  intro h one t ht2 hBig E _ _ _ hE Ω _ _ _ ld
  classical
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.instIsAlgClosure (k := ℚ))
    · rfl
    · exact Subsingleton.elim _ _
  have : NeZero h.N := ⟨h.N_pos.ne'⟩
  have : NeZero (Nat.totient h.N) := ⟨(Nat.totient_pos.2 h.N_pos).ne'⟩
  obtain ⟨c, hc⟩ := exists_coef (l : ℕ) (Nat.totient h.N)
  have := hc
  have hlp : (l : ℕ).Prime := l.2
  have hl2 : (l : ℕ) ≠ 2 := (prime_of_mem_Bchi hl).2
  have hlB : (l : ℕ) ∈ Bchi h.chi := by
    rw [one]
    exact hl
  have hbf := bchiFacts h t hBig
  have hlq1 : (l : ℕ) < h.q1 := (hbf.1 _ hlB).1
  have hld : (l : ℕ) < h.d := (hbf.1 _ hlB).2
  have hidx := hostIndex h
  have hNpos : 0 < h.N := h.N_pos
  have hq1N : h.q1 ≤ h.N := Nat.le_of_dvd hNpos h.host_q1_dvd_N
  have hqN : h.q ≤ h.N := Nat.le_of_dvd hNpos h.q_dvd
  have h16 : 16 ≤ h.N := Nat.le_of_dvd hNpos hidx.2.2.1
  have hlN : (l : ℕ) ≤ h.N := by omega
  set M : ℝ := (h.N : ℝ) * t with hMdef
  set L : ℝ := Real.log ((l : ℕ) : ℝ) with hLdef
  have hN1 : (1 : ℝ) ≤ h.N := by exact_mod_cast (by omega : 1 ≤ h.N)
  have hM3 : 3 ≤ M := by
    have a1 : (16 : ℝ) ≤ h.N := by exact_mod_cast h16
    have a2 : (2 : ℝ) ≤ t := by exact_mod_cast ht2
    rw [hMdef]
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hl1 : (1 : ℝ) ≤ ((l : ℕ) : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hL0 : 0 ≤ L := Real.log_nonneg hl1
  have hLl : L ≤ ((l : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((l : ℕ) : ℝ) by linarith)
    linarith
  have hNM : (h.N : ℝ) ≤ M := by
    have a2 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    rw [hMdef]
    nlinarith
  have hlM : ((l : ℕ) : ℝ) ≤ M := le_trans (by exact_mod_cast hlN) hNM
  have hqM : (h.q : ℝ) ≤ M := le_trans (by exact_mod_cast hqN) hNM
  have hKb : ∀ e, 0 < e → e < t → ∀ k ≤ C, (((l : ℕ) : ℝ) * h.N * e) ^ k ≤ (M ^ 2) ^ C := by
    intro e he0 het k hk
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have het' : (e : ℝ) ≤ t := by exact_mod_cast het.le
    have hx1 : 1 ≤ ((l : ℕ) : ℝ) * h.N * e := by
      have a1 : 1 ≤ ((l : ℕ) : ℝ) * h.N := by nlinarith
      nlinarith
    have hx2 : ((l : ℕ) : ℝ) * h.N * e ≤ M ^ 2 := by
      have a1 : (h.N : ℝ) * e ≤ M := by
        rw [hMdef]
        exact mul_le_mul_of_nonneg_left het' (by linarith)
      calc ((l : ℕ) : ℝ) * h.N * e = ((l : ℕ) : ℝ) * (h.N * e) := by ring
        _ ≤ M * M := mul_le_mul hlM a1 (by positivity) hM0
        _ = M ^ 2 := by ring
    calc (((l : ℕ) : ℝ) * h.N * e) ^ k ≤ (((l : ℕ) : ℝ) * h.N * e) ^ C := pow_le_pow_right₀ hx1 hk
      _ ≤ (M ^ 2) ^ C := pow_le_pow_left₀ (by linarith) hx2 C
  have hkey : ∀ e, 0 < e → e < t → ∀ ψ ∈ h.X c e,
      Vlen (AlgebraicClosure ℚ) c e ψ ≠ ⊤ ∧
        Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) * L ≤ (M ^ 2) ^ C := by
    intro e he het ψ hψ
    have hv := bound h one t hBig (AlgebraicClosure ℚ) c e he het ψ hψ
    exact ⟨hv.1,hv.2.trans (hKb e he het C le_rfl)⟩
  have hXsub : ∀ e, h.X c e ⊆ h.X c 0 ∪ h.X c 1 := by
    intro e ψ hψ
    rw [Host.mem_X] at hψ
    rw [Finset.mem_union, Host.mem_X, Host.mem_X]
    have h2 := hψ.2
    unfold PsiEven at h2
    rcases Nat.even_or_odd e with he | he
    · left
      refine ⟨hψ.1, ?_⟩
      unfold PsiEven
      rw [h2, he.neg_one_pow, pow_zero]
    · right
      refine ⟨hψ.1, ?_⟩
      unfold PsiEven
      rw [h2, he.neg_one_pow, pow_one]
  have hred : ∀ e, 0 < e → e < t → plusLen (ld (l : ℕ)) e * eO (l : ℕ) c.O ≤
      ∑ ψ ∈ h.X c e, (Vlen (AlgebraicClosure ℚ) c e ψ + (lossAll (l : ℕ) h.N h.H.index e : ℕ∞) * eO (l : ℕ) c.O) := by
    intro e he0 het
    exact redAll E h.N h.H (hostLevel h E (by rw [one]; exact hE)) (l : ℕ) hl2 c Ω (ld (l : ℕ)) (AlgebraicClosure ℚ) e he0.ne' (h.X c e)
      (by
        ext ψ
        rw [Finset.mem_coe, Host.mem_X]
        rfl)
  have hsb := Chr.sumBack (l : ℕ) c.O (DirichletCharacter c.O h.N) (fun e => h.X c e) (h.X c 0 ∪ h.X c 1)
    (fun ψ e => Vlen (AlgebraicClosure ℚ) c e ψ) (fun e => plusLen (ld (l : ℕ)) e)
    (fun e => lossAll (l : ℕ) h.N h.H.index e) t hXsub
    (fun e he0 het => ⟨fun ψ hψ => (hkey e he0 het ψ hψ).1, hred e he0 het⟩)
  have hA : (∑ e ∈ Finset.Ico 1 t, ((plusLen (ld (l : ℕ)) e).toNat : ℝ)) ≤
      (∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X c e, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ)) +
        ((h.X c 0 ∪ h.X c 1).card : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) := hsb.2
  have hloss : ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ t * M ^ 6 := by
    calc ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, M ^ 6 := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, het⟩ := Finset.mem_Ico.1 he
          have hb := (lossLe (l : ℕ) h.N h.H.index e hlp hl2 (by omega) hidx.2.1 he1).1
          have hb' : ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ (((h.N * e) ^ 6 : ℕ) : ℝ) := by
            exact_mod_cast hb
          have het' : (e : ℝ) ≤ t := by exact_mod_cast het.le
          calc ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ (((h.N * e) ^ 6 : ℕ) : ℝ) := hb'
            _ = ((h.N : ℝ) * e) ^ 6 := by push_cast; ring
            _ ≤ M ^ 6 := by
              apply pow_le_pow_left₀ (by positivity)
              rw [hMdef]
              exact mul_le_mul_of_nonneg_left het' (by positivity)
      _ = ((Finset.Ico 1 t).card : ℝ) * M ^ 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ t * M ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Ico]
          exact_mod_cast Nat.sub_le t 1
  have hsplit := sum_split (fun e => h.X c e) ∅ (fun ψ e => Chr.nrm (l:ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ))
    t h.N 0 L ((M^2)^C) 0 (fun ψ e => Vn_nonneg (AlgebraicClosure ℚ) c e ψ) hL0 (by positivity)
    (by rfl) (fun e => (xCard c.O h.N).1 _) (by simp)
    (fun e he ψ hψ => Or.inr (hkey e (Finset.mem_Ico.1 he).1 (Finset.mem_Ico.1 he).2 ψ hψ).2)
    (by simp)
  simp only [Nat.cast_zero, mul_zero, zero_add] at hsplit
  have hT0 : ((h.X c 0 ∪ h.X c 1).card : ℝ) ≤ h.N := by exact_mod_cast (xCard c.O h.N).1 _
  have hlossnn : 0 ≤ ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have s1 := mul_le_mul_of_nonneg_left hA hL0
  rw [mul_add] at s1
  have s2 : L * (((h.X c 0 ∪ h.X c 1).card : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ)) ≤
      L * (h.N * (t * M ^ 6)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hT0 hloss hlossnn (by positivity)) hL0
  have finish := final_le M L ((l:ℕ):ℝ) 0 h.N t 0 0 C (2*C+9) hMdef hM3 hLl
    (by positivity) hlM (by rfl) hM0 (by rfl) (by omega) (by rw [mul_zero]; positivity)
  simp only [zero_add, zero_mul, mul_zero, add_zero] at finish
  refine ⟨?_, ?_⟩
  · intro p hp e he het
    rw [Finset.mem_singleton] at hp
    subst hp
    exact hsb.1 e he het
  · rw [Finset.sum_singleton]
    linarith

theorem inside_three_without_layer (second : SecondCaseAt PChar.one) (fifth : CountV) (fifthSmall : CountVs) :
    LocalPlusBound ⟨3,Nat.prime_three⟩ :=
  local_plus_of_character_bounds ⟨3,Nat.prime_three⟩ (Finset.mem_insert_self _ _) (character_bounds_three second fifth fifthSmall)

#print axioms inside_three_without_layer
end RiemannReduction.PrincipalLayer
