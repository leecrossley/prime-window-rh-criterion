import PrincipalConductorMinus
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN

/-! A joint window at the principal character suffices for its full arithmetic window.
    The scale and conductor comparisons adapt the archive's
    UpperTheory.V.vwinAt_of_joint in CMFieldExponentialBounds.AdmissibleOfPageN. -/

noncomputable section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V
namespace RiemannReduction.ConductorOne

/-- Only the actual page functions and the ordinary character are requested. -/
def PrincipalJointPages (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1/52 → ∀ e : ℝ → ℕ, (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
    let t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊
    ∃ J C P X0 : ℝ, 0 < J ∧ ∀ X ≥ X0, ∀ q d : ℕ, PrimePair 1 q d →
      2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) → P < (q : ℝ) → P < (d : ℝ) →
      Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
      ∃ Y : ℝ, InRange J X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
        BaAt (AbF.ofChar PChar.one) eps e t q d x ∧ HVAt PChar.one C eps e t q d x

theorem principal_pages_of_joint {Ct : ℝ} (hC : 1 ≤ Ct) (joint : JointWin Ct) :
    PrincipalJointPages Ct := fun eps hp hlt e he =>
  joint PChar.one eps 4 hp hlt e _ (admissible_of_pageN hp hlt hC he)

theorem principal_window_of_joint_pages {Ct : ℝ} (hC : 1 ≤ Ct)
    (joint : PrincipalJointPages Ct) : VWinAt PChar.one Ct := by
  intro eps h0 h1 e he
  let ψ := PChar.one
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : admitted 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := joint eps h0 h1 e he
  obtain ⟨K, hK0, hK⟩ := minusBound_le_exp_of_log_le 0 (AbF.ofChar ψ).deg
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' := ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2), le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log (↑q * ↑d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hpp : PrimePair 1 q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod, Nat.coprime_one_right _⟩
  obtain ⟨Y, ⟨hYlo, hYhi⟩, hY⟩ := hmain X hXJ q d hpp hq3 hd3 hPq hPd hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hBa, hHV⟩ := hY x hxY hxY2
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hq4 : q % 4 = 3 := by
    have := hw.q_mod
    omega
  have : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  obtain ⟨hc1, hc2, hc3⟩ := conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE
  obtain ⟨hj, _, ht2, htle⟩ := hadm x hx2
  have hm := principal_minus_at_conductor hj hpp hE ht2
  have ht1 : 1 ≤ t x := by omega
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log (↑q * ↑d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hm' := VVminusLe.mono hm hmb
  have hv := vvle_of_parts h2 hm' hp
  have hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) _ hu1 hNt
  exact VVle.mono hv le_rfl htot

theorem principal_window_of_joint {Ct : ℝ} (hC : 1 ≤ Ct) (joint : JointWin Ct) :
    VWinAt PChar.one Ct :=
  principal_window_of_joint_pages hC (principal_pages_of_joint hC joint)

end RiemannReduction.ConductorOne
