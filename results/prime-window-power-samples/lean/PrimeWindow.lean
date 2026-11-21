import DyadicArithmetic
import DelayedPole
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypOfRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannZetaNeZeroOfMemIoo
import Formalism.GammaFactorNonvanishing.RhOfRight

open Complex MeasureTheory Set Filter Topology Deduction

noncomputable section
namespace ThetaTransfer

private def zetaFamily : CharFamily where
  ι := Unit
  N := fun _ => 1
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

private theorem zeta_gm (u : ℝ) : gm zetaFamily u = G (Real.exp u) := by
  have h (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  change (∑ _i : Unit, (1 : ℝ) * (Gchi (1 : DirichletCharacter ℂ 1) (Real.exp u)).re) = _
  rw [Fintype.sum_unique, one_mul]
  unfold Gchi G
  rw [if_pos rfl, show (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) = (fun _ => 1) from funext h]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]

def primeDeficit (u : ℝ) : ℝ :=
  2 * Real.log 2 * (Real.exp u / 4) - primeSum (Real.exp u / 4)

def primePowerDeficit (u : ℝ) : ℝ :=
  2 * Real.log 2 * (Real.exp u / 4) - primePowerSum (Real.exp u / 4)

theorem compactDifference_eq_primePowerDeficit {u : ℝ} (hu : 2 * Real.log 2 < u) :
    compactDifference (Real.log 2) (gm zetaFamily) u = primePowerDeficit u := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (2 * Real.log 2) = 4 := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  have hy : 0 < Real.exp u / 4 := by positivity
  rw [primePowerDeficit, deficit_eq_centered_ramps hy]
  simp only [compactDifference, delay, if_pos (show 0 < u by linarith),
    if_pos (show Real.log 2 < u by linarith), if_pos hu, sub_zero, zeta_gm,
    Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<2), he]
  ring_nf

/-- Window estimates transfer through any eventual upper bound on the original observable. -/
private theorem window_of_le_after {f g : ℝ → ℝ} {θ δ U₁ : ℝ}
    (hfg : ∀ u ≥ U₁, f u ≤ g u) (hW : WindowHypU g θ δ) : WindowHypU f θ δ := by
  intro η hη U₀
  obtain ⟨U, hU, R, hi, hR, hmass⟩ := hW η hη (max U₀ U₁)
  exact ⟨U, (le_max_left _ _).trans hU, R, hi, fun u hu =>
    ⟨(hR u hu).1, (hfg u (((le_max_right _ _).trans hU).trans hu.1)).trans (hR u hu).2⟩, hmass⟩

theorem zeta_zeroFree_of_primePower_window {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hδ : 0 < δ) (hW : WindowHypU primePowerDeficit θ δ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  have h := compactDifference_zeroFree zetaFamily hθ hθ1 hδ
    (window_of_le_after (U₁ := 2 * Real.log 2 + 1)
      (fun u hu => (compactDifference_eq_primePowerDeficit (by linarith : 2 * Real.log 2 < u)).le) hW)
  intro s hs
  simpa [zetaFamily, DirichletCharacter.LFunction_modOne_eq] using h () s hs

/-- A one-sided test that samples genuine primes in (exp(u)/4, exp(u)). -/
theorem zeta_zeroFree_of_prime_window {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hδ : 0 < δ) (hW : WindowHypU primeDeficit θ δ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  zeta_zeroFree_of_primePower_window hθ hθ1 hδ
    (window_of_le_after (U₁ := 0) (fun u _ =>
      sub_le_sub_left (primeSum_le_primePowerSum (Real.exp u / 4)) _) hW)

theorem no_small_primePower_windows_of_zero {ρ : ℂ} (hz : riemannZeta ρ = 0)
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hr : θ < ρ.re) :
    ¬ WindowHypU primePowerDeficit θ δ :=
  fun h => zeta_zeroFree_of_primePower_window hθ hθ1 hδ h ρ hr hz

theorem window_of_point_bounds {f : ℝ → ℝ} {θ δ : ℝ} (hδ : 0 < δ)
    (h : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1+δ)*U), f u ≤ Real.exp (θ*u)) :
    WindowHypU f θ δ := by
  intro η hη U₀
  obtain ⟨X, hX⟩ := windowHyp_of_rpow_eventually δ η hδ.le hη
  obtain ⟨U, hU, hb⟩ := h (max U₀ (max 0 (Real.log X)))
  have hn := (le_max_right U₀ (max 0 (Real.log X))).trans hU
  have hu0 := (le_max_left 0 (Real.log X)).trans hn
  have hXU : X ≤ Real.exp U := by
    by_cases hXp : 0 < X
    · exact (Real.log_le_iff_le_exp hXp).mp ((le_max_right 0 _).trans hn)
    · linarith [Real.exp_pos U]
  have hmass := (hX (Real.exp U) hXU).2
  rw [Real.log_exp, ← Real.exp_mul] at hmass
  have heq : (fun u : ℝ => Real.exp (θ*u) * Real.exp (-θ*u)) = fun _ => (1:ℝ) := by
    funext u; rw [← Real.exp_add]; ring_nf; simp
  refine ⟨U, (le_max_left _ _).trans hU, fun u => Real.exp (θ*u), ?_,
    fun u hu => ⟨(Real.exp_pos _).le, hb u hu⟩, ?_⟩
  · rw [heq]; exact continuousOn_const.integrableOn_Icc
  · rw [heq, setIntegral_const, Real.volume_real_Icc_of_le (by nlinarith : U ≤ (1+δ)*U)]
    simpa [smul_eq_mul, add_mul, mul_comm] using (show (1+δ)*U-U ≤ Real.exp (η*U) by
      calc (1+δ)*U-U = δ*U := by ring
           _ ≤ Real.exp (η*U) := by simpa [mul_comm] using hmass)

/-- Every sufficiently late power window has an endpoint with a large prime-power deficit. -/
theorem deficit_on_every_late_window {ρ : ℂ} (hz : riemannZeta ρ = 0)
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hr : θ < ρ.re) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀, ∃ u ∈ Icc U ((1+δ)*U), Real.exp (θ*u) < primePowerDeficit u := by
  by_contra! hn
  exact no_small_primePower_windows_of_zero hz hθ hθ1 hδ hr (window_of_point_bounds hδ hn)

theorem prime_deficit_on_every_late_window {ρ : ℂ} (hz : riemannZeta ρ = 0)
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hr : θ < ρ.re) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀, ∃ u ∈ Icc U ((1+δ)*U), Real.exp (θ*u) < primeDeficit u := by
  obtain ⟨U₀, h⟩ := deficit_on_every_late_window hz hθ hθ1 hδ hr
  refine ⟨U₀, fun U hU => ?_⟩
  obtain ⟨u, hu, hb⟩ := h U hU
  exact ⟨u, hu, hb.trans_le (sub_le_sub_left (primeSum_le_primePowerSum (Real.exp u / 4)) _)⟩

private theorem neg_poleData {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (p : PoleData g Φ Z)
    (h : ∀ z ∈ Z, z.im ≠ 0) : PoleData (fun u => -g u) (fun s => -Φ s) Z := by
  obtain ⟨C, hC⟩ := p.growth
  refine ⟨p.meas.neg, ⟨C, fun u hu => by simpa using hC u hu⟩, ?_, p.pos, p.diff.neg, p.iso, ?_⟩
  · intro s hs
    simpa [p.laplace s hs] using
      (integral_neg (μ := volume.restrict (Ioi (0 : ℝ))) (fun u : ℝ => (g u : ℂ) * cexp (-s*u))).symm
  · intro ρ hρ
    obtain ⟨a, ha, _, f, hf, he⟩ := p.pole ρ hρ
    refine ⟨-a, neg_ne_zero.mpr ha, fun hi => False.elim (h ρ hρ hi), fun s => -f s, hf.neg, ?_⟩
    filter_upwards [he] with s hs
    rw [hs]; ring

theorem zeta_zeroFree_of_surplus {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hδ : 0 < δ) (hW : WindowHypU (fun u => -primePowerDeficit u) θ δ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨Φ,p⟩ := poleData zetaFamily
  have strip : ∀ z ∈ zeroSet zetaFamily, z.re < 1 := by
    rintro z ⟨_, i, hi | hi⟩ <;> by_contra! h
    · exact charFamily_LFunction_ne_zero_of_one_le_re zetaFamily i z h hi
    · exact charFamily_LFunction_ne_zero_of_one_le_re zetaFamily i _ (by simpa using h) hi
  have nr : ∀ z ∈ zeroSet zetaFamily, z.im ≠ 0 := by
    intro z hz hi
    have hlt := strip z hz
    obtain ⟨hp,i,he⟩ := hz
    have hne := GlobalTheory.RealZeros.riemannZeta_ne_zero_of_mem_Ioo z.re hp hlt
    have ee : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hi])
    have ez : (starRingEnd ℂ) z = z := by rw [← ee]; simp
    rw [ee] at hne
    simp [zetaFamily, DirichletCharacter.LFunction_modOne_eq, ez, hne] at he
  have hw := window_of_le_after (U₁ := 2*Real.log 2 + 1)
    (f := fun u => -compactDifference (Real.log 2) (gm zetaFamily) u)
    (fun u hu => (congrArg Neg.neg (compactDifference_eq_primePowerDeficit (by linarith : 2*Real.log 2 < u))).le) hW
  have hz := landau_window (neg_poleData (compactDifference_poleData p strip) nr) hθ hθ1 hδ hw
  intro s hs he
  have mem : s ∈ zeroSet zetaFamily := ⟨by linarith, (), Or.inl (by
    simpa [zetaFamily, DirichletCharacter.LFunction_modOne_eq] using he)⟩
  exact (not_le_of_gt hs) (hz s mem)

/-- Even a sparse sequence of whole power windows with the indicated sign excludes
    every zeta zero strictly to the right of one half. -/
theorem zeroFree_of_prime_sign_windows {δ : ℝ} (hδ : 0 < δ)
    (sign : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1+δ)*U), 0 ≤ primeDeficit u) :
    ∀ s : ℂ, 1/2 < s.re → riemannZeta s ≠ 0 := by
  intro s hs
  let θ := (1/2 + min 1 s.re) / 2
  have ht : 1/2 < θ := by dsimp [θ]; have := lt_min (by norm_num : (1:ℝ)/2 < 1) hs; linarith
  have ht1 : θ < 1 := by dsimp [θ]; linarith [min_le_left (1:ℝ) s.re]
  have hts : θ < s.re := by dsimp [θ]; linarith [min_le_right (1:ℝ) s.re]
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  apply zeta_zeroFree_of_surplus (by linarith : 0 < θ) ht1 hδ _ s hts
  apply window_of_point_bounds hδ
  intro U₀
  let K := max 1 C
  have hk : 0 < K := (by dsimp [K]; exact (zero_lt_one.trans_le (le_max_left _ _)))
  have hd : 0 < θ - 1/2 := by linarith
  obtain ⟨U, hU, hu⟩ := sign (max U₀ (Real.log K / (θ - 1/2)))
  refine ⟨U, (le_max_left _ _).trans hU, fun u hm => ?_⟩
  have he := (le_max_right U₀ _).trans (hU.trans hm.1)
  have hx : K ≤ Real.exp ((θ - 1/2)*u) := (Real.log_le_iff_le_exp hk).mp (by
    have := (div_le_iff₀ hd).mp he; linarith)
  have hp := primePowerGap_le (Real.exp u / 4)
  rw [show 4*(Real.exp u / 4) = Real.exp u by ring] at hp
  have hsqrt : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
  have hb := hp.trans (hC _)
  rw [hsqrt] at hb
  have hb' : C * Real.exp (u/2) ≤ Real.exp (θ*u) := by
    calc C * Real.exp (u/2) ≤ K * Real.exp (u/2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
        _ ≤ Real.exp ((θ-1/2)*u) * Real.exp (u/2) :=
          mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
        _ = Real.exp (θ*u) := by rw [← Real.exp_add]; congr 1; ring
  have hp' := hu u hm
  unfold primeDeficit at hp'
  unfold primePowerDeficit
  linarith

/-- Sparse intervals of positions of a finite sum of ordinary primes suffice for RH. -/
theorem rh_of_prime_sign_windows {δ : ℝ} (hδ : 0 < δ)
    (sign : ∀ X₀ : ℝ, ∃ X ≥ X₀, ∀ x ∈ Icc X (X ^ (1 + δ)),
      primeSum (x / 4) ≤ (x / 2) * Real.log 2) : RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  apply zeroFree_of_prime_sign_windows hδ _ s hs
  intro U₀
  obtain ⟨X, hX, h⟩ := sign (Real.exp U₀)
  have hx : 0 < X := (Real.exp_pos U₀).trans_le hX
  refine ⟨Real.log X, (Real.le_log_iff_exp_le hx).mpr hX, fun u hu => ?_⟩
  have lo : X ≤ Real.exp u := (Real.log_le_iff_le_exp hx).mp hu.1
  have hi : Real.exp u ≤ X ^ (1 + δ) := by
    rw [Real.rpow_def_of_pos hx]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hu.2)
  have hb := h _ ⟨lo, hi⟩
  unfold primeDeficit
  linarith

#print axioms ThetaTransfer.compactDifference_zeroFree
#print axioms ThetaTransfer.rh_of_prime_sign_windows
#print axioms ThetaTransfer.zeta_zeroFree_of_prime_window
#print axioms ThetaTransfer.no_small_primePower_windows_of_zero
#print axioms ThetaTransfer.prime_deficit_on_every_late_window
#print axioms ThetaTransfer.zeroFree_of_prime_sign_windows

end ThetaTransfer
