import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL

open Complex MeasureTheory Set Filter Topology
open Deduction

noncomputable section
namespace ThetaTransfer

def delay (a : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := if a < u then g (u - a) else 0

def compactDifference (c : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  -delay 0 g u + 3 * delay c g u - 2 * delay (2*c) g u

private theorem delay_meas {g : ℝ → ℝ} (hg : Measurable g) (a : ℝ) : Measurable (delay a g) := by
  exact (hg.comp (measurable_id.sub_const a)).ite measurableSet_Ioi measurable_const

private theorem delay_growth {g : ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2*u)) (u : ℝ) :
    |delay a g u| ≤ C * Real.exp (2*u) := by
  unfold delay
  split_ifs with h
  · refine (hg _ (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.exp_le_exp.mpr (by linarith)
  · simpa using mul_nonneg hC (Real.exp_pos (2*u)).le

private theorem laplace_integrable {g : ℝ → ℝ} (hm : Measurable g) {C : ℝ}
    (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2*u)) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => (g u : ℂ) * cexp (-s * u)) (Ioi 0) := by
  let b := s.re - 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hi := (iteratedDeriv_laplace_int 0 b hb).const_mul C
  apply Integrable.mono' hi
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    simpa using iteratedDeriv_laplace_bound g C hg 0 b s (by dsimp [b]; linarith) u hu

private theorem laplace_delay (g : ℝ → ℝ) (s : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ u in Ioi (0 : ℝ), (delay a g u : ℂ) * cexp (-s * u)) =
      cexp (-s * a) * ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-s * u) := by
  let f := (Ioi (0 : ℝ)).indicator (fun v : ℝ => (g v : ℂ) * cexp (-s * v))
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h : (Ioi (0 : ℝ)).indicator (fun u : ℝ => (delay a g u : ℂ) * cexp (-s * u)) =
      fun u : ℝ => cexp (-s * a) * f (u + -a) := by
    funext u
    by_cases hau : a < u
    · have h0 : 0 < u := lt_of_le_of_lt ha hau
      have h1 : 0 < u - a := by linarith
      simp only [indicator_of_mem (show u ∈ Ioi (0:ℝ) from h0), delay, if_pos hau, f,
        ← sub_eq_add_neg, indicator_of_mem (show u - a ∈ Ioi (0:ℝ) from h1)]
      have ee : cexp (-s * (u : ℂ)) = cexp (-s * a) * cexp (-s * ((u-a : ℝ) : ℂ)) := by
        rw [← Complex.exp_add, Complex.ofReal_sub]; congr 1; ring
      rw [ee]; ring
    · have h1 : u + -a ∉ Ioi (0 : ℝ) := by change ¬ 0 < u + -a; linarith
      simp only [f, indicator_of_notMem h1, mul_zero]
      by_cases h0 : u ∈ Ioi (0 : ℝ)
      · simp [indicator_of_mem h0, delay, hau]
      · simp [h0]
  rw [h, integral_const_mul, integral_add_right_eq_self]

def symbol (c : ℝ) (s : ℂ) : ℂ :=
  (1 - cexp (-s*c)) * (2 * cexp (-s*c) - 1)

private theorem symbol_analytic (c : ℝ) (s : ℂ) : AnalyticAt ℂ (symbol c) s := by
  apply Differentiable.analyticAt
  unfold symbol
  fun_prop

private theorem symbol_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    symbol (Real.log 2) s ≠ 0 := by
  set c := Real.log 2 with hc
  have hc0 : 0 < c := Real.log_pos (by norm_num)
  have he : ‖cexp (-s * (c : ℂ))‖ = Real.exp (-s.re * c) := by
    simp [Complex.norm_exp]
  have upper : ‖cexp (-s * (c : ℂ))‖ < 1 := by
    rw [he, Real.exp_lt_one_iff]
    nlinarith
  have lower : 1 / 2 < ‖cexp (-s * (c : ℂ))‖ := by
    have hh : Real.exp (-c) = 1/2 := by rw [Real.exp_neg, hc, Real.exp_log (by norm_num)]; norm_num
    rw [← hh, he, Real.exp_lt_exp]
    nlinarith
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    rw [← h, norm_one] at upper
    linarith
  · apply sub_ne_zero.mpr
    intro h
    have hh := congrArg norm h
    rw [norm_mul, norm_one] at hh
    norm_num only [Complex.norm_ofNat] at hh
    linarith

private theorem symbol_real {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hi : s.im = 0) :
    0 < (symbol (Real.log 2) s).re ∧ (symbol (Real.log 2) s).im = 0 := by
  let c := Real.log 2
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hlt : Real.exp (-s.re*c) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hhalf : Real.exp (-c) = 1/2 := by
    rw [Real.exp_neg, show c = Real.log 2 by rfl, Real.exp_log (by norm_num)]; norm_num
  have hgt : 1/2 < Real.exp (-s.re*c) := by rw [← hhalf, Real.exp_lt_exp]; nlinarith
  have hs : (s.re : ℂ) = s := Complex.ext (by simp) (by simp [hi])
  have he : cexp (-s*(c:ℂ)) = (Real.exp (-s.re*c) : ℝ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, hs]
  let q := Real.exp (-s.re*c)
  have eq : symbol c s = (((1-q)*(2*q-1) : ℝ) : ℂ) := by
    unfold symbol; rw [he]
    simp only [q, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
  change 0 < (symbol c s).re ∧ (symbol c s).im = 0
  rw [eq, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨mul_pos (sub_pos.mpr hlt) (by dsimp [q]; linarith), rfl⟩

/-- A delayed second difference keeps every pole of a Dirichlet-family transform. -/
theorem compactDifference_poleData {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (p : PoleData g Φ Z) (strip : ∀ ρ ∈ Z, ρ.re < 1) :
    PoleData (compactDifference (Real.log 2) g) (fun s => symbol (Real.log 2) s * Φ s) Z := by
  let c := Real.log 2
  have hc : 0 ≤ c := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
  obtain ⟨C, hC⟩ := p.growth
  have hCp : 0 ≤ C := by
    have h := hC 0 le_rfl
    simpa using (abs_nonneg (g 0)).trans h
  have hg (a : ℝ) (ha : 0 ≤ a) := delay_growth hCp ha hC
  refine ⟨((delay_meas p.meas 0).neg.add (measurable_const.mul (delay_meas p.meas c))).sub
    (measurable_const.mul (delay_meas p.meas (2*c))), ⟨6*C, ?_⟩, ?_, p.pos, ?_, p.iso, ?_⟩
  · intro u _
    change |-(delay 0 g u) + 3 * delay c g u - 2 * delay (2*c) g u| ≤ _
    have h := abs_add_le (-(delay 0 g u) + 3 * delay c g u) (-(2 * delay (2*c) g u))
    rw [← sub_eq_add_neg, abs_neg] at h
    have h' := abs_add_le (-(delay 0 g u)) (3 * delay c g u)
    rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3)] at h'
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at h
    linarith [hg 0 le_rfl u, hg c hc u, hg (2*c) (by positivity) u]
  · intro s hs
    let I (a : ℝ) (u : ℝ) := (delay a g u : ℂ) * cexp (-s*u)
    have hi (a : ℝ) (ha : 0 ≤ a) : IntegrableOn (I a) (Ioi 0) :=
      laplace_integrable (delay_meas p.meas a) (fun u _ => hg a ha u) hs
    have hfunc : (fun u : ℝ => (compactDifference c g u : ℂ) * cexp (-s*u)) =
        fun u => -I 0 u + (3:ℂ)*I c u - (2:ℂ)*I (2*c) u := by
      funext u; dsimp [compactDifference, I]; push_cast; ring
    change symbol c s * Φ s = ∫ u in Ioi (0:ℝ), (compactDifference c g u : ℂ) * cexp (-s*u)
    rw [hfunc, integral_sub (f := fun u => -I 0 u + (3:ℂ)*I c u) (g := fun u => (2:ℂ)*I (2*c) u)
      ((hi 0 le_rfl).neg.add ((hi c hc).const_mul 3)) ((hi (2*c) (by positivity)).const_mul 2),
      integral_add (f := fun u => -I 0 u) (g := fun u => (3:ℂ)*I c u)
        (hi 0 le_rfl).neg ((hi c hc).const_mul 3), integral_neg,
      integral_const_mul, integral_const_mul]
    change _ = -(∫ u in Ioi (0:ℝ), (delay 0 g u : ℂ) * _) + 3 * (∫ u in Ioi (0:ℝ), (delay c g u : ℂ) * _) -
      2 * (∫ u in Ioi (0:ℝ), (delay (2*c) g u : ℂ) * _)
    rw [laplace_delay g s le_rfl, laplace_delay g s hc, laplace_delay g s (by positivity : 0 ≤ 2*c),
      ← p.laplace s hs]
    have hd : cexp (-s*((2*c : ℝ) : ℂ)) = cexp (-s*c) ^ 2 := by
      rw [pow_two, ← Complex.exp_add, Complex.ofReal_mul]; congr 1; push_cast; ring
    rw [hd]
    simp [symbol]
    ring
  · intro s hs
    exact (symbol_analytic c s).differentiableAt.differentiableWithinAt.mul (p.diff s hs)
  · intro ρ hρ
    obtain ⟨r, hr, hreal, h, hh, hloc⟩ := p.pole ρ hρ
    have hM := symbol_analytic c ρ
    refine ⟨symbol c ρ * r, mul_ne_zero (symbol_strip (p.pos ρ hρ) (strip ρ hρ)) hr, ?_,
      fun s => symbol c s * h s + dslope (symbol c) ρ s * r,
      (hM.mul hh).add ((poleData_dslope hM).mul analyticAt_const), ?_⟩
    · intro hi
      obtain ⟨ha, hb⟩ := symbol_real (p.pos ρ hρ) (strip ρ hρ) hi
      obtain ⟨hx, hy⟩ := hreal hi
      change 0 < (symbol c ρ).re at ha
      change (symbol c ρ).im = 0 at hb
      simp [Complex.mul_re, Complex.mul_im, hb, hy, mul_pos ha hx]
    · filter_upwards [hloc, self_mem_nhdsWithin] with s hloc hs
      have hn : s ≠ ρ := hs
      rw [hloc, dslope_of_ne _ hn, slope_def_field]
      field_simp [sub_ne_zero.mpr hn]
      ring

theorem compactDifference_zeroFree (F : CharFamily) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (hW : WindowHypU (compactDifference (Real.log 2) (gm F)) θ δ) : ZeroFree F θ := by
  obtain ⟨Φ, p⟩ := poleData F
  have strip : ∀ ρ ∈ zeroSet F, ρ.re < 1 := by
    rintro ρ ⟨_, i, hi | hi⟩ <;> by_contra! h
    · exact charFamily_LFunction_ne_zero_of_one_le_re F i ρ h hi
    · exact charFamily_LFunction_ne_zero_of_one_le_re F i _ (by simpa using h) hi
  have hz := landau_window (compactDifference_poleData p strip) hθ hθ1 hδ hW
  intro i s hs hzero
  exact (not_le_of_gt hs) (hz s ⟨by linarith, i, Or.inl hzero⟩)

end ThetaTransfer
