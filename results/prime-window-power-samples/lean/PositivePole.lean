import PrimeWindow

open Complex Filter Set MeasureTheory Topology Deduction
noncomputable section
namespace RiemannReduction

/-- At a regular positive real point, adding c exp(a u) adds a pole with residue c. -/
private theorem add_exp_pole {g : ℝ → ℝ} {F : ℂ → ℂ} {Z : Set ℂ}
    (p : PoleData g F Z) {a c : ℝ} (ha : 0 < a) (ha2 : a < 2) (hc : 0 < c)
    (regular : (a : ℂ) ∉ Z) :
    PoleData (fun u => g u + c*Real.exp (a*u))
      (fun s => F s + (c:ℂ)/(s-a)) (insert (a:ℂ) Z) := by
  obtain ⟨C, growth⟩ := p.growth
  have reg : AnalyticAt ℂ F (a:ℂ) := by
    apply p.diff.analyticAt
    filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds
      (show 0 < (a:ℂ).re from ha), eventually_nhdsWithin_iff.mp (p.iso a ha)] with z hz hz'
    exact ⟨hz, by rcases eq_or_ne z a with rfl | h; exact regular; exact hz' h⟩
  refine ⟨p.meas.add (by fun_prop), ⟨C+c, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have e := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha2.le hu)
    exact (abs_add_le _ _).trans (by
      rw [abs_of_pos (mul_pos hc (Real.exp_pos _)), add_mul]
      exact add_le_add (growth _ hu) (mul_le_mul_of_nonneg_left e hc.le))
  · intro s hs
    have hi : IntegrableOn (fun u : ℝ => (g u : ℂ)*cexp (-s*u)) (Ioi 0) := by
      let b := s.re-2
      have hb : 0 < b := by dsimp [b]; linarith
      apply Integrable.mono' ((iteratedDeriv_laplace_int 0 b hb).const_mul C)
      · apply Measurable.aestronglyMeasurable
        have := p.meas
        fun_prop
      · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
          simpa using iteratedDeriv_laplace_bound g C growth 0 b s (by dsimp [b]; linarith) u hu)
    have neg : ((a:ℂ)-s).re < 0 := by simp; linarith
    have he (u : ℝ) : ((g u + c*Real.exp (a*u) : ℝ) : ℂ)*cexp (-s*u) =
        (g u:ℂ)*cexp (-s*u) + (c:ℂ)*cexp (((a:ℂ)-s)*u) := by
      push_cast
      rw [add_mul, mul_assoc, ← Complex.exp_add]
      congr 3
      ring
    simp_rw [he]
    rw [integral_add hi ((integrableOn_exp_mul_complex_Ioi neg 0).const_mul (c:ℂ)),
      ← p.laplace s hs, integral_const_mul, integral_exp_mul_complex_Ioi neg]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (a:ℂ)-s = -(s-a) by ring]
    simp only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg, one_mul]
  · intro z hz
    rcases hz with h | h
    · simpa [h] using ha
    · exact p.pos z h
  · intro z hz
    have hza : z ≠ (a:ℂ) := fun e => hz.2 (Or.inl e)
    have divdiff : DifferentiableAt ℂ (fun s : ℂ => (c:ℂ)/(s-a)) z := by
      fun_prop (disch := exact sub_ne_zero.mpr hza)
    exact (p.diff z ⟨hz.1, fun h => hz.2 (Or.inr h)⟩).mono
      (fun _ h => ⟨h.1, fun hZ => h.2 (Or.inr hZ)⟩) |>.add
        divdiff.differentiableWithinAt
  · intro z hz
    have avoid : ∀ᶠ w in 𝓝[≠] z, w ≠ (a:ℂ) := by
      rcases eq_or_ne z a with rfl | ne
      · exact self_mem_nhdsWithin
      · exact eventually_ne_nhdsWithin ne
    filter_upwards [p.iso z hz, avoid] with w hw hn
    exact fun h => h.elim hn hw
  · intro z hz
    rcases hz with h | hz
    · subst z
      exact ⟨c, ofReal_ne_zero.mpr hc.ne', fun _ => ⟨hc, rfl⟩, F, reg,
        Eventually.of_forall fun _ => add_comm _ _⟩
    · have hza : z ≠ (a:ℂ) := fun e => regular (e ▸ hz)
      obtain ⟨r, hr, hreal, f, hf, he⟩ := p.pole z hz
      refine ⟨r, hr, hreal, fun s => f s + (c:ℂ)/(s-a),
        hf.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)), ?_⟩
      filter_upwards [he] with s hs
      rw [hs, add_assoc]

private def oneFamily : CharFamily where
  ι := Unit
  N := fun _ => 1
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

/-- Every sufficiently late logarithmic power window contains a point where the prime-power
deficit is greater than -c times the square root, for any fixed positive c. -/
theorem prime_power_recovers {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ A : ℝ, ∀ U ≥ A, ∃ u ∈ Icc U ((1+δ)*U),
      0 < ThetaTransfer.primePowerDeficit u + c*Real.exp (u/2) := by
  obtain ⟨F,p⟩ := poleData oneFamily
  have strip : ∀ z ∈ zeroSet oneFamily, z.re < 1 := by
    rintro z ⟨_,i,hi | hi⟩ <;> by_contra! h
    · exact charFamily_LFunction_ne_zero_of_one_le_re oneFamily i z h hi
    · exact charFamily_LFunction_ne_zero_of_one_le_re oneFamily i _ (by simpa using h) hi
  have good : ((1/2 : ℝ) : ℂ) ∉ zeroSet oneFamily := by
    rintro ⟨_,i,hi⟩
    have h := GlobalTheory.RealZeros.riemannZeta_ne_zero_of_mem_Ioo (1/2) (by norm_num) (by norm_num)
    change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (↑(1/2 : ℝ)) = 0 ∨
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ((starRingEnd ℂ) (↑(1/2 : ℝ))) = 0 at hi
    rw [DirichletCharacter.LFunction_modOne_eq, Complex.conj_ofReal] at hi
    exact hi.elim h h
  have pole := add_exp_pole (ThetaTransfer.compactDifference_poleData p strip)
    (a := 1/2) (by norm_num) (by norm_num) hc good
  by_contra! bad
  have win : WindowHypU (fun u => ThetaTransfer.compactDifference (Real.log 2) (gm oneFamily) u +
      c*Real.exp ((1/2)*u)) (1/4) δ := by
    intro η hη U₀
    obtain ⟨U,hU,h⟩ := bad (max U₀ (2*Real.log 2+1))
    refine ⟨U, (le_max_left _ _).trans hU, fun _ => 0, by simp, fun u hu => ⟨le_rfl, ?_⟩,
      by simpa using (Real.exp_pos (η*U)).le⟩
    have late := ((le_max_right _ _).trans hU).trans hu.1
    have e := ThetaTransfer.compactDifference_eq_primePowerDeficit (u := u) (by linarith)
    change ThetaTransfer.compactDifference (Real.log 2) (gm oneFamily) u = _ at e
    change ThetaTransfer.compactDifference (Real.log 2) (gm oneFamily) u + c*Real.exp ((1/2)*u) ≤ 0
    rw [show (1/2:ℝ)*u = u/2 by ring, e]
    exact h u hu
  have impossible := landau_window pole (by norm_num : (0:ℝ) < 1/4) (by norm_num) hδ win
    (↑(1/2 : ℝ)) (Set.mem_insert _ _)
  norm_num at impossible

#print axioms prime_power_recovers
end RiemannReduction
