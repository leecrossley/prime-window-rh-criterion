import VShortShift
import PrimeWindow
import Reflection

open Filter MeasureTheory
namespace RiemannReduction.DivisorBand
noncomputable section

/-- Choose a near-rightmost zero and a strip bound simultaneously, retaining
room both for the height of a normalized excursion and for many base indices. -/
theorem tenth_exponents (failure : ¬RiemannHypothesis) {γ : ℝ} (g1 : γ<1) :
    ∃ (h θ b C : ℝ) (ρ : ℂ), 0<h ∧ h≤1/200 ∧ γ/20<1/20-2*h ∧
      1/2+4*h<θ ∧ θ<1 ∧ θ<ρ.re ∧ riemannZeta ρ=0 ∧ 0≤b ∧ b≤2 ∧
      0<C ∧ (∀ t : ℝ, 2≤t → |ZetaWindow.psiError t|≤C*t^b) ∧
      (1-h)+b-2<θ-1 ∧ 2*γ≤(40-h)*(1/20-2*h) := by
  let S : Set ℝ := {r | ∃ z : ℂ, ZetaWindow.stripZero z ∧ z.re=r}
  have off : ¬(∀ z : ℂ, 1/2<z.re → z≠1 → riemannZeta z≠0) :=
    fun good => failure (RiemannReduction.rh_of_right good)
  push Not at off
  obtain ⟨z,zr,_,zz⟩ := off
  have mem : z.re ∈ S := ⟨z,⟨by linarith,lt_of_not_ge (fun hr => riemannZeta_ne_zero_of_one_le_re hr zz),zz⟩,rfl⟩
  have bounded : BddAbove S := ⟨1,fun _ ⟨_,hw,eq⟩ => eq ▸ hw.2.1.le⟩
  let σ := sSup S
  have bot : 1/2<σ := zr.trans_le (le_csSup bounded mem)
  have top : σ≤1 := csSup_le ⟨_,mem⟩ (fun _ ⟨_,hw,eq⟩ => eq ▸ hw.2.1.le)
  let h := min ((σ-1/2)/20) (min ((1-γ)/100) (1/200))
  have hp : 0<h := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have left : h≤(σ-1/2)/20 := min_le_left _ _
  have right : h≤(1-γ)/100 := (min_le_right _ _).trans (min_le_left _ _)
  have cap : h≤1/200 := (min_le_right _ _).trans (min_le_right _ _)
  let θ := σ-h/4
  have existsZero : ∃ w : ℂ, ZetaWindow.stripZero w ∧ θ<w.re := by
    by_contra! none
    have : σ≤θ := csSup_le ⟨_,mem⟩ (fun _ ⟨w,hw,eq⟩ => eq ▸ none w hw)
    dsimp [θ] at this; linarith
  obtain ⟨ρ,hρ,large⟩ := existsZero
  obtain ⟨C,cp,psi⟩ := ZetaWindow.psi_error_of_strip_bound (by linarith : 0≤σ) (show 0<h/4 by linarith)
    (fun w hw => le_csSup bounded (show w.re ∈ S from ⟨w,hw,rfl⟩))
  refine ⟨h,θ,σ+h/4,C,ρ,hp,cap,by linarith,?_,?_,large,hρ.2.2,by linarith,by linarith,cp,psi,?_,by nlinarith [sq_nonneg h]⟩ <;>
    dsimp [θ] <;> linarith

private lemma exp_margin (u : ℝ) : D (Real.exp u) = ThetaTransfer.primePowerDeficit u := by
  unfold D c ThetaTransfer.primePowerDeficit; ring

private lemma point_majorant {f : ℝ → ℝ} {θ δ : ℝ} (dp : 0<δ)
    (bounds : ∀ U₀ : ℝ, ∃ U≥U₀, ∀ u ∈ Set.Icc U ((1+δ)*U), f u≤Real.exp (θ*u)) :
    Deduction.WindowHypU f θ δ := by
  intro η ep U₀
  obtain ⟨X,cap⟩ := Deduction.windowHyp_of_rpow_eventually δ η dp.le ep
  obtain ⟨U,late,hU⟩ := bounds (max U₀ (max 0 (Real.log X)))
  have after := (le_max_right U₀ _).trans late
  have up := (le_max_left 0 (Real.log X)).trans after
  have xe : X ≤ Real.exp U := by
    by_cases xp : 0<X
    · exact (Real.log_le_iff_le_exp xp).mp ((le_max_right 0 _).trans after)
    · linarith [Real.exp_pos U]
  have mass := (cap (Real.exp U) xe).2
  rw [Real.log_exp,←Real.exp_mul] at mass
  have unit : (fun u : ℝ => Real.exp (θ*u)*Real.exp (-θ*u)) = fun _ => (1:ℝ) := by
    funext u; rw [←Real.exp_add,show θ*u+-θ*u=0 by ring,Real.exp_zero]
  refine ⟨U,(le_max_left _ _).trans late,fun u => Real.exp (θ*u),?_,fun u hu => ⟨(Real.exp_pos _).le,hU u hu⟩,?_⟩
  · rw [unit]; exact continuousOn_const.integrableOn_Icc
  · rw [unit,setIntegral_const,Real.volume_real_Icc_of_le (by nlinarith : U≤(1+δ)*U)]
    simp only [smul_eq_mul,mul_one]
    nlinarith [show Real.exp (U*η)=Real.exp (η*U) by rw [mul_comm]]

/-- Both signs have excursions on every sufficiently late logarithmic window
of any prescribed positive relative width. -/
theorem tenth_signed_peaks {ρ : ℂ} (zero : riemannZeta ρ=0) {θ : ℝ}
    (tp : 0<θ) (t1 : θ<1) (right : θ<ρ.re) (s : ℝ) (sign : s=1 ∨ s= -1) {δ : ℝ} (dp : 0<δ) :
    ∃ U₀ : ℝ, ∀ U≥U₀, ∃ u ∈ Set.Icc U ((1+δ)*U), (Real.exp u)^θ < s*D (Real.exp u) := by
  have eq (u : ℝ) : (Real.exp u)^θ=Real.exp (θ*u) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm]
  rcases sign with rfl | rfl
  · simpa only [one_mul,exp_margin,eq] using ThetaTransfer.deficit_on_every_late_window zero tp t1 dp right
  · by_contra! bounds
    apply ThetaTransfer.zeta_zeroFree_of_surplus tp t1 dp _ ρ right zero
    apply point_majorant dp
    simpa only [eq,exp_margin,neg_one_mul] using bounds

/-- Near-extremal excursions retain a power advantage over the square-root
scale all the way across the short interval. -/
theorem tenth_peak_height {b h θ C s : ℝ} (sign : s=1 ∨ s= -1) (hp : 0<h)
    (height : 1/2+4*h<θ) (b0 : 0≤b) (b2 : b≤2) (cp : 0<C)
    (psi : ∀ t : ℝ, 2≤t → |ZetaWindow.psiError t|≤C*t^b) (gap : (1-h)+b-2<θ-1) :
    ∀ᶠ x : ℝ in atTop, x^θ < s*D x → ∀ y : ℝ, x≤y → y≤x+x^(1-h) →
      x^(4*h) < s*D y/Real.sqrt y := by
  have grow := (tendsto_rpow_atTop (show 0<θ-1/2-4*h by linarith)).eventually_ge_atTop 2
  have drift := relative_short_shift b0 b2 cp psi (show 1-h≤1 by linarith) gap (show 0<(1/2:ℝ) by norm_num)
  filter_upwards [eventually_gt_atTop (0:ℝ),grow,drift] with x xp big near
  intro peak y xy last
  have yp := xp.trans_le xy
  have top : x^(θ-1)<s*D x/x := by
    rw [Real.rpow_sub xp,Real.rpow_one]; exact div_lt_div_of_pos_right peak xp
  have close := abs_le.mp (near y xy last)
  have normed : (1/2)*x^(θ-1) < s*D y/y := by
    rcases sign with rfl | rfl <;> simp only [one_mul,neg_one_mul,neg_div] at top ⊢ <;> linarith [close.1,close.2]
  have amp : 2*x^(4*h) ≤ x^(θ-1)*Real.sqrt x := by
    have bound := mul_le_mul_of_nonneg_right big (Real.rpow_nonneg xp.le (4*h))
    rw [←Real.rpow_add xp,show θ-1/2-4*h+4*h=θ-1+1/2 by ring] at bound
    rw [Real.sqrt_eq_rpow,←Real.rpow_add xp]
    exact bound
  have root := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt xy) (Real.rpow_nonneg xp.le (θ-1))
  have mult := mul_lt_mul_of_pos_right normed (Real.sqrt_pos.mpr yp)
  have id : (s*D y/y)*Real.sqrt y=s*D y/Real.sqrt y := by
    field_simp [yp.ne',ne_of_gt (Real.sqrt_pos.mpr yp)]
    rw [Real.sq_sqrt yp.le]
  linarith

end
end RiemannReduction.DivisorBand
