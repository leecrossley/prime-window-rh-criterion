import FourthPowerSpacing
import TenthPowerSpectrum

open Finset Filter
namespace RiemannReduction.DivisorBand
noncomputable section

/-- A narrow logarithmic window places the excursion close enough to the
upper end of the base block to control its ordinary, unweighted mean. -/
private lemma peak_near_top {h : ℝ} (hp : 0<h) (hs : h≤1/200) {P : ℝ → Prop}
    (peaks : ∀ δ : ℝ, 0<δ → ∃ U₀ : ℝ, ∀ U≥U₀, ∃ u ∈ Set.Icc U ((1+δ)*U), P (Real.exp u)) :
    ∀ᶠ a : ℕ in atTop, ∃ x : ℝ, (a:ℝ)^(8-h) ≤ x ∧ x ≤ (a:ℝ)^(8-h/2) ∧ P x := by
  let δ := (h/2)/(8-h)
  have pos : 0<8-h := by linarith
  obtain ⟨U₀,hits⟩ := peaks δ (div_pos (by linarith) pos)
  have grow := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop pos
  filter_upwards [grow.eventually_ge_atTop U₀,eventually_ge_atTop (1:ℕ)] with a large one
  have ap : 0<(a:ℝ) := by exact_mod_cast one
  obtain ⟨u,hu,peak⟩ := hits ((8-h)*Real.log a) large
  have id : (1+δ)*(8-h)=8-h/2 := by dsimp [δ]; field_simp; ring
  refine ⟨Real.exp u,?_,?_,peak⟩
  · rw [Real.rpow_def_of_pos ap,mul_comm]; exact Real.exp_le_exp.mpr hu.1
  · rw [Real.rpow_def_of_pos ap,mul_comm]
    apply Real.exp_le_exp.mpr
    simpa only [←mul_assoc,id] using hu.2

/-- If RH fails, a whole consecutive run of fourth-power samples has
both high normalized values and enough total weight to affect the entire
base block. The exponent h is independent of the block and of the sign. -/
theorem fourth_sample_excursions (failure : ¬RiemannHypothesis)  :
    ∃ h > (0:ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ᶠ a : ℕ in atTop,
      ∃ (N w : ℕ) (H : ℝ), a≤N ∧ N+w≤a^2 ∧ 0≤H ∧
        (a:ℝ)^(2+h) ≤ ((w:ℝ)+1)*H ∧ ∀ n ∈ Icc N (N+w), H < s*fourthMargin n := by
  obtain ⟨h,θ,b,C,ρ,hp,hs,_,th,t1,right,zero,b0,b2,cp,psi,gap,_⟩ := tenth_exponents (γ:=1/2) failure (by norm_num)
  refine ⟨h,hp,fun s sign => ?_⟩
  obtain ⟨X₀,persist⟩ := eventually_atTop.mp (tenth_peak_height sign hp th b0 b2 cp psi gap)
  obtain ⟨X₁,fit⟩ := eventually_atTop.mp (fourth_power_interval hp (by linarith))
  have tp : 0<θ := by linarith
  have positions := peak_near_top (P:=fun x => x^θ<s*D x) hp hs
    (fun δ dp => tenth_signed_peaks zero tp t1 right s sign dp)
  have grow := (tendsto_rpow_atTop (show 0<h/2 by linarith)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [positions,grow.eventually_ge_atTop 2,
    eventually_ge_atTop (max 2 (max ⌈X₀⌉₊ ⌈X₁⌉₊))] with a hit large late
  obtain ⟨x,lo,hi,peak⟩ := hit
  have ar : (2:ℝ) ≤ a := by exact_mod_cast (le_max_left _ _).trans late
  have ap : 0 < (a:ℝ) := by linarith
  have one : 1 ≤ (a:ℝ) := by linarith
  have ax : (a:ℝ)^4 ≤ x := by
    rw [←Real.rpow_natCast]; exact (Real.rpow_le_rpow_of_exponent_le one (by norm_num; linarith)).trans lo
  have aa : (a:ℝ) ≤ x := by
    have le := Real.rpow_le_rpow_of_exponent_le one (show (1:ℝ)≤8-h by linarith)
    rw [Real.rpow_one] at le
    exact le.trans lo
  have xp : 0<x := ap.trans_le aa
  have lateX {v : ℝ} (cap : ⌈v⌉₊≤a) : v≤x :=
    (Nat.le_ceil v).trans ((Nat.cast_le.mpr cap).trans aa)
  let N := ⌈x^(1/4:ℝ)⌉₊
  let w := ⌊x^(1/4-2*h)⌋₊
  obtain ⟨left,last⟩ := fit x (lateX (v:=X₁) (by omega))
  change x ≤ (N:ℝ)^4 at left
  change (↑(N+w):ℝ)^4 ≤ x+x^(1-h) at last
  have idx : a≤N := by exact_mod_cast le_of_pow_le_pow_left₀ (n:=4) (by decide) (Nat.cast_nonneg N) (ax.trans left)
  have small : x^(1-h) ≤ x := (Real.rpow_le_rpow_of_exponent_le (one.trans aa) (by linarith)).trans_eq (Real.rpow_one _)
  have top : (N+w)≤a^2 := by
    have cap : 2*x ≤ (a:ℝ)^8 := by
      have product := mul_le_mul (show (2:ℝ)≤(a:ℝ)^(h/2) from large) hi xp.le (by positivity)
      rw [←Real.rpow_add ap,show h/2+(8-h/2)=8 by ring] at product
      simpa using product
    have bound : (↑(N+w):ℝ)^4 ≤ ((a:ℝ)^2)^4 := by
      rw [←pow_mul]; exact last.trans ((show x+x^(1-h) ≤ 2*x by linarith).trans cap)
    exact_mod_cast le_of_pow_le_pow_left₀ (n:=4) (by decide) (sq_nonneg (a:ℝ)) bound
  let H := x^(4*h)
  have size : (a:ℝ)^(2+h) ≤ ((w:ℝ)+1)*H := by
    have ex : 2+h ≤ (8-h)*(1/4+2*h) := by
      nlinarith [mul_le_mul_of_nonneg_right hs hp.le]
    calc _ ≤ (a:ℝ)^((8-h)*(1/4+2*h)) := Real.rpow_le_rpow_of_exponent_le one ex
         _ = ((a:ℝ)^(8-h))^(1/4+2*h) := Real.rpow_mul ap.le _ _
         _ ≤ x^(1/4+2*h) := Real.rpow_le_rpow (Real.rpow_nonneg ap.le _) lo (by linarith)
         _ = x^(1/4-2*h)*H := by dsimp [H]; rw [←Real.rpow_add xp]; congr 1; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one _).le (Real.rpow_nonneg xp.le _)
  refine ⟨N,w,H,idx,top,Real.rpow_nonneg xp.le _,size,?_⟩
  intro n hn
  have ny : x ≤ (n:ℝ)^4 := left.trans (pow_le_pow_left₀ (Nat.cast_nonneg N) (Nat.cast_le.mpr (mem_Icc.mp hn).1) 4)
  have endpt := (pow_le_pow_left₀ (Nat.cast_nonneg n) (Nat.cast_le.mpr (mem_Icc.mp hn).2) 4).trans last
  have atBase := persist x (lateX (v:=X₀) (by omega)) peak _ ny endpt
  have square : (n:ℝ)^4=((n:ℝ)^2)^2 := by rw [←pow_mul]
  rw [show Real.sqrt ((n:ℝ)^4)=(n:ℝ)^2 by rw [square,Real.sqrt_sq (by positivity)]] at atBase
  simpa only [fourthMargin,mul_div_assoc] using atBase

end
end RiemannReduction.DivisorBand
