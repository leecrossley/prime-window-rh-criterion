import PrimeWindow
import Reflection

open Set Complex
namespace PowerSamples

/-- A left shift in log scale gains half a power of its length in each zero term. -/
theorem term_increment (z : ℂ) (left : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ 2 * Real.sqrt ‖z‖ := by
  have h := Real.sq_sqrt (norm_nonneg z)
  by_cases small : ‖z‖ ≤ 1
  · have rs : Real.sqrt ‖z‖ ≤ 1 := (Real.sqrt_le_one).mpr small
    have pos := Real.sqrt_nonneg ‖z‖
    have prod := mul_nonneg pos (sub_nonneg.mpr rs)
    nlinarith [Complex.norm_exp_sub_one_le small]
  · have ht : 1 ≤ Real.sqrt ‖z‖ := by
      simpa using Real.sqrt_le_sqrt (le_of_not_ge small)
    have hn : ‖Complex.exp z‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr left
    have ht' := norm_sub_le (Complex.exp z) (1 : ℂ)
    rw [norm_one] at ht'
    linarith

/-- A fixed improvement below the supremum rules out a supremum above one half.
No zero at the supremum is needed. -/
theorem right_edge {B g : ℝ} (upto : B ≤ 1) (gain : 0 < g)
    (excluded : ∀ θ : ℝ, 1/2 < θ → B-g < θ → θ < 1 → B ≤ θ) : B ≤ 1/2 := by
  by_contra! high
  let m := max (1/2 : ℝ) (B-g)
  have hm : m < B := max_lt high (by linarith)
  have a : (1/2 : ℝ) ≤ m := le_max_left _ _
  have b : B-g ≤ m := le_max_right _ _
  have := excluded ((m+B)/2) (by linarith) (by linarith) (by linarith)
  linarith

/-- A polynomial slack absorbs the constant in the interpolated one-sided windows. -/
theorem window_excludes {α θ δ C : ℝ} (slack : α < θ) (positive : 0 < θ)
    (strip : θ < 1) (width : 0 < δ)
    (windows : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1+δ)*U),
      -ThetaTransfer.primePowerDeficit u ≤ C * Real.exp (α*u)) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  apply ThetaTransfer.zeta_zeroFree_of_surplus positive strip width
  apply ThetaTransfer.window_of_point_bounds width
  intro U₀
  let K := max 1 C
  have hk : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨U, hu, h⟩ := windows (max U₀ (Real.log K/(θ-α)))
  refine ⟨U, (le_max_left _ _).trans hu, fun u member => ?_⟩
  have lo := (le_max_right U₀ (Real.log K/(θ-α))).trans (hu.trans member.1)
  have hev : K ≤ Real.exp ((θ-α)*u) := (Real.log_le_iff_le_exp hk).mp
    (by nlinarith [(div_le_iff₀ (sub_pos.mpr slack)).mp lo])
  calc -ThetaTransfer.primePowerDeficit u ≤ C * Real.exp (α*u) := h u member
    _ ≤ Real.exp ((θ-α)*u)*Real.exp (α*u) :=
      mul_le_mul_of_nonneg_right ((le_max_right 1 C).trans hev) (Real.exp_pos _).le
    _ = Real.exp (θ*u) := by rw [← Real.exp_add]; congr 1; ring

/-- The final implication after the arithmetic sampling estimate in the paper. -/
theorem rh_of_interpolated_windows {B g δ C : ℝ} (upto : B ≤ 1) (gain : 0 < g)
    (width : 0 < δ) (upper : ∀ z : ℂ, riemannZeta z = 0 → z.re ≤ B)
    (edge : ∀ t : ℝ, t < B → ∃ z : ℂ, riemannZeta z = 0 ∧ t < z.re)
    (windows : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1+δ)*U),
      -ThetaTransfer.primePowerDeficit u ≤ C * Real.exp (max (1/2) (B-g)*u)) :
    RiemannHypothesis := by
  have cut : B ≤ 1/2 := by
    apply right_edge upto gain
    intro t ht hb ht1
    by_contra! h
    obtain ⟨z, hz, right⟩ := edge t h
    exact window_excludes (max_lt ht hb) (by linarith) ht1 width windows z right hz
  apply RiemannReduction.rh_of_right
  intro z right _ zero
  exact (not_lt_of_ge ((upper z zero).trans cut)) right

/-- The logarithm of the scale n^k. The proof only uses n ≥ 1. -/
noncomputable def scale (k n : ℕ) : ℝ := (k : ℝ) * Real.log n

/-- Transfer from actual power samples, given the analytic increment estimate
proved in the paper. The natural block may vary with the lower cutoff. -/
theorem rh_of_power_samples_of_increment {k n₀ : ℕ} (hk : 1 ≤ k)
    {B g C L : ℝ} (upto : B ≤ 1) (gain : 0 < g) (hc : 0 ≤ C) (hL : 0 ≤ L)
    (upper : ∀ z : ℂ, riemannZeta z = 0 → z.re ≤ B)
    (edge : ∀ t : ℝ, t < B → ∃ z : ℂ, riemannZeta z = 0 ∧ t < z.re)
    (increment : ∀ n ≥ n₀, ∀ u ∈ Icc (scale k n) (scale k (n+1)),
      -ThetaTransfer.primePowerDeficit u ≤ -ThetaTransfer.primePowerDeficit (scale k n) +
        L*(Real.exp ((B-g)*u)+1))
    (samples : ∀ m : ℕ, ∃ K ≥ m, ∀ n ∈ Finset.Icc K (K*K),
      -ThetaTransfer.primePowerDeficit (scale k n) ≤ C*Real.exp (scale k n/2)) :
    RiemannHypothesis := by
  apply rh_of_interpolated_windows (B := B) (g := g) (δ := 1) (C := C+2*L)
    upto gain (by norm_num) upper edge
  intro U₀
  obtain ⟨K, cap, tested⟩ := samples (max n₀ (max 1 ⌈Real.exp U₀⌉₊))
  have bk := (le_max_right n₀ _).trans cap
  have oneK : 1 ≤ K := (le_max_left _ _).trans bk
  have kp : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have kk : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have pos : (0 : ℝ) < k := by linarith
  have lg := Real.log_nonneg (show 1 ≤ (K:ℝ) by exact_mod_cast oneK)
  have L0 : U₀ ≤ Real.log K := (Real.le_log_iff_exp_le kp).mpr
    ((Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans bk)))
  have nonneg : 0 ≤ scale k K := mul_nonneg pos.le lg
  refine ⟨scale k K, L0.trans (le_mul_of_one_le_left lg kk), fun u hu => ?_⟩
  let n := ⌊Real.exp (u/k)⌋₊
  have low : Real.log K ≤ u/k := (le_div_iff₀ pos).mpr (by
    simpa [scale, mul_comm] using hu.1)
  have high : u/k ≤ Real.log (↑(K*K : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul kp.ne' kp.ne']
    apply (div_le_iff₀ pos).mpr
    dsimp [scale] at hu
    linarith [hu.2]
  have nlo : K ≤ n := Nat.le_floor ((Real.log_le_iff_le_exp kp).mp low)
  have nhi : n ≤ K*K := Nat.cast_le.mp ((Nat.floor_le (Real.exp_pos _).le).trans
    ((Real.le_log_iff_exp_le (by positivity)).mp high))
  have np : (0:ℝ) < n := kp.trans_le (Nat.cast_le.mpr nlo)
  have sl : scale k n ≤ u := by
    have t := (Real.log_le_iff_le_exp np).mpr (Nat.floor_le (Real.exp_pos _).le)
    simpa [scale, mul_comm] using (le_div_iff₀ pos).mp t
  have sr : u ≤ scale k (n+1) := by
    have t : Real.exp (u/k) ≤ (↑(n+1 : ℕ):ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    have tl := (Real.le_log_iff_exp_le (by positivity)).mpr t
    simpa [scale, mul_comm] using (div_le_iff₀ pos).mp tl
  have h := increment n (((le_max_left _ _).trans cap).trans nlo) u ⟨sl,sr⟩
  have s := tested n (Finset.mem_Icc.mpr ⟨nlo,nhi⟩)
  let α : ℝ := max (1/2) (B-g)
  have u0 := nonneg.trans hu.1
  have e₁ : Real.exp (scale k n/2) ≤ Real.exp (α*u) := by
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right (le_max_left (1/2 : ℝ) (B-g)) u0]
  have e₂ : Real.exp ((B-g)*u) ≤ Real.exp (α*u) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) u0)
  have e₃ : 1 ≤ Real.exp (α*u) := Real.one_le_exp (mul_nonneg
    ((by norm_num : (0:ℝ) ≤ 1/2).trans (le_max_left _ _)) u0)
  change _ ≤ (C+2*L)*Real.exp (α*u)
  linarith [mul_le_mul_of_nonneg_left e₁ hc, mul_le_mul_of_nonneg_left e₂ hL,
    mul_le_mul_of_nonneg_left e₃ hL]

end PowerSamples
