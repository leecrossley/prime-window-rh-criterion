import VShortShift

open Filter Finset
namespace RiemannReduction.DivisorBand
noncomputable section

/-- A consecutive set of integer bases whose fourth powers lie just to
the right of x. The term lost to rounding is included in the endpoint bound. -/
theorem fourth_power_interval {h : ℝ} (hp : 0<h) (small : 2*h<1/4) :
    ∀ᶠ x : ℝ in atTop, let N := ⌈x^(1/4:ℝ)⌉₊
      let w := ⌊x^(1/4-2*h)⌋₊
      x ≤ (N:ℝ)^4 ∧ (↑(N+w):ℝ)^4 ≤ x+x^(1-h) := by
  have grow := (tendsto_rpow_atTop hp).eventually_ge_atTop (8*3^(3:ℕ))
  filter_upwards [eventually_ge_atTop (1:ℝ),grow] with x one enough
  have xp : 0<x := by linarith
  let s := x^(1/4:ℝ)
  let t := x^(1/4-2*h)
  let N := ⌈s⌉₊
  let w := ⌊t⌋₊
  have s1 : 1 ≤ s := Real.one_le_rpow one (by norm_num)
  have t1 : 1 ≤ t := Real.one_le_rpow one (by linarith)
  have ts : t ≤ s := Real.rpow_le_rpow_of_exponent_le one (by linarith)
  have base : s^4=x := by
    dsimp [s]; rw [←Real.rpow_natCast,←Real.rpow_mul xp.le]; norm_num
  have product : s^3*t = x^(1-2*h) := by
    dsimp [s,t]; rw [←Real.rpow_natCast,←Real.rpow_mul xp.le,←Real.rpow_add xp]; congr 1; norm_num; ring
  have room : (s+2*t)^4-s^4 ≤ (8*3^3)*(s^3*t) := by
    have diff := abs_pow_sub_pow_le (s+2*t) s 4
    rw [abs_of_nonneg (by linarith : 0 ≤ s+2*t),abs_of_nonneg (by linarith : 0 ≤ s),
      max_eq_left (by linarith : s ≤ s+2*t),add_sub_cancel_left,
      abs_of_nonneg (by linarith : 0≤2*t)] at diff
    have cap := pow_le_pow_left₀ (by linarith : 0 ≤ s+2*t) (show s+2*t ≤ 3*s by linarith) 3
    have gain := mul_le_mul_of_nonneg_left cap (show 0≤2*t*4 by linarith)
    norm_num only [Nat.reduceSub,Nat.cast_ofNat] at diff
    rw [mul_pow] at gain
    linarith [le_abs_self ((s+2*t)^4-s^4)]
  have allowance : (8*3^3)*(s^3*t) ≤ x^(1-h) := by
    rw [product]
    calc _ ≤ x^h*x^(1-2*h) := mul_le_mul_of_nonneg_right enough (Real.rpow_nonneg xp.le _)
         _ = _ := by rw [←Real.rpow_add xp]; congr 1; ring
  have lo : s ≤ N := Nat.le_ceil _
  have hi : (↑(N+w):ℝ) ≤ s+2*t := by
    push_cast
    linarith [(Nat.ceil_lt_add_one (by linarith : 0 ≤ s)).le,Nat.floor_le (by linarith : 0≤t)]
  exact ⟨base.ge.trans (pow_le_pow_left₀ (by linarith) lo 4),
    (pow_le_pow_left₀ (Nat.cast_nonneg (N+w)) hi 4).trans (by linarith)⟩

/-- Positive normalized margin is favorable for the original question. -/
def fourthMargin (n : ℕ) : ℝ := D ((n:ℝ)^4)/(n:ℝ)^2


end
end RiemannReduction.DivisorBand
