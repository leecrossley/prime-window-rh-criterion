import DivisorSieveRows
import PacketTheta

open Finset Filter RiemannReduction.DivisorBand
namespace RiemannReduction.DivisorSieve
noncomputable section

private lemma theta_box {u v : ℕ} (h : u≤v) :
    Chebyshev.theta u + ∑ p ∈ box u v, Real.log p = Chebyshev.theta v := by
  simp only [Chebyshev.theta,box,Nat.floor_natCast,sum_filter]
  exact sum_Ioc_consecutive _ (Nat.zero_le _) h

private theorem log_grows : Tendsto (fun s : ℕ => packetLog s) atTop atTop :=
  tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))

/-- The ordinary prime number theorem supplies uniformly many prime factors
from each of the four fixed intervals. -/
theorem box_supply : ∀ᶠ s : ℕ in atTop, ∀ a b : ℕ, 1≤a → a<b → b≤40 →
    (s:ℝ) ≤ 32*packetLog s*((box (a*s) (b*s)).card:ℝ) := by
  obtain ⟨H,hH,approx⟩ := packetTheta_decay 1
  filter_upwards [eventually_ge_atTop (1:ℕ),log_grows.eventually_ge_atTop (160*H)] with s hs big
  intro a b ha hab hb
  have sp : 0 < (s:ℝ) := by exact_mod_cast hs
  have hs' : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have L := packetLog_ge hs'
  have err (u : ℕ) (h1 : 1≤u) (h2 : u≤40) :
      |Chebyshev.theta (u*s)-(u*s:ℕ)| ≤ (s:ℝ)/4 := by
    have uu : (1:ℝ)≤u := by exact_mod_cast h1
    have u40 : (u:ℝ)≤40 := by exact_mod_cast h2
    have le : (s:ℝ)≤(u:ℝ)*s := by nlinarith only [mul_le_mul_of_nonneg_right uu sp.le]
    have h := approx ((u:ℝ)*s) (hs'.trans le)
    rw [pow_one] at h
    have gt := big.trans (packetLog_mono sp le)
    have prod := mul_le_mul_of_nonneg_left gt (abs_nonneg (Chebyshev.theta ((u:ℝ)*s)-(u:ℝ)*s))
    have ub := mul_le_mul_of_nonneg_right u40 sp.le
    have scaled : 160*H*|Chebyshev.theta ((u:ℝ)*s)-(u:ℝ)*s| ≤ 40*H*s := by
      nlinarith only [h,prod,mul_le_mul_of_nonneg_left ub (by linarith only [hH] : 0≤H)]
    push_cast
    apply le_of_mul_le_mul_left (a:=H) _ (by linarith only [hH])
    linarith only [scaled]
  have ea := (abs_le.mp (err a ha (by omega))).2
  have eb := (abs_le.mp (err b (by omega) hb)).1
  have eq := theta_box (Nat.mul_le_mul_right s hab.le)
  have ab' : (a:ℝ)+1≤b := by exact_mod_cast hab
  have diff := mul_le_mul_of_nonneg_right ab' sp.le
  push_cast at eq ea eb
  have mass : (s:ℝ)/2 ≤ ∑ p ∈ box (a*s) (b*s), Real.log p := by
    linarith only [eq,ea,eb,diff]
  have cap (p : ℕ) (hp : p∈box (a*s) (b*s)) : Real.log p ≤ 16*packetLog s := by
    obtain ⟨mem,prime⟩ := mem_filter.mp hp
    have le : (p:ℝ) ≤ (b:ℝ)*s := by exact_mod_cast (mem_Ioc.mp mem).2
    have b1 : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
    have b40 : (b:ℝ)≤40 := by exact_mod_cast hb
    have h := Real.log_le_log (by exact_mod_cast prime.pos) le
    rw [Real.log_mul b1.ne' sp.ne'] at h
    unfold packetLog
    linarith only [h,Real.log_le_self b1.le,b40,Real.log_nonneg hs']
  have upper := sum_le_sum (s:=box (a*s) (b*s)) (fun p hp => cap p hp)
  simp only [sum_const,nsmul_eq_mul] at upper
  linarith only [mass,upper]

theorem reserve_growth : ∀ᶠ s : ℕ in atTop,
    ∀ v : ℕ → ℝ, Admissible (25*s^2) v →
      (s:ℝ)^3 ≤ (32*128^3) * (packetLog s)^3 * compositeMass v (400*s^3) := by
  obtain ⟨G,gp,logRoot⟩ := log_power_sqrt 1
  have square_grows : Tendsto (fun s : ℕ => s^2) atTop atTop :=
    tendsto_pow_atTop (by decide)
  have root_grows := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ),box_supply,square_grows.eventually box_supply,
    root_grows.eventually_ge_atTop (128*G)] with s hs supply supplyQ root
  intro v hv
  change 128*G ≤ Real.sqrt (s:ℝ) at root
  let L := packetLog (s:ℝ)
  let M := ⌊(s:ℝ)/(64*L)⌋₊
  have hs' : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have lg : 4≤L := packetLog_ge hs'
  have lp : 0<64*L := by linarith
  have g := logRoot s hs'
  rw [pow_one] at g
  have big : 128*L ≤ (s:ℝ) := by
    have h := mul_le_mul_of_nonneg_right root (Real.sqrt_nonneg (s:ℝ))
    dsimp [L]
    nlinarith only [h,g,Real.mul_self_sqrt (Nat.cast_nonneg (α:=ℝ) s)]
  have floorL : (M:ℝ)*(64*L) ≤ s := (le_div_iff₀ lp).mp (Nat.floor_le (by positivity))
  have floorU : (s:ℝ)<((M:ℝ)+1)*(64*L) := (div_lt_iff₀ lp).mp (Nat.lt_floor_add_one _)
  have m1 : 1≤M := Nat.le_floor (by
    push_cast
    exact (one_le_div lp).2 (by linarith only [big,lg]))
  have m1' : (1:ℝ)≤M := by exact_mod_cast m1
  have sU : (s:ℝ) ≤ 128*L*M := by
    nlinarith only [floorU,mul_le_mul_of_nonneg_right m1' lp.le]
  have make {a b : ℕ} (h1 : 1≤a) (h2 : a<b) (h3 : b≤40) :
      Nonempty (Fin M ↪ ↥(box (a*s) (b*s))) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_fin,Fintype.card_coe]
    have h := supply a b h1 h2 h3
    have le : (M:ℝ) ≤ (box (a*s) (b*s)).card := by
      apply le_of_mul_le_mul_left (a:=64*L) _ lp
      nlinarith only [floorL,h,mul_nonneg (by linarith : 0≤L) (Nat.cast_nonneg (α:=ℝ) (box (a*s) (b*s)).card),
        show L=packetLog s from rfl]
    exact_mod_cast le
  obtain ⟨P⟩ := make (a:=5) (b:=6) (by decide) (by decide) (by decide)
  obtain ⟨S⟩ := make (a:=6) (b:=7) (by decide) (by decide) (by decide)
  obtain ⟨H⟩ := make (a:=7) (b:=8) (by decide) (by decide) (by decide)
  have cap := supplyQ 32 40 (by decide) (by decide) (by decide)
  have lq : packetLog ((s^2:ℕ):ℝ) ≤ 2*L := by
    simp only [Nat.cast_pow,packetLog,L,Real.log_pow,Nat.cast_ofNat]; linarith
  have qs : (M:ℝ)^2 ≤ (box (32*s^2) (40*s^2)).card := by
    have sc := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) lp.le) floorL 2
    let C := (box (32*s^2) (40*s^2)).card
    have up := mul_le_mul_of_nonneg_right lq (Nat.cast_nonneg (α:=ℝ) C)
    have one : 1 ≤ 64*L := by linarith
    have mm : (M:ℝ)^2*(64*L) ≤ ((M:ℝ)*(64*L))^2 := by
      nlinarith only [mul_le_mul_of_nonneg_left one
        (mul_nonneg (sq_nonneg (M:ℝ)) lp.le)]
    apply le_of_mul_le_mul_left (a:=64*L) _ lp
    dsimp only [C] at up
    simp only [Nat.cast_pow] at cap up
    nlinarith only [mm,sc,cap,up]
  obtain ⟨Q⟩ : Nonempty ((Fin M × Fin M) ↪ ↥(box (32*s^2) (40*s^2))) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,←sq]
    exact_mod_cast qs
  have rows := composite_rows hs P S H Q hv
  have cub := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) s) sU 3
  have weighted := mul_le_mul_of_nonneg_left rows
    (pow_nonneg (show 0≤128*L by linarith) 3)
  change (s:ℝ)^3 ≤ (32*128^3)*L^3*_
  linarith only [cub,weighted]

end
end RiemannReduction.DivisorSieve
