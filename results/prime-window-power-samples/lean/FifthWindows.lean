import PrimeWindow
import PrimeBandWeights
import Reflection
import SquareSampling
import TurningPoints
import MarginVariation
import Mathlib.NumberTheory.Bertrand

open Filter Set MeasureTheory
namespace RiemannReduction.PrimeGrid

/-- The requested bound on the two endpoints and every doubled prime in arbitrarily late blocks. -/
def FifthBlocks : Prop :=
  ∀ m : ℕ, ∃ N ≥ m, ∀ j ∈ Finset.Icc N (N*N),
    (j = N ∨ j = N*N ∨ ∃ p : ℕ, p.Prime ∧ j = 2*p) →
      -(Real.sqrt j/5) ≤ powerMargin j

private lemma power_le_margin (j : ℕ) : powerMargin j ≤ margin j := by
  rw [powerMargin, margin, sumTo_eq_primeSum]
  exact sub_le_sub_left (ThetaTransfer.primeSum_le_primePowerSum _) _

/-- Bertrand brackets x by doubled primes of comparable size. No gap estimate for primes is needed. -/
private lemma double_prime_brackets {N : ℕ} {x : ℝ} (hN : 2 ≤ N)
    (lo : 4*N ≤ x) (hi : 4*x ≤ (↑(N*N : ℕ):ℝ)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ 2*p ∧ 2*p ≤ ⌊x⌋₊ ∧
      ⌊x⌋₊ ≤ 2*q ∧ 2*q ≤ N*N ∧ (↑(2*q : ℕ):ℝ) ≤ 4*x := by
  let n := ⌊x/4⌋₊
  have big : (2:ℝ) ≤ N := Nat.cast_le.mpr hN
  have xn : (n:ℝ) ≤ x/4 := Nat.floor_le (by linarith)
  have nx : x/4 < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have nN : N ≤ n := (Nat.le_floor_iff (by linarith)).mpr (by linarith)
  obtain ⟨p,hp,lp,up⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  obtain ⟨q,hq,lq,uq⟩ := Nat.exists_prime_lt_and_le_two_mul (2*n+2) (by omega)
  have pLo : (↑(2*p : ℕ):ℝ) ≤ x := by
    have z : (p:ℝ) ≤ 2*n := by exact_mod_cast up
    push_cast
    linarith
  have qHi : x ≤ (↑(2*q : ℕ):ℝ) := by
    have z : 2*(n:ℝ)+2 < q := by exact_mod_cast lq
    push_cast
    linarith
  have cap : (↑(2*q : ℕ):ℝ) ≤ 4*x := by
    have z : (q:ℝ) ≤ 2*(2*(n:ℝ)+2) := by exact_mod_cast uq
    push_cast
    linarith
  exact ⟨p,q,hp,hq,by omega,(Nat.le_floor_iff (by linarith)).mpr pLo,
    Nat.cast_le.mp ((Nat.floor_le (by linarith : 0 ≤ x)).trans qHi),
    Nat.cast_le.mp (cap.trans hi),cap⟩

private lemma ordinary_margin_on_inner_window {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 2 ≤ N)
    (samples : ∀ p : ℕ, p.Prime → N ≤ 2*p → 2*p ≤ N*N →
      -C*Real.sqrt (2*p : ℕ) ≤ powerMargin (2*p))
    {x : ℝ} (lo : 4*N ≤ x) (hi : 4*x ≤ (↑(N*N : ℕ):ℝ)) :
    -(2*C+32)*Real.sqrt x ≤ margin x := by
  obtain ⟨p,q,pr,qr,start,lx,ux,stop,cap⟩ := double_prime_brackets hN lo hi
  have big : (2:ℝ) ≤ N := Nat.cast_le.mpr hN
  have xp : 1 ≤ x := by linarith
  have root : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt xp
  have atPrime (r : ℕ) (hr : r.Prime) (left : 2*p ≤ 2*r) (right : 2*r ≤ 2*q) :
      -(2*C)*Real.sqrt x ≤ margin (2*r : ℕ) := by
    have z := (samples r hr (start.trans left) (right.trans stop)).trans (power_le_margin _)
    have size : (↑(2*r : ℕ):ℝ) ≤ 4*x := (Nat.cast_le.mpr right).trans cap
    have rootCap := Real.sqrt_le_sqrt size
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at rootCap
    nlinarith [mul_le_mul_of_nonneg_left rootCap hC]
  have pq := lx.trans ux
  have grid := (block_margin_lower_iff pq (-(2*C)*Real.sqrt x)).mpr
    ⟨atPrime p pr le_rfl pq,atPrime q qr pq le_rfl,
      fun r hr l h => atPrime r hr l.le h.le⟩ ⌊x⌋₊ (Finset.mem_Icc.mpr ⟨lx,ux⟩)
  have floorPos : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using xp)
  have f1 : (1:ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast floorPos
  have near := Nat.lt_floor_add_one x
  have drop := margin_drop (u := (⌊x⌋₊:ℝ)) (v := x) (by linarith)
    (Nat.floor_le (by linarith)) (by linarith)
  linarith

private lemma zeroFree_of_sqrt_windows {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (windows : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1+δ)*U),
      -K*Real.exp (u/2) ≤ ThetaTransfer.primePowerDeficit u) :
    ∀ z : ℂ, 1/2 < z.re → riemannZeta z ≠ 0 := by
  apply ThetaTransfer.zeta_zeroFree_of_surplus (by norm_num) (by norm_num) hδ
  intro η hη U₀
  obtain ⟨Y,hY⟩ := Deduction.windowHyp_of_rpow_eventually (K*δ) η (by positivity) hη
  obtain ⟨U,hu,h⟩ := windows (max U₀ (max 0 (Real.log Y)))
  have late := (le_max_right U₀ _).trans hu
  have up := (le_max_left 0 (Real.log Y)).trans late
  have yU : Y ≤ Real.exp U := by
    by_cases yp : 0 < Y
    · exact (Real.log_le_iff_le_exp yp).mp ((le_max_right 0 _).trans late)
    · linarith [Real.exp_pos U]
  have mass := (hY (Real.exp U) yU).2
  rw [Real.log_exp, ← Real.exp_mul] at mass
  rw [mul_comm U η] at mass
  have eq : (fun u : ℝ => K*Real.exp (u/2)*Real.exp (-(1/2)*u)) = fun _ => K := by
    funext u
    rw [mul_assoc, ← Real.exp_add, show u/2+-(1/2)*u = 0 by ring, Real.exp_zero, mul_one]
  refine ⟨U,(le_max_left _ _).trans hu,fun u => K*Real.exp (u/2),?_,?_,?_⟩
  · rw [eq]
    exact continuousOn_const.integrableOn_Icc
  · intro u hu'
    exact ⟨by positivity, by linarith [h u hu']⟩
  · rw [eq,setIntegral_const,Real.volume_real_Icc_of_le (by nlinarith : U ≤ (1+δ)*U)]
    simp only [smul_eq_mul]
    nlinarith

/-- Even after dropping the two endpoint tests, any fixed square-root allowance
on the remaining doubled-prime samples on arbitrarily late square blocks implies RH. -/
theorem rh_of_doubled_prime_sqrt_windows {C : ℝ} (hC : 0 ≤ C)
    (blocks : ∀ m : ℕ, ∃ N ≥ m, ∀ p : ℕ, p.Prime → N ≤ 2*p → 2*p ≤ N*N →
      -C*Real.sqrt (2*p : ℕ) ≤ powerMargin (2*p)) : RiemannHypothesis := by
  obtain ⟨E,hE⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := 2*C+32+max E 0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply RiemannReduction.rh_of_right
  intro s hs _
  apply zeroFree_of_sqrt_windows hK (δ := 1/2) (by norm_num) _ s hs
  intro U₀
  obtain ⟨N,hN,samples⟩ := blocks (max 1024 ⌈Real.exp U₀⌉₊)
  have bigN := (le_max_left _ _).trans hN
  have big : (1024:ℝ) ≤ N := by exact_mod_cast bigN
  have pos : 0 < (N:ℝ) := by linarith
  have four : 0 < 4*(N:ℝ) := by linarith
  have fromU : Real.exp U₀ ≤ (N:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  refine ⟨Real.log (4*N), (Real.le_log_iff_exp_le four).mpr (by linarith), fun u hu => ?_⟩
  have lo := (Real.log_le_iff_le_exp four).mp hu.1
  have hi : 4*Real.exp u ≤ (↑(N*N : ℕ):ℝ) := by
    have enough := Real.log_le_log (by norm_num : (0:ℝ)<4^5)
      (show (4:ℝ)^5 ≤ N by norm_num; exact bigN)
    rw [Real.log_pow] at enough
    push_cast at enough
    have ub := hu.2
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) pos.ne'] at ub
    have e := Real.exp_le_exp.mpr (show Real.log 4+u ≤ Real.log N+Real.log N by linarith)
    rw [Real.exp_add, Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4),Real.exp_log pos] at e
    exact_mod_cast e
  have ord := ordinary_margin_on_inner_window hC (by omega : 2 ≤ N) samples lo hi
  have gap := ThetaTransfer.primePowerGap_le (Real.exp u/4)
  rw [show 4*(Real.exp u/4) = Real.exp u by ring] at gap
  have bound := gap.trans (hE _)
  have sqrt : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
  rw [margin, sumTo_eq_primeSum, sqrt] at ord
  rw [sqrt] at bound
  unfold ThetaTransfer.primePowerDeficit
  dsimp [K]
  nlinarith [mul_le_mul_of_nonneg_right (le_max_left E 0) (Real.exp_pos (u/2)).le]

theorem rh_of_fifth_blocks (h : FifthBlocks) : RiemannHypothesis := by
  apply rh_of_doubled_prime_sqrt_windows (C := 1/5) (by norm_num)
  intro m
  obtain ⟨N,lo,tests⟩ := h m
  refine ⟨N,lo,fun p hp pl pu => ?_⟩
  linarith [tests (2*p) (Finset.mem_Icc.mpr ⟨pl,pu⟩) (Or.inr (Or.inr ⟨p,hp,rfl⟩))]

/-- Any fixed square-root loss at the square samples throughout unbounded blocks suffices for RH. -/
theorem rh_of_square_sqrt_windows {C : ℝ} (hc : 0 ≤ C)
    (samples : ∀ m : ℕ, ∃ K ≥ m, ∀ k ∈ Finset.Icc K (K*K), -C*k ≤ powerMargin (k^2)) :
    RiemannHypothesis := by
  apply rh_of_doubled_prime_sqrt_windows (C := C+1) (by linarith)
  intro m
  obtain ⟨N,hm,checks⟩ := whole_sqrt_blocks_of_square_samples hc (ε := 1) (by norm_num) samples m
  exact ⟨N,hm,fun p _ lo hi => checks (2*p) (Finset.mem_Icc.mpr ⟨lo,hi⟩)⟩

#print axioms rh_of_doubled_prime_sqrt_windows
#print axioms rh_of_fifth_blocks
#print axioms rh_of_square_sqrt_windows
end RiemannReduction.PrimeGrid
