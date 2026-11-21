import PrimePacketMean

open Finset ArithmeticFunction
namespace RiemannReduction.DivisorBand
noncomputable section

def packetLog (t : ℝ) := 4 + Real.log t
def packetProfile (t : ℝ) := D t - mainSlope

theorem packetLog_ge {t : ℝ} (ht : 1 ≤ t) : 4 ≤ packetLog t := by
  unfold packetLog; linarith [Real.log_nonneg ht]

theorem packetLog_mono {s t : ℝ} (hs : 0 < s) (h : s ≤ t) : packetLog s ≤ packetLog t :=
  by unfold packetLog; linarith [Real.log_le_log hs h]

private lemma exp_power (z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    z^m ≤ (m.factorial : ℝ)*Real.exp z := by
  have h := Real.pow_div_factorial_le_exp z hz m
  have pos : 0 < (m.factorial : ℝ) := by positivity
  simpa [mul_comm] using (div_le_iff₀ pos).mp h

theorem log_power_sqrt (m : ℕ) : ∃ H > (0:ℝ), ∀ t : ℝ, 1 ≤ t →
    (packetLog t)^m ≤ H*Real.sqrt t := by
  refine ⟨2^m*(m.factorial : ℝ)*Real.exp 2,by positivity,fun t ht => ?_⟩
  have tp : 0<t := by linarith
  have h := exp_power (packetLog t / 2) (by linarith [packetLog_ge ht]) m
  have e : Real.exp (packetLog t/2) = Real.exp 2*Real.sqrt t := by
    rw [show packetLog t/2 = 2 + Real.log t/2 by unfold packetLog; ring,
      Real.exp_add, Real.exp_half, Real.exp_log tp]
  rw [e, div_pow] at h
  have v := (div_le_iff₀ (by positivity : (0:ℝ)<2^m)).mp h
  linarith only [v, show (m.factorial : ℝ)*(Real.exp 2*Real.sqrt t)*2^m =
      2^m*(m.factorial:ℝ)*Real.exp 2*Real.sqrt t by ring]

theorem exp_sqrt_log_power (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ H > (0:ℝ), ∀ t : ℝ, 1 ≤ t →
      Real.exp (-b*Real.sqrt (Real.log t))*(packetLog t)^m ≤ H := by
  let M := 2*m
  refine ⟨(M.factorial:ℝ)*Real.exp (2*b)/b^M,by positivity,fun t ht => ?_⟩
  let z := Real.sqrt (Real.log t)
  have zp : 0 ≤ z := Real.sqrt_nonneg _
  have z2 : z^2 = Real.log t := Real.sq_sqrt (Real.log_nonneg ht)
  have a : packetLog t ≤ (2+z)^2 := by unfold packetLog; nlinarith
  have ap := pow_le_pow_left₀ (by linarith [packetLog_ge ht] : 0 ≤ packetLog t) a m
  rw [← pow_mul] at ap
  have s := exp_power (b*(2+z)) (by positivity) M
  rw [mul_pow,show b*(2+z)=2*b+b*z by ring, Real.exp_add] at s
  have bp : 0 < b^M := by positivity
  have eq : Real.exp (-b*z) = (Real.exp (b*z))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  change Real.exp (-b*z)*(packetLog t)^m ≤ _
  rw [eq, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), div_mul_eq_mul_div, le_div_iff₀ bp]
  have v := mul_le_mul_of_nonneg_left ap bp.le
  dsimp [M] at v s ⊢
  nlinarith only [v,s]

theorem packetProfile_linear : ∃ H ≥ (1:ℝ), ∀ t : ℝ, 1 ≤ t → |packetProfile t| ≤ H*t := by
  refine ⟨|c|+(|Real.log 4|+4)+|mainSlope|+1,by linarith [abs_nonneg c,abs_nonneg (Real.log 4),abs_nonneg mainSlope],fun t ht => ?_⟩
  have tn : 0 ≤ t := by linarith
  have nn : 0 ≤ ThetaTransfer.primePowerSum (t/4) :=
    sum_nonneg (fun n _ => mul_nonneg vonMangoldt_nonneg (ThetaTransfer.tent_nonneg _))
  have up : ThetaTransfer.primePowerSum (t/4) ≤ Chebyshev.psi t := by
    rw [ThetaTransfer.primePowerSum, show 4*(t/4)=t by ring,
      Nat.range_succ_eq_Icc_zero, Chebyshev.psi_eq_sum_Icc]
    exact sum_le_sum fun n _ => mul_le_of_le_one_right vonMangoldt_nonneg (ThetaTransfer.tent_le_one _)
  have p := up.trans (Chebyshev.psi_le_const_mul_self tn)
  have a := mul_le_mul_of_nonneg_right (le_abs_self c) tn
  have d := mul_le_mul_of_nonneg_right (neg_abs_le c) tn
  have h := mul_le_mul_of_nonneg_right (le_abs_self (Real.log 4)) tn
  have m := mul_le_mul_of_nonneg_left ht (abs_nonneg mainSlope)
  rw [packetProfile,D,abs_le]
  constructor <;> nlinarith [abs_nonneg c,abs_nonneg (Real.log 4),le_abs_self mainSlope,neg_abs_le mainSlope,
    mul_nonneg (abs_nonneg c) tn,mul_nonneg (abs_nonneg (Real.log 4)) tn]

theorem packetProfile_decay (m : ℕ) : ∃ H ≥ (1:ℝ), ∀ t : ℝ, 1 ≤ t →
    |packetProfile t| *(packetLog t)^m ≤ H*t := by
  obtain ⟨b,B,bp,pnt⟩ := Formalism.ZF.gzPNT
  obtain ⟨F,Fp,hF⟩ := exp_sqrt_log_power m bp
  obtain ⟨G,Gp,hG⟩ := log_power_sqrt m
  obtain ⟨J,J1,hJ⟩ := packetProfile_linear
  let S := (packetLog 8)^m
  let U := |B| *F*2^m
  have Sn : 0 ≤ S := pow_nonneg (by linarith [packetLog_ge (by norm_num : (1:ℝ)≤8)]) _
  have Un : 0 ≤ U := by dsimp [U]; positivity
  have Jn : 0 ≤ J := by linarith
  have pos : 1 ≤ 1+J*S+6*U+|mainSlope| *G := by
    linarith [mul_nonneg Jn Sn,mul_nonneg (abs_nonneg mainSlope) Gp.le]
  refine ⟨_,pos,fun t ht => ?_⟩
  have tn : 0 ≤ t := by linarith
  have Lp : 0 ≤ packetLog t := by linarith [packetLog_ge ht]
  have powN : 0 ≤ (packetLog t)^m := pow_nonneg Lp _
  by_cases cut : t ≤ 8
  · have h := mul_le_mul (hJ t ht) (pow_le_pow_left₀ Lp (packetLog_mono (by linarith) cut) m)
          powN (by positivity : 0 ≤ J*t)
    have cmp : J*S ≤ 1+J*S+6*U+|mainSlope| *G := by linarith [mul_nonneg (abs_nonneg mainSlope) Gp.le]
    exact h.trans ((by dsimp [S]; ring : J*t*packetLog 8^m=J*S*t).le.trans
      (mul_le_mul_of_nonneg_right cmp tn))
  have ramp (d : ℝ) (d1 : 1 ≤ d) (d4 : d ≤ 4) :
      |Formalism.Gz (t/d)| *(packetLog t)^m ≤ U*t := by
    have dp : 0<d := by linarith
    have u2 : 2 ≤ t/d := (le_div_iff₀ dp).mpr (by linarith)
    have u1 : 1 ≤ t/d := by linarith
    have up : 0 < t/d := by linarith
    have un := div_le_self tn d1
    have L : packetLog t ≤ 2*packetLog (t/d) := by
      have ld := Real.log_le_sub_one_of_pos dp
      have e := Real.log_div (by linarith : t ≠ 0) dp.ne'
      unfold packetLog
      linarith [Real.log_nonneg u1]
    have lpow := pow_le_pow_left₀ Lp L m
    rw [mul_pow] at lpow
    have r := (pnt (t/d) u2).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self B) up.le) (Real.exp_pos _).le)
    have h := mul_le_mul r lpow powN (by positivity)
    have v := mul_le_mul_of_nonneg_left (hF (t/d) u1) (by positivity : 0 ≤ |B| *(t/d)*2^m)
    have w := mul_le_mul_of_nonneg_left un Un
    dsimp [U] at w ⊢
    nlinarith only [h,v,w]
  have a := abs_le.mp (show |Formalism.Gz t*(packetLog t)^m| ≤ U*t by
    rw [abs_mul,abs_of_nonneg powN]; simpa using ramp 1 (by norm_num) (by norm_num))
  have b₂ := abs_le.mp (show |Formalism.Gz (t/2)*(packetLog t)^m| ≤ U*t by
    rw [abs_mul,abs_of_nonneg powN]; exact ramp 2 (by norm_num) (by norm_num))
  have b₄ := abs_le.mp (show |Formalism.Gz (t/4)*(packetLog t)^m| ≤ U*t by
    rw [abs_mul,abs_of_nonneg powN]; exact ramp 4 (by norm_num) (by norm_num))
  have sq := Real.sq_sqrt tn
  have rt := Real.one_le_sqrt.mpr ht
  have st : Real.sqrt t ≤ t := by nlinarith [mul_le_mul_of_nonneg_right rt (Real.sqrt_nonneg t)]
  have slope := mul_le_mul_of_nonneg_left ((hG t ht).trans (mul_le_mul_of_nonneg_left st Gp.le))
      (abs_nonneg mainSlope)
  rw [← abs_of_nonneg powN,← abs_mul,packetProfile,deficit_eq_gz (by linarith),abs_le]
  have hs := abs_le.mp (show |mainSlope*(packetLog t)^m| ≤ |mainSlope| *(G*t) by
    simpa [abs_mul,abs_of_nonneg powN] using slope)
  constructor <;> nlinarith only [a.1,a.2,b₂.1,b₂.2,b₄.1,b₄.2,hs.1,hs.2,tn,
    mul_nonneg (mul_nonneg (by linarith : 0 ≤ J) Sn) tn]

end
end RiemannReduction.DivisorBand
