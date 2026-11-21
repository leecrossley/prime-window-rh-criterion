import PacketProfile
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PsiChiBoundOf

open Finset
namespace RiemannReduction.DivisorBand
noncomputable section

private lemma psi_one (y : ℝ) :
    Formalism.ZeroFreeDirichlet.psiChi (1:DirichletCharacter ℂ 1) y = (Chebyshev.psi y:ℂ) := by
  have char (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n:ZMod 1) = 1 := by
    rw [Subsingleton.elim (n:ZMod 1) 1,map_one]
  simp only [Formalism.ZeroFreeDirichlet.psiChi,char,mul_one,Chebyshev.psi,Complex.ofReal_sum,
    ← Icc_add_one_left_eq_Ioc,zero_add]

/-- The classical prime number theorem gives all fixed inverse logarithmic powers
for the ordinary Chebyshev theta function. -/
theorem packetTheta_decay (m : ℕ) : ∃ H ≥ (1:ℝ), ∀ t : ℝ, 1 ≤ t →
    |Chebyshev.theta t-t| * (packetLog t)^m ≤ H*t := by
  obtain ⟨cg,Kg,cgp,gz⟩ := Formalism.ZF.gzPNT
  let c₀ := min cg 1
  have cp : 0 < c₀ := lt_min cgp one_pos
  obtain ⟨F,Fp,f⟩ := exp_sqrt_log_power m (show 0<c₀/4 by linarith)
  obtain ⟨J,Jp,j⟩ := log_power_sqrt m
  obtain ⟨V,v⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let B := 128/c₀^2+18+4*|Kg|
  have bp : 0 ≤ B := by dsimp [B]; positivity
  let H := 1+B*F+|V| *J+(packetLog 2)^m
  have smallN : 0 ≤ (packetLog 2)^m := pow_nonneg (by linarith [packetLog_ge (by norm_num : (1:ℝ)≤2)]) _
  have h1 : 1 ≤ H := by dsimp [H]; linarith [mul_nonneg bp Fp.le,mul_nonneg (abs_nonneg V) Jp.le]
  refine ⟨H,h1,fun t ht => ?_⟩
  have tp : 0 < t := by linarith
  have ln : 0 ≤ (packetLog t)^m := pow_nonneg (by linarith [packetLog_ge ht]) _
  by_cases ht2 : 2 ≤ t
  · have p := Formalism.ZeroFreeDirichlet.chebyshev_principal_character_bound (q:=1)
        cp (min_le_right _ _) (min_le_left _ _) (abs_nonneg Kg) ht2
        (by simpa using Real.one_le_exp (show 0 ≤ c₀/4*Real.sqrt (Real.log t) by positivity))
        (fun z hz => (gz z (ht2.trans hz)).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self Kg) (tp.le.trans hz)) (Real.exp_pos _).le))
    rw [psi_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at p
    have ep : |Chebyshev.psi t-t| ≤ B*t*Real.exp (-(c₀/4)*Real.sqrt (Real.log t)) := by
      dsimp [B]; linarith only [p,show
        (128/c₀^2+2+4*|Kg|)*t*Real.exp (-(c₀/4)*Real.sqrt (Real.log t))+
        16*t*Real.exp (-(c₀/4)*Real.sqrt (Real.log t)) =
        (128/c₀^2+18+4*|Kg|)*t*Real.exp (-(c₀/4)*Real.sqrt (Real.log t)) by ring]
    have p1 := mul_le_mul_of_nonneg_right ep ln
    have p2 := mul_le_mul_of_nonneg_left (f t ht) (mul_nonneg bp tp.le)
    have gap := (v t).trans (mul_le_mul_of_nonneg_right (le_abs_self V) (Real.sqrt_nonneg t))
    have g1 := mul_le_mul_of_nonneg_right gap ln
    have g2 := mul_le_mul_of_nonneg_left (j t ht) (mul_nonneg (abs_nonneg V) (Real.sqrt_nonneg t))
    have ss := Real.mul_self_sqrt tp.le
    have triangle := abs_sub_le (Chebyshev.theta t) (Chebyshev.psi t) t
    rw [abs_of_nonpos (sub_nonpos.mpr (Chebyshev.theta_le_psi t))] at triangle
    have total := mul_le_mul_of_nonneg_right triangle ln
    dsimp [H]
    nlinarith only [p1,p2,g1,g2,total,show |V| *Real.sqrt t*(J*Real.sqrt t) = |V| *J*t by
      calc _ = |V| *J*(Real.sqrt t*Real.sqrt t) := by ring
           _ = _ := by rw [ss],tp.le,mul_nonneg smallN tp.le]
  · have z := Chebyshev.theta_eq_zero_of_lt_two (lt_of_not_ge ht2)
    rw [z,zero_sub,abs_neg,abs_of_pos tp]
    have pow := pow_le_pow_left₀ (by linarith [packetLog_ge ht]) (packetLog_mono tp (le_of_not_ge ht2)) m
    have le : (packetLog 2)^m ≤ H := by dsimp [H]; linarith [mul_nonneg bp Fp.le,mul_nonneg (abs_nonneg V) Jp.le]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (pow.trans le) tp.le

end
end RiemannReduction.DivisorBand
