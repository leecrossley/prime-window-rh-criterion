import ZetaWindowMass
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula

open Finset
namespace RiemannReduction.ZetaWindow
noncomputable section

def psiError (t : ℝ) := Chebyshev.psi t - t

private def zerosBelow (y : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im| < y ∧ riemannZeta z = 0}

def zeroTerm (z : ℂ) (u : ℝ) : ℂ :=
  (analyticOrderNatAt riemannZeta z : ℂ) * ((u:ℂ)^z / z)

private theorem psi_error_one (u : ℝ) :
    Formalism.MainNotions.GlobalTheoryTheory.psi0 (1 : DirichletCharacter ℂ 1) u = (psiError u : ℂ) := by
  classical
  have char (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n:ZMod 1) 1,map_one]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.psi0,
    Formalism.MainNotions.GlobalTheoryTheory.abelian₂,char,mul_one,
    psiError,Chebyshev.psi,Complex.ofReal_sub,Complex.ofReal_sum,← Icc_add_one_left_eq_Ioc,zero_add]
  rfl

private lemma truncation_error_le {y u : ℝ} (hy : 2 ≤ y) (lo : y ≤ u) (hi : u ≤ 4*y) (L : ℝ) :
    u * Real.log (u*y)^2/y + Real.log u + L ≤ (1100+|L|)*Real.sqrt y := by
  have yp : 0 < y := by linarith
  have up : 0 < u := by linarith
  have ln := Real.log_nonneg (show 1 ≤ y by linarith)
  have logs := Real.log_le_log up hi
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) yp.ne',
    show (4:ℝ)=2^2 by norm_num,Real.log_pow] at logs
  have two := Real.log_le_log (by norm_num : (0:ℝ)<2) hy
  have l1 : Real.log u ≤ 3*Real.log y := by norm_num at logs; linarith
  have lp : 0 ≤ Real.log (u*y) := Real.log_nonneg (by nlinarith)
  have l2 : Real.log (u*y) ≤ 4*Real.log y := by rw [Real.log_mul up.ne' yp.ne']; linarith
  have quarter := Real.log_le_rpow_div yp.le (show (0:ℝ)<1/4 by norm_num)
  have square : (y^(1/4:ℝ))^2 = Real.sqrt y := by
    rw [← Real.rpow_natCast,← Real.rpow_mul yp.le,Real.sqrt_eq_rpow]; norm_num
  have power := pow_le_pow_left₀ ln (show Real.log y ≤ 4*y^(1/4:ℝ) by linarith) 2
  have l2sq := pow_le_pow_left₀ lp l2 2
  have l4 : Real.log (u*y)^2 ≤ 256*Real.sqrt y := by nlinarith
  have scaled : u*Real.log (u*y)^2/y ≤ 1024*Real.sqrt y := by
    apply (div_le_iff₀ yp).mpr
    nlinarith [mul_le_mul hi l4 (sq_nonneg _) (by linarith : 0 ≤ 4*y)]
  have half := Real.log_le_rpow_div yp.le (show (0:ℝ)<1/2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at half
  have r1 := Real.one_le_sqrt.mpr (show 1 ≤ y by linarith)
  nlinarith [mul_le_mul_of_nonneg_left r1 (abs_nonneg L),le_abs_self L]

/-- Take one finite multiset of zeros (represented by support and multiplicity)
for every evaluation in the integration interval. This theorem is unconditional. -/
theorem common_zero_truncation : ∃ B > (0:ℝ), ∀ y : ℝ, 2 ≤ y →
    ∃ S : Finset ℂ, (∀ z ∈ S, stripZero z) ∧ ∀ u : ℝ, y ≤ u → u ≤ 4*y →
      ‖(psiError u:ℂ) + ∑ z ∈ S, zeroTerm z u‖ ≤ B*Real.sqrt y := by
  classical
  obtain ⟨C,cp,trunc⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  let L := ∑ᶠ z ∈ zerosBelow 1, mass z / ‖z‖
  refine ⟨C*(1100+|L|),by positivity,fun y hy => ?_⟩
  have spec (u : ℝ) (lo : y ≤ u) := trunc 1 (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one u y hy lo
  simp only [DirichletCharacter.LFunction_modOne_eq,Nat.cast_one,one_mul,psi_error_one] at spec
  have fin : (zerosBelow y).Finite := (spec y le_rfl).1
  refine ⟨fin.toFinset,fun z hz => ?_,fun u lo hi => ?_⟩
  · have h := fin.mem_toFinset.mp hz
    exact ⟨h.1,h.2.1,h.2.2.2⟩
  · have est := (spec u lo).2
    change ‖(psiError u:ℂ) + ∑ᶠ z ∈ zerosBelow y, zeroTerm z u‖ ≤
      C*(u*Real.log (u*y)^2/y+Real.log u+L) at est
    rw [finsum_mem_eq_finite_toFinset_sum _ fin] at est
    exact est.trans ((mul_le_mul_of_nonneg_left (truncation_error_le hy lo hi L) cp.le).trans_eq
      (mul_assoc ..).symm)

#print axioms common_zero_truncation
end
end RiemannReduction.ZetaWindow
