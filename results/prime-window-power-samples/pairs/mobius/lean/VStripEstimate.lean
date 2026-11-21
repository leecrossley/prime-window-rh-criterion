import CommonZeroTruncation
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset
namespace RiemannReduction.ZetaWindow
noncomputable section

private def unitWindow (t : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im-t| ≤ 1 ∧ riemannZeta z = 0}

private lemma unitCounts : ∃ C > (0:ℝ), ∀ t : ℝ, ∃ fin : (unitWindow t).Finite,
    ∑ z ∈ fin.toFinset, mass z ≤ C*Real.log (|t|+2) := by
  obtain ⟨C,hC,count⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C,hC,fun t => ?_⟩
  have h := count 1 (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one t
  simp only [DirichletCharacter.LFunction_modOne_eq,Nat.cast_one,one_mul] at h
  obtain ⟨fin,bound⟩ := h
  exact ⟨fin, by rwa [finsum_mem_eq_finite_toFinset_sum _ fin] at bound⟩

private def bin (z : ℂ) := ⌊|z.im|⌋₊

/-- Truncating at height t costs two logarithms for the absolute reciprocal zero weights. -/
theorem truncated_reciprocal_mass : ∃ H ≥ (0:ℝ), ∀ (t : ℝ), 2 ≤ t →
    ∀ S : Finset ℂ, (∀ z ∈ S, stripZero z ∧ |z.im| < t) →
    ∑ z ∈ S, mass z/‖z‖ ≤ H*(1+Real.log t)^2 := by
  classical
  obtain ⟨C,cp,count⟩ := unitCounts
  obtain ⟨low,_⟩ := count 0
  let L := ∑ z ∈ low.toFinset, mass z/‖z‖
  have lp : 0 ≤ L := sum_nonneg fun z _ => div_nonneg (mass_nonneg z) (norm_nonneg z)
  refine ⟨L+4*C,by positivity,fun t ht S spec => ?_⟩
  let high := S.filter (fun z => 1 ≤ |z.im|)
  let small := S.filter (fun z => ¬1 ≤ |z.im|)
  have smallSub : small ⊆ low.toFinset := by
    intro z hz
    obtain ⟨hs,lo⟩ := mem_filter.mp hz
    obtain ⟨⟨a,b,zero⟩,_⟩ := spec z hs
    exact low.mem_toFinset.mpr ⟨a,b,by simpa using (le_of_not_ge lo),zero⟩
  have smallBound : ∑ z ∈ small, mass z/‖z‖ ≤ L :=
    sum_le_sum_of_subset_of_nonneg smallSub (fun z _ _ => div_nonneg (mass_nonneg z) (norm_nonneg z))
  have logs : Real.log (t+2) ≤ 2*Real.log t := by
    have h := Real.log_le_log (by linarith : 0<t+2) (show t+2 ≤ t^2 by nlinarith [sq_nonneg (t-2)])
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have lg := Real.log_nonneg (show 1 ≤ t by linarith)
  have highBound : ∑ z ∈ high, mass z/‖z‖ ≤ (4*C*Real.log t)*(1+Real.log t) := by
    have split := sum_fiberwise_of_maps_to (s := high) (t := Icc 1 ⌊t⌋₊) (g := bin) (by
      intro z hz
      obtain ⟨hz,lo⟩ := mem_filter.mp hz
      exact mem_Icc.mpr ⟨Nat.le_floor (by simpa using lo),Nat.floor_mono (spec z hz).2.le⟩)
      (fun z => mass z/‖z‖)
    rw [←split]
    calc _ ≤ ∑ n ∈ Icc 1 ⌊t⌋₊, (4*C*Real.log t)*(n:ℝ)⁻¹ := by
             apply sum_le_sum
             intro n hn
             have np : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
             obtain ⟨pos,hpos⟩ := count (n:ℝ)
             obtain ⟨neg,hneg⟩ := count (-(n:ℝ))
             simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)] at hpos hneg
             let F := high.filter (fun z => bin z = n)
             have loc {z : ℂ} (hz : z ∈ F) : z ∈ S ∧ (n:ℝ) ≤ |z.im| ∧ |z.im| < n+1 := by
               obtain ⟨hi,eq⟩ := mem_filter.mp hz
               refine ⟨(mem_filter.mp hi).1,?_,?_⟩ <;> rw [←eq]
               · exact Nat.floor_le (abs_nonneg _)
               · exact Nat.lt_floor_add_one _
             have sub : F ⊆ pos.toFinset ∪ neg.toFinset := by
               intro z hz
               obtain ⟨zs,lo,hi⟩ := loc hz
               obtain ⟨⟨a,b,zero⟩,_⟩ := spec z zs
               apply mem_union.mpr
               rcases le_total 0 z.im with p | p
               · rw [abs_of_nonneg p] at lo hi
                 exact Or.inl (pos.mem_toFinset.mpr ⟨a,b,abs_le.mpr ⟨by linarith,by linarith⟩,zero⟩)
               · rw [abs_of_nonpos p] at lo hi
                 exact Or.inr (neg.mem_toFinset.mpr ⟨a,b,abs_le.mpr ⟨by linarith,by linarith⟩,zero⟩)
             have part := sum_le_sum_of_subset_of_nonneg (f:=mass) sub (fun z _ _ => mass_nonneg z)
             have union := sum_union_inter (s₁:=pos.toFinset) (s₂:=neg.toFinset) (f:=mass)
             have inter := sum_nonneg (s:=pos.toFinset ∩ neg.toFinset) (fun z _ => mass_nonneg z)
             have nt : (n:ℝ) ≤ t := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))
             have ln := (Real.log_le_log (by positivity : 0<(n:ℝ)+2) (by linarith : (n:ℝ)+2≤t+2)).trans logs
             have m : ∑ z ∈ F, mass z ≤ 4*C*Real.log t := by nlinarith [mul_le_mul_of_nonneg_left ln cp.le]
             calc _ ≤ ∑ z ∈ F, mass z/(n:ℝ) := by
                      apply sum_le_sum
                      intro z hz
                      exact div_le_div_of_nonneg_left (mass_nonneg z) np ((loc hz).2.1.trans (Complex.abs_im_le_norm _))
                  _ ≤ _ := by rw [←sum_div,←div_eq_mul_inv]; exact div_le_div_of_nonneg_right m np.le
         _ ≤ _ := by
           rw [←mul_sum]
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using
             harmonic_floor_le_one_add_log t (by linarith)
  have pieces := sum_filter_add_sum_filter_not S (fun z : ℂ => 1≤|z.im|) (fun z => mass z/‖z‖)
  change (∑ z ∈ high, mass z/‖z‖) + (∑ z ∈ small, mass z/‖z‖) = _ at pieces
  nlinarith [mul_nonneg lp (show 0≤(1+Real.log t)^2-1 by nlinarith [sq_nonneg (Real.log t)]),
    mul_nonneg cp.le (show 0≤1+Real.log t by linarith)]

private def belowHeight (t : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im| < t ∧ riemannZeta z = 0}

private lemma principal_psi (u : ℝ) :
    Formalism.MainNotions.GlobalTheoryTheory.psi0 (1 : DirichletCharacter ℂ 1) u = (psiError u : ℂ) := by
  have char (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n:ZMod 1) 1,map_one]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.psi0,Formalism.MainNotions.GlobalTheoryTheory.abelian₂,
    char,mul_one,psiError,Chebyshev.psi,Complex.ofReal_sub,Complex.ofReal_sum,
    ← Icc_add_one_left_eq_Ioc,zero_add]
  rfl

theorem psi_error_of_strip_bound {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η)
    (strip : ∀ z : ℂ, stripZero z → z.re ≤ σ) :
    ∃ C > (0:ℝ), ∀ t : ℝ, 2 ≤ t → |psiError t| ≤ C*t^(σ+η) := by
  classical
  obtain ⟨B,bp,trunc⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨H,hp,massBound⟩ := truncated_reciprocal_mass
  let L := ∑ᶠ z ∈ belowHeight 1, mass z/‖z‖
  let J := B*(5+|L|)+H
  have jp : 0 < J := by dsimp [J]; positivity
  let A := 1+1/(η/2)
  have ap : 0 < A := by dsimp [A]; positivity
  refine ⟨J*A^2,by positivity,fun t ht => ?_⟩
  have tp : 0 < t := by linarith
  have t1 : 1 ≤ t := by linarith
  have lg := Real.log_nonneg t1
  have base : 1 ≤ t^σ := Real.one_le_rpow t1 hσ
  have spec := trunc 1 (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one t t ht le_rfl
  simp only [DirichletCharacter.LFunction_modOne_eq,Nat.cast_one,one_mul,principal_psi] at spec
  have fin : (belowHeight t).Finite := spec.1
  let S := fin.toFinset
  have hS (z : ℂ) (hz : z ∈ S) : stripZero z ∧ |z.im| < t := by
    obtain ⟨p,o,i,eq⟩ := fin.mem_toFinset.mp hz
    exact ⟨⟨p,o,eq⟩,i⟩
  have err := spec.2
  change ‖(psiError t:ℂ) + ∑ᶠ z ∈ belowHeight t, zeroTerm z t‖ ≤
    B*(t*Real.log (t*t)^2/t+Real.log t+L) at err
  rw [finsum_mem_eq_finite_toFinset_sum _ fin,Real.log_mul tp.ne' tp.ne',
    mul_div_cancel_left₀ _ tp.ne'] at err
  have spectrum : ‖∑ z ∈ S, zeroTerm z t‖ ≤ (t^σ)*(H*(1+Real.log t)^2) := by
    apply (norm_sum_le _ _).trans
    calc _ ≤ ∑ z ∈ S, (t^σ)*(mass z/‖z‖) := by
             apply sum_le_sum; intro z hz
             rw [zeroTerm,norm_mul,norm_div,Complex.norm_natCast,Complex.norm_cpow_eq_rpow_re_of_pos tp]
             change mass z * (t^z.re / ‖z‖) ≤ _
             rw [show mass z * (t^z.re / ‖z‖) = (t^z.re)*(mass z/‖z‖) by ring]
             exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le t1 (strip z (hS z hz).1))
               (div_nonneg (mass_nonneg z) (norm_nonneg z))
         _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (massBound t ht S hS) (Real.rpow_nonneg tp.le _)
  have upper : (Real.log t + Real.log t)^2+Real.log t+L ≤ (5+|L|)*(1+Real.log t)^2 := by
    nlinarith [le_abs_self L,mul_nonneg (abs_nonneg L) (by nlinarith [sq_nonneg (Real.log t)] : 0≤(1+Real.log t)^2-1),
      sq_nonneg (Real.log t)]
  have grow := mul_le_mul_of_nonneg_left base (show 0 ≤ B*((5+|L|)*(1+Real.log t)^2) by positivity)
  have tri := norm_sub_le ((psiError t:ℂ) + ∑ z ∈ S, zeroTerm z t) (∑ z ∈ S, zeroTerm z t)
  rw [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs] at tri
  have main : |psiError t| ≤ J*(t^σ)*(1+Real.log t)^2 := by
    dsimp [J]
    apply tri.trans
    have ee := err.trans (mul_le_mul_of_nonneg_left upper bp.le)
    change ‖(psiError t:ℂ) + ∑ z ∈ S, zeroTerm z t‖ ≤ _ at ee
    nlinarith only [add_le_add ee spectrum,grow]
  have tHalf : 1 ≤ t^(η/2) := Real.one_le_rpow t1 (by linarith)
  have logHalf := Real.log_le_rpow_div tp.le (show 0<η/2 by linarith)
  have small : 1+Real.log t ≤ A*t^(η/2) := by dsimp [A]; rw [add_mul,one_mul,one_div,←div_eq_inv_mul]; linarith
  have sq := pow_le_pow_left₀ (by linarith : 0≤1+Real.log t) small 2
  have ep : (t^(η/2))^2 = t^η := by
    rw [←Real.rpow_natCast,←Real.rpow_mul tp.le]; congr 1; push_cast; ring
  rw [mul_pow,ep] at sq
  rw [Real.rpow_add tp]
  exact main.trans ((mul_le_mul_of_nonneg_left sq (by positivity : 0 ≤ J*t^σ)).trans_eq (by ring))

#print axioms truncated_reciprocal_mass
#print axioms psi_error_of_strip_bound

end
end RiemannReduction.ZetaWindow
