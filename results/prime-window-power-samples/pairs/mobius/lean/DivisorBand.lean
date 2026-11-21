import PrimeBand

open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta ArithmeticFunction.Moebius
namespace RiemannReduction.DivisorBand
noncomputable section

/-- A finite sum over the integer dilations x/d. -/
def dilate (f : ArithmeticFunction ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ Icc 1 ⌊x⌋₊, f d * v (x/d)

/-- Dilation composition agrees with Dirichlet convolution, including the real cutoffs. -/
theorem dilate_mul (f g : ArithmeticFunction ℝ) (v : ℝ → ℝ) (x : ℝ) :
    dilate (f*g) v x = dilate f (dilate g v) x := by
  let N := ⌊x⌋₊
  let I := Icc 1 N
  let term (d m : ℕ) := f d*g (m/d)*v (x/m)
  have inner (m : ℕ) (hm : m ∈ I) :
      (f*g) m * v (x/m) = ∑ d ∈ I, if d ∣ m then term d m else 0 := by
    obtain ⟨pos,cap⟩ := mem_Icc.mp hm
    have filt : m.divisors = I.filter (fun d => d ∣ m) := by
      ext d
      simp only [Nat.mem_divisors,mem_filter,mem_Icc,I]
      constructor
      · rintro ⟨dvd,ne⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos dvd pos,(Nat.le_of_dvd pos dvd).trans cap⟩,dvd⟩
      · rintro ⟨_,dvd⟩; exact ⟨dvd,by omega⟩
    rw [mul_apply,Nat.sum_divisorsAntidiagonal (fun d e => f d*g e),Finset.sum_mul,filt,sum_filter]
  unfold dilate
  simp only [Nat.floor_div_natCast]
  change ∑ m ∈ I, (f*g) m * v (x/m) =
    ∑ d ∈ I, f d * ∑ e ∈ Icc 1 (N/d), g e*v (x/d/e)
  calc _ = ∑ m ∈ I, ∑ d ∈ I, if d ∣ m then term d m else 0 := sum_congr rfl inner
       _ = ∑ d ∈ I, ∑ m ∈ I, if d ∣ m then term d m else 0 := sum_comm
       _ = _ := by
         apply sum_congr rfl
         intro d hd
         have dp := (mem_Icc.mp hd).1
         rw [← sum_filter,Finset.mul_sum]
         symm
         apply sum_nbij' (fun e => d*e) (fun m => m/d)
         · intro e he
           obtain ⟨ep,cap⟩ := mem_Icc.mp he
           exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos dp ep,by
             simpa only [mul_comm] using (Nat.le_div_iff_mul_le dp).mp cap⟩,dvd_mul_right d e⟩
         · intro m hm
           obtain ⟨hi,dvd⟩ := mem_filter.mp hm
           obtain ⟨mp,cap⟩ := mem_Icc.mp hi
           exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le dp).mpr (by simpa using Nat.le_of_dvd mp dvd),
             Nat.div_le_div_right cap⟩
         · intro e _; exact Nat.mul_div_cancel_left e dp
         · intro m hm; exact Nat.mul_div_cancel' (mem_filter.mp hm).2
         · intro e _
           simp only [term,Nat.mul_div_cancel_left e dp,Nat.cast_mul,div_div]
           ring

theorem dilate_one (v : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x) : dilate 1 v x = v x := by
  have mem : 1 ∈ Icc 1 ⌊x⌋₊ := mem_Icc.mpr ⟨le_rfl,Nat.le_floor (by simpa using hx)⟩
  simp [dilate,ArithmeticFunction.one_apply,ite_mul,mem]

def c : ℝ := Real.log 2 / 2
def window (x : ℝ) : ℝ := ThetaTransfer.tent (x/4)
def D (x : ℝ) : ℝ := c*x-ThetaTransfer.primePowerSum (x/4)

theorem D_nat (j : ℕ) : D j = PrimeGrid.powerMargin j := by unfold D c PrimeGrid.powerMargin; ring

theorem band_dilate (x : ℝ) : dilate vonMangoldt window x = ThetaTransfer.primePowerSum (x/4) := by
  rw [ThetaTransfer.primePowerSum,show 4*(x/4)=x by ring,Nat.range_succ_eq_Icc_zero]
  unfold dilate window
  have extend : ∑ n ∈ Icc 1 ⌊x⌋₊, vonMangoldt n*ThetaTransfer.tent ((x/4)/n) =
      ∑ n ∈ Icc 0 ⌊x⌋₊, vonMangoldt n*ThetaTransfer.tent ((x/4)/n) := by
    apply sum_subset (Icc_subset_Icc (by decide) le_rfl)
    intro n hn off
    have z : n=0 := by have l := (mem_Icc.mp hn).2; by_contra h; exact off (mem_Icc.mpr ⟨by omega,l⟩)
    simp [z]
  rw [← extend]
  apply sum_congr rfl
  intro n _
  rw [show x/n/4 = x/4/n by ring]

/-- Averaging the actual prime band over all integer dilations replaces Λ by the ordinary logarithm. -/
theorem divisor_band_identity (x : ℝ) :
    dilate ζ (fun t => ThetaTransfer.primePowerSum (t/4)) x = dilate ArithmeticFunction.log window x := by
  simp_rw [← band_dilate]
  rw [← dilate_mul,ArithmeticFunction.zeta_mul_vonMangoldt]

/-- The residual after removal of a floor main term. It contains no prime weights. -/
def residual (A x : ℝ) : ℝ :=
  c*x*(harmonic ⌊x⌋₊:ℝ) - dilate ArithmeticFunction.log window x - A*⌊x⌋₊

theorem divisor_residual_eq (A x : ℝ) : residual A x = dilate ζ D x - A*⌊x⌋₊ := by
  have linear : dilate ζ (fun t => c*t) x = c*x*(harmonic ⌊x⌋₊:ℝ) := by
    simp only [dilate,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.mul_sum]
    apply sum_congr rfl
    intro d hd
    simp only [natCoe_apply,zeta_apply_ne (Nat.ne_of_gt (mem_Icc.mp hd).1),Nat.cast_one,one_mul]
    ring
  have split : dilate ζ D x =
      dilate ζ (fun t => c*t) x - dilate ζ (fun t => ThetaTransfer.primePowerSum (t/4)) x := by
    simp only [dilate,D,mul_sub,sum_sub_distrib]
  rw [split,linear,divisor_band_identity]; rfl

private lemma dilate_zeta_const (A x : ℝ) :
    dilate ζ (fun _ => A) x = A*(⌊x⌋₊:ℝ) := by
  unfold dilate
  calc _ = ∑ _d ∈ Icc 1 ⌊x⌋₊, A := by
         apply sum_congr rfl
         intro d hd
         simp [natCoe_apply,zeta_apply_ne (Nat.ne_of_gt (mem_Icc.mp hd).1)]
       _ = _ := by simp [mul_comm]

/-- Exact inversion of the elementary residual at every real x at least one. -/
theorem moebius_reconstruction (A : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    D x = A + dilate μ (residual A) x := by
  have move : dilate μ (residual A) x = dilate μ (dilate ζ D) x -
      dilate μ (dilate ζ (fun _ => A)) x := by
    unfold dilate
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    rw [← mul_sub,divisor_residual_eq,← dilate_zeta_const]
    rfl
  rw [move,← dilate_mul,← dilate_mul,coe_moebius_mul_coe_zeta,dilate_one _ hx,dilate_one _ hx]
  ring

#print axioms divisor_band_identity
#print axioms moebius_reconstruction
end
end RiemannReduction.DivisorBand
