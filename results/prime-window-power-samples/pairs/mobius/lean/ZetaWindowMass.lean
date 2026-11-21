import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset

open Finset
namespace RiemannReduction.ZetaWindow
noncomputable section

def stripZero (z : ℂ) : Prop := 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0

def mass (z : ℂ) : ℝ := analyticOrderNatAt riemannZeta z

theorem mass_nonneg (z : ℂ) : 0 ≤ mass z := Nat.cast_nonneg _

theorem re_of_rh (rh : RiemannHypothesis) {z : ℂ} (h : stripZero z) : z.re = 1/2 := by
  apply rh z h.2.2
  · rintro ⟨n,rfl⟩
    have hz := h.1
    simp [Complex.mul_re] at hz
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  · rintro rfl
    simpa using h.2.1

private def window (t : ℝ) : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧
  |z.im-t| ≤ 1 ∧ riemannZeta z = 0}

private lemma windows : ∃ C > (0:ℝ), ∀ t : ℝ, ∃ fin : (window t).Finite,
    ∑ z ∈ fin.toFinset, mass z ≤ C*Real.log (|t|+2) := by
  obtain ⟨C,hC,count⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C,hC,fun t => ?_⟩
  have h := count 1 (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one t
  simp only [DirichletCharacter.LFunction_modOne_eq,Nat.cast_one,one_mul] at h
  obtain ⟨fin,bound⟩ := h
  exact ⟨fin, by rwa [finsum_mem_eq_finite_toFinset_sum _ fin] at bound⟩

private def bucket (z : ℂ) : ℕ := ⌊|z.im|⌋₊

private lemma bucket_window {z : ℂ} (hz : stripZero z) :
    z ∈ window (bucket z) ∨ z ∈ window (-(bucket z:ℝ)) := by
  have lo := Nat.floor_le (abs_nonneg z.im)
  have hi := Nat.lt_floor_add_one |z.im|
  change (0 < z.re ∧ z.re < 1 ∧ |z.im-↑⌊|z.im|⌋₊| ≤ 1 ∧ riemannZeta z = 0) ∨
    (0 < z.re ∧ z.re < 1 ∧ |z.im- -↑⌊|z.im|⌋₊| ≤ 1 ∧ riemannZeta z = 0)
  generalize hn : (↑⌊|z.im|⌋₊ : ℝ) = n at *
  by_cases pos : 0 ≤ z.im
  · rw [abs_of_nonneg pos] at lo hi
    exact Or.inl ⟨hz.1,hz.2.1,abs_le.mpr ⟨by linarith,by linarith⟩,hz.2.2⟩
  · rw [abs_of_nonpos (le_of_not_ge pos)] at lo hi
    exact Or.inr ⟨hz.1,hz.2.1,abs_le.mpr ⟨by linarith,by linarith⟩,hz.2.2⟩

private lemma weight_le {z : ℂ} (line : z.re = 1/2) :
    1/(‖z‖*‖z-1‖) ≤ 5/((bucket z:ℝ)+1)^2 := by
  have rz : ‖z‖^2 = 1/4+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply,line]; ring
  have rs : ‖z-1‖^2 = 1/4+z.im^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]; simp [line]; ring
  have eq : ‖z-1‖ = ‖z‖ := by nlinarith [norm_nonneg z,norm_nonneg (z-1)]
  have pos : 0 < ‖z‖ := by nlinarith [sq_nonneg z.im,norm_nonneg z]
  rw [eq,← sq]
  apply (div_le_div_iff₀ (sq_pos_of_pos pos) (sq_pos_of_pos (by positivity))).mpr
  have floor : (bucket z:ℝ) ≤ |z.im| := Nat.floor_le (abs_nonneg _)
  have size := pow_le_pow_left₀ (by positivity : 0 ≤ (bucket z:ℝ)+1)
    (by linarith : (bucket z:ℝ)+1 ≤ |z.im|+1) 2
  nlinarith [sq_nonneg (2*|z.im|-1/2),sq_abs z.im]

private lemma log_series : Summable (fun n : ℕ => Real.log ((n:ℝ)+2)/((n:ℝ)+1)^2) := by
  have ps := (Real.summable_nat_rpow.mpr (show -(3/2:ℝ) < -1 by norm_num))
  have shifted := (summable_nat_add_iff 1).mpr ps
  have major : Summable (fun n : ℕ => 4 * ((n:ℝ)+1)^(-(3/2):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using shifted.mul_left 4
  apply major.of_nonneg_of_le
  · intro n; exact div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])) (sq_nonneg _)
  intro n
  set x : ℝ := (n:ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0 < x := by linarith
  have l := Real.log_le_rpow_div (show 0 ≤ (n:ℝ)+2 by positivity) (show (0:ℝ)<1/2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at l
  have sq1 := Real.sq_sqrt (show 0 ≤ (n:ℝ)+2 by positivity)
  have sq2 := Real.sq_sqrt hp.le
  have roots : Real.sqrt ((n:ℝ)+2) ≤ 2*Real.sqrt x := by
    have : (n:ℝ)+2 ≤ 4*x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
    nlinarith [Real.sqrt_nonneg x,Real.sqrt_nonneg ((n:ℝ)+2)]
  rw [show -(3/2:ℝ)=1/2-(2:ℕ) by norm_num,Real.rpow_sub hp,Real.rpow_natCast,← Real.sqrt_eq_rpow]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (sq_pos_of_pos hp)]
  linarith

/-- Uniform in the truncation height and including multiplicities. -/
theorem finite_inverse_square_mass (rh : RiemannHypothesis) : ∃ H ≥ (0:ℝ),
    ∀ S : Finset ℂ, (∀ z ∈ S, stripZero z) →
    (∑ z ∈ S, mass z/(‖z‖*‖z-1‖)) ≤ H := by
  classical
  obtain ⟨C,cp,count⟩ := windows
  let g (n : ℕ) := Real.log ((n:ℝ)+2)/((n:ℝ)+1)^2
  have gn (n : ℕ) : 0 ≤ g n :=
    div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])) (sq_nonneg _)
  refine ⟨10*C*∑' n, g n, mul_nonneg (by positivity) (tsum_nonneg gn),fun S hS => ?_⟩
  let bins := S.image bucket
  have split := sum_fiberwise_of_maps_to (t := bins) (fun z hz => mem_image_of_mem bucket hz)
    (fun z => mass z/(‖z‖*‖z-1‖))
  rw [← split]
  calc _ ≤ ∑ n ∈ bins, 10*C*g n := by
         apply sum_le_sum
         intro n _
         obtain ⟨pos,hpos⟩ := count (n:ℝ)
         obtain ⟨neg,hneg⟩ := count (-(n:ℝ))
         simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)] at hpos hneg
         let F := S.filter (fun z => bucket z=n)
         have sub : F ⊆ pos.toFinset ∪ neg.toFinset := by
           intro z mem
           obtain ⟨hz,hn⟩ := mem_filter.mp mem
           have h := bucket_window (hS z hz)
           rw [hn] at h
           simpa using h
         have upper := sum_le_sum_of_subset_of_nonneg (f:=mass) sub (fun z _ _ => mass_nonneg z)
         have union := sum_union_inter (s₁:=pos.toFinset) (s₂:=neg.toFinset) (f:=mass)
         have small := sum_nonneg (s:=pos.toFinset ∩ neg.toFinset) (fun z _ => mass_nonneg z)
         have both : ∑ z ∈ F, mass z ≤ 2*C*Real.log ((n:ℝ)+2) := by linarith
         calc _ ≤ ∑ z ∈ F, mass z*(5/((n:ℝ)+1)^2) := by
                apply sum_le_sum
                intro z hz
                obtain ⟨mem,hn⟩ := mem_filter.mp hz
                have w := weight_le (re_of_rh rh (hS z mem))
                rw [hn] at w
                simpa only [← div_eq_mul_one_div] using mul_le_mul_of_nonneg_left w (mass_nonneg z)
              _ = (∑ z ∈ F, mass z)*(5/((n:ℝ)+1)^2) := (sum_mul ..).symm
              _ ≤ (2*C*Real.log ((n:ℝ)+2))*(5/((n:ℝ)+1)^2) :=
                mul_le_mul_of_nonneg_right both (by positivity)
              _ = 10*C*g n := by dsimp [g]; ring
       _ = 10*C * ∑ n ∈ bins, g n := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (log_series.sum_le_tsum bins (fun n _ => gn n)) (by positivity)

#print axioms finite_inverse_square_mass
end
end RiemannReduction.ZetaWindow
