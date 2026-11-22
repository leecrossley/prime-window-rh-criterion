import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK

/-! The dyadic part of the archived window, using only the prime-two exceptional
indices in the interval selection. This version needs no odd-prime tower input. -/
noncomputable section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
namespace RiemannReduction.PrincipalLayer

def TwoGrid (Ct : ℝ) (M : AbF) : Prop :=
  ∀ eps A1 : ℝ, 0 < eps → eps < 1/52 → ∃ J X0 : ℝ, 0 < J ∧
    ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X ≥ X0, ∀ q d : ℕ, PrimePair M.m q d →
      Real.log ((q:ℝ)*d) ≤ X ^ (eps/(4*J)) → ∃ Y : ℝ, InRange J X Y ∧
        ∀ x : ℝ, Y ≤ x → x ≤ Y^(2:ℝ) → BaAt M eps e t q d x

theorem dyadic_grid (M : AbF) {Ct : ℝ} (hCt : 1 ≤ Ct)
    (generators : ∃ CK : ℝ, LemmaK CK) (two : TwoIn) : TwoGrid Ct M := by
  obtain ⟨CK0,hK0⟩ := generators
  let CK := max CK0 1
  have hCK1 : 1 ≤ CK := le_max_right _ _
  have hCKpos : 0 < CK := zero_lt_one.trans_le hCK1
  have hK : LemmaK CK := kmono CK0 CK (le_max_left _ _) hK0
  obtain ⟨R,residue⟩ := two M
  intro eps A1 heps small
  set J : ℝ := 2 ^ (R+2) * (2*CK*Ct/eps)^R with hJdef
  have hCt0 : 0 < Ct := by linarith
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨x0, atTwo⟩ := partA CK hCKpos hK M R J Ct eps A1 hJ hCt0.le heps
  let x1 := max 2 x0
  have pos : 0 ≤ x1 := (by norm_num : (0:ℝ) ≤ 2).trans (le_max_left _ _)
  refine ⟨J,max 2 (x1^J),hJ,?_⟩
  intro e t admittedEt X late q d pair logSmall
  have lower : x1 ≤ X ^ (1/J) := by
    calc x1 = (x1^J)^(1/J) := by rw [← Real.rpow_mul pos,mul_one_div_cancel hJ.ne',Real.rpow_one]
         _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg pos _) ((le_max_right _ _).trans late) (by positivity)
  obtain ⟨L,_,_,base,level⟩ := residue q d pair
  obtain ⟨exceptions,card,use⟩ := atTwo e t admittedEt X q d pair logSmall L base level
  have eta : 0 < eps/(2*CK) := by positivity
  have etaCt : eps/(2*CK) ≤ Ct := by
    apply le_trans _ hCt
    rw [div_le_one (by positivity)]
    linarith
  have X2 := (le_max_left _ _).trans late
  obtain ⟨Y,range,good⟩ := window R (eps/(2*CK)) Ct X exceptions eta etaCt (by linarith) card
  rw [show Ct/(eps/(2*CK))=2*CK*Ct/eps by rw [div_div_eq_mul_div]; ring] at range
  refine ⟨Y,range,fun x hy hx => ?_⟩
  have lo : X^(1/J) ≤ x := range.1.trans hy
  exact use x ((le_max_right (2:ℝ) x0).trans (lower.trans lo)) lo (hx.trans range.2) (good x hy hx)

#print axioms dyadic_grid
end RiemannReduction.PrincipalLayer
