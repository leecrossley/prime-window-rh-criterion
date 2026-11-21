import FourthSignExcursions
import FourthPrimeMassTransfer
import SquareSignedConverse

/-! A logarithmic positive-part budget on fourth powers works with either
    sign of the actual square remainder. This proof uses real excursions
    from a hypothetical right-hand zero. -/

open Finset Filter
namespace RiemannReduction.DivisorBand.FourthMass
noncomputable section

def signedDeficit (s : ℝ) (n : ℕ) : ℝ := s*D ((n:ℝ)^4)
def signedRemainder (s : ℝ) (n : ℕ) : ℝ := s*remainder n

private theorem harmonic_block (m : ℕ) (mp : 1 ≤ m) :
    ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ ≤ 1+2*Real.log m := by
  have ext := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc mp (le_refl (m^2)))
    (f := fun n : ℕ => (n:ℝ)⁻¹) (fun _ _ _ => by positivity)
  have h := harmonic_le_one_add_log (m^2)
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
             Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at h
  exact ext.trans h

private theorem sum_majorant (m : ℕ) (mp : 1 ≤ m) (C : ℝ) (c0 : 0 ≤ C)
    (f : ℕ → ℝ) (each : ∀ n ∈ Icc m (m^2), f n ≤ C*(n:ℝ)⁻¹) :
    ∑ n ∈ Icc m (m^2), f n ≤ C*(1+2*Real.log m) := by
  apply (sum_le_sum each).trans
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (harmonic_block m mp) c0

private theorem square_input {n : ℕ} (late : 10^8 ≤ n) :
    |D ((n:ℝ)^4)-remainder n| ≤ 2*(n:ℝ)^2 := by
  have h : 10^16 ≤ n^2 := calc
    10^16 = (10^8)^2 := by norm_num
    _ ≤ n^2 := Nat.pow_le_pow_left late _
  have dyad := deficit_pair_error_two h
  rw [show (((n^2:ℕ):ℝ))^2=(n:ℝ)^4 by push_cast; ring, Nat.cast_pow] at dyad
  exact dyad

theorem signed_mass_discrepancy (s : ℝ) (sign : s=1 ∨ s= -1) {m : ℕ} (late : 10^8 ≤ m) :
    |mass (signedDeficit s) m-mass (signedRemainder s) m| ≤ 2*(1+2*Real.log m) := by
  unfold mass
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_majorant m (by omega) 2 (by norm_num)
  intro n hn
  have large := late.trans (mem_Icc.mp hn).1
  have np : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [←sub_div,abs_div,abs_of_pos (pow_pos np _)]
  apply (div_le_iff₀ (pow_pos np 3)).mpr
  have one : |s|=1 := by rcases sign with rfl|rfl <;> norm_num
  calc
    _ ≤ |signedDeficit s n-signedRemainder s n| := abs_max_sub_max_le_abs _ _ _
    _ = |D ((n:ℝ)^4)-remainder n| := by rw [signedDeficit,signedRemainder,←mul_sub,abs_mul,one,one_mul]
    _ ≤ 2*(n:ℝ)^2 := square_input large
    _ = 2*(n:ℝ)⁻¹*(n:ℝ)^3 := by field_simp

private theorem transfer_signed (s : ℝ) (sign : s=1 ∨ s= -1) :
    cofinalLogBound (signedDeficit s) ↔ cofinalLogBound (signedRemainder s) := by
  constructor <;> rintro ⟨C,nonnegative,h⟩ <;> refine ⟨C+2,by linarith,?_⟩ <;> intro A
  all_goals
    obtain ⟨m,large,budget⟩ := h (max (10^8) A)
    refine ⟨m,(le_max_right _ _).trans large,?_⟩
    have ab := abs_le.mp (signed_mass_discrepancy s sign ((le_max_left _ _).trans large))
    rw [add_mul]
    linarith

theorem quartic_mass_grows (failure : ¬RiemannHypothesis) :
    ∃ h > (0:ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ᶠ a : ℕ in atTop,
      (a:ℝ)^h ≤ mass (signedDeficit s) a := by
  obtain ⟨h,hp,runs⟩ := fourth_sample_excursions failure
  refine ⟨h,hp,fun s sign => ?_⟩
  filter_upwards [runs s sign,eventually_ge_atTop (1:ℕ)] with a run ap
  obtain ⟨N,w,H,first,last,h0,total,inside⟩ := run
  have ar : 0 < (a:ℝ) := by exact_mod_cast ap
  let f := fun n : ℕ => max (signedDeficit s n) 0/(n:ℝ)^3
  have part : ((w:ℝ)+1)*H ≤ ∑ n ∈ Icc N (N+w), (a:ℝ)^2*f n := by
    have each (n : ℕ) (hn : n ∈ Icc N (N+w)) : H ≤ (a:ℝ)^2*f n := by
      have bounds := mem_Icc.mp hn
      have np : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have cap : (n:ℝ) ≤ (a:ℝ)^2 := by exact_mod_cast bounds.2.trans last
      have v := inside n hn
      change H < s*(D ((n:ℝ)^4)/(n:ℝ)^2) at v
      have v' : H*(n:ℝ)^2 ≤ signedDeficit s n := by
        rw [←mul_div_assoc] at v
        exact (le_div_iff₀ (sq_pos_of_pos np)).mp v.le
      change H ≤ (a:ℝ)^2*(max (signedDeficit s n) 0/(n:ℝ)^3)
      rw [←mul_div_assoc]
      apply (le_div_iff₀ (pow_pos np 3)).mpr
      calc
        H*(n:ℝ)^3 = (n:ℝ)*(H*(n:ℝ)^2) := by ring
        _ ≤ (n:ℝ)*max (signedDeficit s n) 0 :=
          mul_le_mul_of_nonneg_left (v'.trans (le_max_left _ _)) np.le
        _ ≤ (a:ℝ)^2*max (signedDeficit s n) 0 := mul_le_mul_of_nonneg_right cap (le_max_right _ _)
    simpa [Nat.card_Icc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using sum_le_sum each
  have extend := sum_le_sum_of_subset_of_nonneg (f:=fun n => (a:ℝ)^2*f n)
    (Icc_subset_Icc first last) (fun i _ _ => mul_nonneg (sq_nonneg _) (div_nonneg (le_max_right _ _) (by positivity)))
  have bound := total.trans (part.trans extend)
  rw [←mul_sum,Real.rpow_add ar,Real.rpow_two] at bound
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ar)).mp bound

private theorem log_budget_lt {h : ℝ} (hp : 0<h) (C : ℝ) (c0 : 0≤C) :
    ∀ᶠ a : ℕ in atTop, C*(1+2*Real.log a) < (a:ℝ)^h := by
  let δ : ℝ := 1/(8*(C+1))
  have δp : 0 < δ := by dsimp [δ]; positivity
  have small := (isLittleO_log_rpow_atTop hp).bound δp
  have growing := ((tendsto_rpow_atTop hp).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop (2*C+1)
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)) small,growing,eventually_ge_atTop (1:ℕ)] with a hl big one
  have ar : (1:ℝ)≤a := by exact_mod_cast one
  have rp := Real.rpow_nonneg (Nat.cast_nonneg a : (0:ℝ)≤a) h
  change 2*C+1 < (a:ℝ)^h at big
  change ‖Real.log (a:ℝ)‖ ≤ δ*‖(a:ℝ)^h‖ at hl
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg ar),abs_of_nonneg rp] at hl
  have scale : (2*C)*δ ≤ 1/2 := by
    dsimp [δ]
    rw [←mul_div_assoc,mul_one]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have a1 := mul_le_mul_of_nonneg_left hl (show 0≤2*C by linarith)
  have a2 := mul_le_mul_of_nonneg_right scale rp
  nlinarith only [a1,a2,big]

private theorem signed_mass_of_rh (rh : RiemannHypothesis) (s : ℝ) (sign : s=1 ∨ s= -1) :
    cofinalLogBound (signedDeficit s) := by
  obtain ⟨C,cp,bound⟩ := square_root_bound_of_rh rh
  refine ⟨C,cp.le,fun A => ⟨max 3 A,le_max_right _ _,?_⟩⟩
  let m := max 3 A
  apply sum_majorant m (by dsimp [m]; omega) C cp.le
  intro n hn
  have late : 3≤n := (le_max_left 3 A).trans (mem_Icc.mp hn).1
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have cap := bound (n^2) (late.trans (Nat.le_self_pow (by decide) _))
  rw [show (((n^2:ℕ):ℝ))^2=(n:ℝ)^4 by push_cast; ring, Nat.cast_pow] at cap
  have one : |s|=1 := by rcases sign with rfl|rfl <;> norm_num
  have point : signedDeficit s n ≤ C*(n:ℝ)^2 := (le_abs_self _).trans (by
    simpa only [signedDeficit,abs_mul,one,one_mul] using cap)
  apply (div_le_iff₀ (pow_pos np 3)).mpr
  calc
    max (signedDeficit s n) 0 ≤ C*(n:ℝ)^2 := max_le point (mul_nonneg cp.le (sq_nonneg _))
    _ = C*(n:ℝ)⁻¹*(n:ℝ)^3 := by field_simp

/-- Either sign gives a complete logarithmic criterion for the same residual. -/
theorem rh_iff_signed_quartic_budget (s : ℝ) (sign : s=1 ∨ s= -1) :
    RiemannHypothesis ↔ cofinalLogBound (signedRemainder s) := by
  rw [←transfer_signed s sign]
  refine ⟨fun rh => signed_mass_of_rh rh s sign, ?_⟩
  rintro ⟨C,c0,good⟩
  by_contra failure
  obtain ⟨h,hp,growth⟩ := quartic_mass_grows failure
  obtain ⟨base,after⟩ := eventually_atTop.mp ((growth s sign).and (log_budget_lt hp C c0))
  obtain ⟨m,late,pass⟩ := good base
  obtain ⟨lower,upper⟩ := after m late
  exact (not_lt_of_ge (lower.trans pass)) upper

/-- If an off-line zero exists, each signed remainder mass eventually exceeds
    a fixed positive power of the base on every complete window. -/
theorem remainder_mass_grows (failure : ¬RiemannHypothesis) :
    ∃ j > (0:ℝ), ∀ s : ℝ, (s=1 ∨ s= -1) → ∀ᶠ a : ℕ in atTop,
      (a:ℝ)^j < mass (signedRemainder s) a := by
  obtain ⟨h,hp,growth⟩ := quartic_mass_grows failure
  have jp : 0<h/2 := by linarith
  refine ⟨h/2,jp,fun s sign => ?_⟩
  have large := ((tendsto_rpow_atTop jp).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 3
  filter_upwards [growth s sign,log_budget_lt jp 2 (by norm_num),large,eventually_ge_atTop (10^8:ℕ)] with a lower logp high late
  have ap : 0<(a:ℝ) := by exact_mod_cast (show 0<a by omega)
  change 3 ≤ (a:ℝ)^(h/2) at high
  have square : (a:ℝ)^h = ((a:ℝ)^(h/2))^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ap.le]; congr 1; norm_num
  rw [square] at lower
  have upper := (abs_le.mp (signed_mass_discrepancy s sign late)).2
  nlinarith only [lower,logp,upper,mul_nonneg (by linarith : 0 ≤ (a:ℝ)^(h/2)-2) (Real.rpow_nonneg ap.le (h/2))]

/-- A separate cofinal sequence is allowed for each positive exponent. -/
theorem rh_iff_subpower_quartic_budget (s : ℝ) (sign : s=1 ∨ s= -1) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ m ≥ A, mass (signedRemainder s) m ≤ (m:ℝ)^ε := by
  constructor
  · intro rh ε ep A
    obtain ⟨C,c0,good⟩ := (rh_iff_signed_quartic_budget s sign).mp rh
    obtain ⟨u,large⟩ := eventually_atTop.mp (log_budget_lt ep C c0)
    obtain ⟨m,start,pass⟩ := good (max u A)
    exact ⟨m,(le_max_right _ _).trans start,pass.trans (large m ((le_max_left _ _).trans start)).le⟩
  · intro good
    by_contra failure
    obtain ⟨j,jp,growth⟩ := remainder_mass_grows failure
    obtain ⟨u,large⟩ := eventually_atTop.mp (growth s sign)
    obtain ⟨m,start,pass⟩ := good j jp u
    exact (not_lt_of_ge pass) (large m start)

/-- Cofinal control of losses on fourth-power samples would bound every sufficiently
    late square, including all integers on every sufficiently late complete block. -/
theorem all_squares_of_quartic_loss (budget : cofinalLogBound (signedRemainder (-1))) :
    ∃ C > (0:ℝ), ∀ k : ℕ, 3≤k → |D ((k:ℝ)^2)| ≤ C*k :=
  square_root_bound_of_rh ((rh_iff_signed_quartic_budget (-1) (Or.inr rfl)).mpr budget)

theorem all_squares_of_subpower_quartic_loss
    (budget : ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ m ≥ A, mass (signedRemainder (-1)) m ≤ (m:ℝ)^ε) :
    ∃ C > (0:ℝ), ∀ k : ℕ, 3≤k → |D ((k:ℝ)^2)| ≤ C*k :=
  square_root_bound_of_rh ((rh_iff_subpower_quartic_budget (-1) (Or.inr rfl)).mpr budget)

end
end RiemannReduction.DivisorBand.FourthMass
