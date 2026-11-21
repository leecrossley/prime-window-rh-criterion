import Mathlib

namespace MedianExceptions

/-- A median is required to have at least half the observations on each side. -/
def IsMedian {ι : Type*} (s : Finset ι) (f : ι → ℝ) (m : ℝ) : Prop :=
  s.card ≤ 2 * (s.filter fun i => f i ≤ m).card ∧
  s.card ≤ 2 * (s.filter fun i => m ≤ f i).card

/-- A strict majority in a closed band traps every median, including either even-sample endpoint. -/
theorem majority_traps_median {ι : Type*} (s : Finset ι) (f : ι → ℝ) (m c r : ℝ)
    (hm : IsMedian s f m)
    (hmajor : s.card < 2 * (s.filter fun i => |f i - c| ≤ r).card) :
    |m - c| ≤ r := by
  classical
  let good := s.filter fun i => |f i - c| ≤ r
  have card_bound (b : Finset ι) (hb : b ⊆ s) (hd : Disjoint good b) :
      good.card + b.card ≤ s.card := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) hb)
  have majority : s.card < 2 * good.card := hmajor
  rcases hm with ⟨hleft, hright⟩
  apply abs_le.mpr
  constructor
  · by_contra! h
    have hd : Disjoint good (s.filter fun i => f i ≤ m) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have ha := (abs_le.mp (Finset.mem_filter.mp hi).2).1
      have hb := (Finset.mem_filter.mp hj).2
      linarith
    have hc := card_bound _ (Finset.filter_subset _ _) hd
    omega
  · by_contra! h
    have hd : Disjoint good (s.filter fun i => m ≤ f i) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have ha := (abs_le.mp (Finset.mem_filter.mp hi).2).2
      have hb := (Finset.mem_filter.mp hj).2
      linarith
    have hc := card_bound _ (Finset.filter_subset _ _) hd
    omega

/-- A sample transported from its grid anchor is close to the full median once a majority is trapped. -/
theorem transport_to_median (x anchor c m t e : ℝ)
    (hx : |x - anchor| ≤ e) (ha : |anchor - c| ≤ t) (hm : |m - c| ≤ t + e) :
    |x-m| ≤ 2*(t+e) := by
  rcases abs_le.mp hx with ⟨hl, hr⟩
  rcases abs_le.mp ha with ⟨al, ar⟩
  rcases abs_le.mp hm with ⟨ml, mr⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The chronological prefix used for the finite certificate contains a strict majority. -/
theorem prefix_majority (offsets : ℕ) :
    offsets + 1 < 2 * ((offsets+1)/2 + 1) ∧ (offsets+1)/2 ≤ offsets := by
  omega

/-- The maximum density exponent is achieved at the right edge on this upper strip. -/
theorem huxley_exponent (s : ℝ) (hl : 3/4 ≤ s) (hr : s ≤ 7/8) :
    4*s - (7/8)*(2 - 3*(1-s)/(3*s-1)) ≤ 203/104 := by
  have hden : 0 < 3*s-1 := by linarith
  have hp : 0 ≤ (7-8*s)*(156*s-94) :=
    mul_nonneg (by linarith) (by linarith)
  let density : ℝ := 3*(1-s)/(3*s-1)
  have hid : density*(3*s-1) = 3*(1-s) := div_mul_cancel₀ _ hden.ne'
  change 4*s - (7/8)*(2-density) ≤ 203/104
  by_contra! h
  have hpos := mul_pos (sub_pos.mpr h) hden
  nlinarith only [hp, hid, hpos]

/-- On the lower strip Ingham's estimate also stays below the right-edge exponent. -/
theorem ingham_exponent (s : ℝ) (hr : s ≤ 3/4) :
    4*s - (7/8)*(2 - 3*(1-s)/(2-s)) ≤ 203/104 := by
  have hden : 0 < 2-s := by linarith
  have hp : 0 ≤ (3-4*s)*(5-4*s) := mul_nonneg (by linarith) (by linarith)
  field_simp [hden.ne']
  nlinarith

theorem power_margin :
    2*(127:ℚ)/128 - 203/104 - 1/32 = 1/832 := by norm_num

theorem longer_grid_margin :
    2 - ((7:ℚ)/2 - (23/13)*(1-3/20)) = 1/260 ∧ (1:ℚ)/300 < 1/260 := by
  norm_num

/-- Density times the cutoff exponent on the Ingham range. -/
theorem ingham_survivors (s : ℝ) (hl : 1/2 ≤ s) (hr : s ≤ 7/10) :
    3*(1-s)*(4*s-2)/(1+s) ≤ 36/85 := by
  apply (div_le_iff₀ (show (0:ℝ) < 1+s by linarith)).mpr
  have hp : 0 ≤ (7-10*s)*(78-102*s) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [hp]

/-- The Guth--Maynard density suffices on the upper range for counting the retained zeros. -/
theorem guth_maynard_survivors (s : ℝ) (hl : 7/10 ≤ s) :
    15*(1-s)*(4*s-2)/(25*s-9) ≤ 36/85 := by
  apply (div_le_iff₀ (show (0:ℝ) < 25*s-9 by linarith)).mpr
  have hp : 0 ≤ (10*s-7)*(510*s-318) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [hp]

theorem cutoff_margins : (36:ℚ)/85 + 1/256 < 3/7 ∧ (1:ℚ)/256 < 5/104 := by
  norm_num

#print axioms majority_traps_median
#print axioms transport_to_median
#print axioms prefix_majority
#print axioms huxley_exponent
#print axioms ingham_exponent
#print axioms power_margin
#print axioms longer_grid_margin
#print axioms ingham_survivors
#print axioms guth_maynard_survivors
#print axioms cutoff_margins

end MedianExceptions
