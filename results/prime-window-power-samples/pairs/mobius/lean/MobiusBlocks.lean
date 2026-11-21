import MobiusPair
import SquareConstant

open Finset
namespace RiemannReduction.DivisorBand

/-- The same fixed allowance and the same full root intervals as in the square criterion. -/
def TailBoundBlocks (B : ℝ) : Prop :=
  ∀ m : ℕ, ∃ K ≥ m, ∀ k ∈ Icc K (K^2), -B*k ≤ largeDivisorSum k

theorem square_blocks_of_signed_tail {B : ℝ} (h : TailBoundBlocks B) :
    PrimeGrid.SquareBoundBlocks (B+100) := by
  intro m
  obtain ⟨K,start,bound⟩ := h (max 1 m)
  refine ⟨K,(le_max_right _ _).trans start,fun k hk => ?_⟩
  have pos : 0 < k := ((le_max_left 1 m).trans start).trans (mem_Icc.mp hk).1
  linarith [(tail_margin_comparison pos).1,bound k hk]

theorem signed_tail_of_square_blocks {C : ℝ} (h : PrimeGrid.SquareBoundBlocks C) :
    TailBoundBlocks (C+101) := by
  intro m
  obtain ⟨K,start,bound⟩ := h (max 1 m)
  refine ⟨K,(le_max_right _ _).trans start,fun k hk => ?_⟩
  have pos : 0 < k := ((le_max_left 1 m).trans start).trans (mem_Icc.mp hk).1
  linarith [(tail_margin_comparison pos).2,bound k hk]

theorem signed_tail_blocks_iff_square_blocks :
    (∃ B, TailBoundBlocks B) ↔ (∃ C, PrimeGrid.SquareBoundBlocks C) :=
  ⟨fun ⟨B,h⟩ => ⟨B+100,square_blocks_of_signed_tail h⟩,
   fun ⟨C,h⟩ => ⟨C+101,signed_tail_of_square_blocks h⟩⟩

theorem rh_of_signed_tail {B : ℝ} (h : TailBoundBlocks B) : RiemannHypothesis :=
  PrimeGrid.rh_of_any_square_bound (square_blocks_of_signed_tail h)

/-- Complement after pairing a width of k times floor(sqrt(k)). -/
def RemainderBoundBlocks (B : ℝ) : Prop :=
  ∀ m : ℕ, ∃ K ≥ m, ∀ k ∈ Icc K (K^2), -B*k ≤ unpairedTail k (k*k.sqrt)

theorem remainder_margin_comparison {k : ℕ} (large : 108^2 ≤ k) :
    unpairedTail k (k*k.sqrt) - 116*k ≤ PrimeGrid.powerMargin (k^2) ∧
    PrimeGrid.powerMargin (k^2) - 117*k ≤ unpairedTail k (k*k.sqrt) := by
  have pos : 0 < k := by norm_num at large; omega
  obtain ⟨a,b⟩ := tail_margin_comparison pos
  obtain ⟨c,d⟩ := abs_le.mp (peel_pairs_at_square_root_cost large)
  constructor <;> linarith

theorem square_blocks_of_remainder {B : ℝ} (h : RemainderBoundBlocks B) :
    PrimeGrid.SquareBoundBlocks (B+116) := by
  intro m
  obtain ⟨K,start,bound⟩ := h (max (108^2) m)
  refine ⟨K,(le_max_right _ _).trans start,fun k hk => ?_⟩
  have large := ((le_max_left (108^2) m).trans start).trans (mem_Icc.mp hk).1
  linarith [(remainder_margin_comparison large).1,bound k hk]

theorem remainder_of_square_blocks {C : ℝ} (h : PrimeGrid.SquareBoundBlocks C) :
    RemainderBoundBlocks (C+117) := by
  intro m
  obtain ⟨K,start,bound⟩ := h (max (108^2) m)
  refine ⟨K,(le_max_right _ _).trans start,fun k hk => ?_⟩
  have large := ((le_max_left (108^2) m).trans start).trans (mem_Icc.mp hk).1
  linarith [(remainder_margin_comparison large).2,bound k hk]

theorem remainder_blocks_iff_square_blocks :
    (∃ B, RemainderBoundBlocks B) ↔ (∃ C, PrimeGrid.SquareBoundBlocks C) :=
  ⟨fun ⟨B,h⟩ => ⟨B+116,square_blocks_of_remainder h⟩,
   fun ⟨C,h⟩ => ⟨C+117,remainder_of_square_blocks h⟩⟩

#print axioms signed_tail_blocks_iff_square_blocks
#print axioms rh_of_signed_tail
#print axioms remainder_blocks_iff_square_blocks
end RiemannReduction.DivisorBand
