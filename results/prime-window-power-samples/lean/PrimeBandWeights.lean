import PrimeGrid
import PrimeBand

namespace RiemannReduction.PrimeGrid

lemma weight_eq_tent (u : ℝ) {p : ℕ} (hp : 0 < p) :
    weight u p = ThetaTransfer.tent ((u/4)/p) := by
  have pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have scaled (a : ℝ) (ha : 0 < a) :
      max (u/a - 1) 0 = max (u-a) 0 / a := by
    rw [← max_div_div_right ha.le, zero_div, sub_div, div_self ha.ne']
  change (2*max (u-p) 0 - 3*max (u-↑(2*p : ℕ)) 0 + max (u-↑(4*p : ℕ)) 0) / (2*p) =
    max (4*((u/4)/p)-1) 0 - 3*max (2*((u/4)/p)-1) 0 + 2*max ((u/4)/p-1) 0
  push_cast
  rw [show 4*((u/4)/p) = u/p by ring,
    show 2*((u/4)/p) = u/(2*p) by field_simp; ring,
    show (u/4)/p = u/(4*p) by field_simp,
    scaled p pos, scaled (2*p) (by positivity), scaled (4*p) (by positivity)]
  field_simp
  ring

lemma sumTo_eq_primeSum (u : ℝ) :
    sumTo ⌊u⌋₊ u = ThetaTransfer.primeSum (u/4) := by
  rw [ThetaTransfer.primeSum, show 4*(u/4) = u by ring]
  unfold sumTo primes
  apply Finset.sum_congr rfl
  intro p hp
  rw [weight_eq_tent u (Finset.mem_filter.mp hp).2.pos]

end RiemannReduction.PrimeGrid
