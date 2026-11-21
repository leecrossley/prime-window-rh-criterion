import MobiusAbsolute
import SquareContribution

open Finset Filter ArithmeticFunction
namespace RiemannReduction.DivisorBand
noncomputable section

/-- Primes with x/2 < p ≤ 2x/3, where the first-bin residual is positive. -/
def binPrimes (x : ℝ) : Finset ℕ := Nat.primesLE ⌊2*x/3⌋₊ \ Nat.primesLE ⌊x/2⌋₊

private lemma bin_member {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p ∈ binPrimes x) :
    p.Prime ∧ x/2 < p ∧ (p:ℝ) ≤ 2*x/3 := by
  obtain ⟨hi,lo⟩ := mem_sdiff.mp hp
  obtain ⟨cap,prime⟩ := Nat.mem_primesLE.mp hi
  refine ⟨prime,?_,(Nat.le_floor_iff (by positivity)).mp cap⟩
  exact lt_of_not_ge fun h => lo (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by positivity)).mpr h,prime⟩)

private lemma bin_log_sum {x : ℝ} (hx : 0 ≤ x) :
    ∑ p ∈ binPrimes x, Real.log p = Chebyshev.theta (2*x/3)-Chebyshev.theta (x/2) := by
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
  exact sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_le_floor (by linarith)))

private lemma count_lower {x t : ℝ} (tpos : 0 ≤ t) (le : t ≤ x)
    (low : 3*t/80 ≤ Chebyshev.theta (2*t/3)-Chebyshev.theta (t/2)) :
    3*t/80 ≤ ((binPrimes t).card:ℝ)*Real.log x := by
  rw [← bin_log_sum tpos] at low
  calc _ ≤ ∑ p ∈ binPrimes t, Real.log p := low
       _ ≤ ∑ _p ∈ binPrimes t, Real.log x := sum_le_sum (fun p hp => by
          obtain ⟨prime,_,h⟩ := bin_member tpos hp
          exact Real.log_le_log (Nat.cast_pos.mpr prime.pos) (by linarith))
       _ = _ := by simp

private lemma count_upper {x : ℝ} (hx : 4 ≤ x)
    (upper : Chebyshev.theta (2*x/3)-Chebyshev.theta (x/2) ≤ 3*x/10) :
    ((binPrimes x).card:ℝ)*Real.log x ≤ 3*x/5 := by
  have sum : ((binPrimes x).card:ℝ)*Real.log x ≤ 2*(∑ p ∈ binPrimes x, Real.log p) := by
    rw [mul_sum,← nsmul_eq_mul,← sum_const]
    apply sum_le_sum
    intro p hp
    obtain ⟨prime,lo,_⟩ := bin_member (by linarith) hp
    have p2 : (2:ℝ) ≤ p := by exact_mod_cast prime.two_le
    have le : x ≤ (p:ℝ)^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ (p:ℝ)-2) (Nat.cast_nonneg (α := ℝ) p)]
    have log := Real.log_le_log (by linarith : 0 < x) le
    simpa [Real.log_pow] using log
  rw [bin_log_sum (by linarith)] at sum
  linarith

private def summand (x : ℝ) (n : ℕ) : ℝ := (ArithmeticFunction.moebius n:ℝ)*residual mainSlope (x/n)

private lemma bin_weight {x : ℝ} {n : ℕ} (np : 0 < n) (lo : x/2 < n) (hi : (n:ℝ) ≤ 2*x/3) :
    1/48 ≤ residual mainSlope (x/n) ∧ residual mainSlope (x/n) ≤ 100 := by
  have pos := (Nat.cast_pos.mpr np : (0:ℝ) < n)
  have a : 3/2 ≤ x/n := (le_div_iff₀ pos).mpr (by linarith)
  have b : x/n < 2 := (div_lt_iff₀ pos).mpr (by linarith)
  exact ⟨residual_first_bin a b,(abs_le.mp (residual_bounded (by linarith : 1 ≤ x/n))).2⟩

private lemma prime_loss {x : ℝ} (hx : 4 ≤ x)
    (upper : Chebyshev.theta (2*x/3)-Chebyshev.theta (x/2) ≤ 3*x/10) :
    -60*x ≤ (∑ p ∈ binPrimes x, summand x p)*Real.log x := by
  have h : (∑ _p ∈ binPrimes x, (-100:ℝ)) ≤ ∑ p ∈ binPrimes x, summand x p := by
    apply sum_le_sum
    intro p hp
    obtain ⟨prime,lo,hi⟩ := bin_member (by linarith) hp
    have upper := (bin_weight prime.pos lo hi).2
    simp only [summand,moebius_apply_prime prime,Int.cast_neg,Int.cast_one,neg_one_mul]
    linarith
  simp only [sum_const,nsmul_eq_mul] at h
  have hl := mul_le_mul_of_nonneg_right h (Real.log_nonneg (by linarith : 1 ≤ x))
  nlinarith [count_upper hx upper]

private lemma prime_deficit {x : ℝ} (hx : 4 ≤ x)
    (low : 3*x/80 ≤ Chebyshev.theta (2*x/3)-Chebyshev.theta (x/2)) :
    (∑ p ∈ binPrimes x, summand x p)*Real.log x ≤ -x/1280 := by
  have h : (∑ p ∈ binPrimes x, summand x p) ≤ ∑ _p ∈ binPrimes x, (-1/48:ℝ) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨prime,lo,hi⟩ := bin_member (by linarith) hp
    have lower := (bin_weight prime.pos lo hi).1
    simp only [summand,moebius_apply_prime prime,Int.cast_neg,Int.cast_one,neg_one_mul]
    linarith
  simp only [sum_const,nsmul_eq_mul] at h
  have hl := mul_le_mul_of_nonneg_right h (Real.log_nonneg (by linarith : 1 ≤ x))
  nlinarith [count_lower (by linarith : 0 ≤ x) le_rfl low]

/-- Products of a fixed prime q and a prime in the rescaled interval. -/
def binProducts (x : ℝ) (q : Nat.Primes) : Finset ℕ :=
  (binPrimes (x/(q:ℕ))).image (fun p => (q:ℕ)*p)

private lemma product_position {x : ℝ} (xp : 0 ≤ x) {q : Nat.Primes} {p : ℕ}
    (hp : p ∈ binPrimes (x/(q:ℕ))) :
    p.Prime ∧ x/2 < ↑((q:ℕ)*p) ∧ (↑((q:ℕ)*p):ℝ) ≤ 2*x/3 := by
  have pos : (0:ℝ) < (q:ℕ) := Nat.cast_pos.mpr q.prop.pos
  obtain ⟨prime,lo,hi⟩ := bin_member (div_nonneg xp pos.le) hp
  refine ⟨prime,?_,?_⟩ <;> push_cast
  · have := (div_lt_iff₀ pos).mp (by linarith : x/(q:ℕ) < 2*p)
    linarith
  · have := (le_div_iff₀ pos).mp (by linarith : 3*(p:ℝ)/2 ≤ x/(q:ℕ))
    linarith

private lemma product_gain {x : ℝ} (hx : 4 ≤ x) (q : Nat.Primes) (above : ∀ p ∈ binPrimes (x/(q:ℕ)), (q:ℕ) < p)
    (low : 3*(x/(q:ℕ))/80 ≤ Chebyshev.theta (2*(x/(q:ℕ))/3)-Chebyshev.theta ((x/(q:ℕ))/2)) :
    x/1280*(1/(q:ℕ)) ≤ (∑ n ∈ binProducts x q, summand x n)*Real.log x := by
  have pos : (0:ℝ) < (q:ℕ) := Nat.cast_pos.mpr q.prop.pos
  have scale : x/(q:ℕ) ≤ x := div_le_self (by linarith) (by exact_mod_cast q.prop.one_lt.le)
  have count := count_lower (div_nonneg (by linarith) pos.le) scale low
  have each : (∑ _p ∈ binPrimes (x/(q:ℕ)), (1/48:ℝ)) ≤ ∑ n ∈ binProducts x q, summand x n := by
    unfold binProducts
    rw [sum_image (by intro a _ b _ e; exact Nat.eq_of_mul_eq_mul_left q.prop.pos e)]
    apply sum_le_sum
    intro p hp
    obtain ⟨prime,lo,hi⟩ := product_position (by linarith) hp
    have cop := (Nat.coprime_primes q.prop prime).mpr (above p hp).ne
    simp only [summand,isMultiplicative_moebius.map_mul_of_coprime cop,moebius_apply_prime prime,
      moebius_apply_prime q.prop,neg_mul_neg,one_mul,Int.cast_one]
    exact (bin_weight (Nat.mul_pos q.prop.pos prime.pos) lo hi).1
  simp only [sum_const,nsmul_eq_mul] at each
  have h := mul_le_mul_of_nonneg_right each (Real.log_nonneg (by linarith : 1 ≤ x))
  rw [show x/1280*(1/(q:ℕ))=(x/(q:ℕ))/1280 by ring]
  nlinarith

/-- The actual prime and semiprime divisor indices in the selected families. -/
def primeProductSet (S : Finset Nat.Primes) (x : ℝ) : Finset ℕ :=
  binPrimes x ∪ S.biUnion (binProducts x)

private lemma large_reciprocal_sum :
    ∃ S : Finset Nat.Primes, 80000 ≤ ∑ q ∈ S, (1/(q:ℕ):ℝ) := by
  by_contra! small
  exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun q => by positivity)
    (fun S => (small S).le))

private lemma balance_real (S : Finset Nat.Primes) (many : 80000 ≤ ∑ q ∈ S, (1/(q:ℕ):ℝ)) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ ∑ n ∈ primeProductSet S x, summand x n := by
  let M := S.sup (fun q => (q:ℕ))
  have scaled : ∀ᶠ x : ℝ in atTop, ∀ q ∈ S, 2*(M:ℝ) ≤ x/(q:ℕ) ∧
      3*(x/(q:ℕ))/80 ≤ Chebyshev.theta (2*(x/(q:ℕ))/3)-Chebyshev.theta ((x/(q:ℕ))/2) := by
    apply (eventually_all_finite S.finite_toSet).mpr
    intro q _
    have trend : Tendsto (fun x : ℝ => x/(q:ℕ)) atTop atTop :=
      tendsto_id.atTop_div_const (Nat.cast_pos.mpr q.prop.pos)
    exact (trend.eventually_ge_atTop _).and (trend.eventually (first_bin_theta_bounds.mono (fun _ h => h.1)))
  filter_upwards [eventually_ge_atTop (4:ℝ),first_bin_theta_bounds,scaled] with x hx bounds sc
  have xp : 0 ≤ x := by linarith
  have sep {q : Nat.Primes} (hq : q ∈ S) {p : ℕ} (hp : p ∈ binPrimes (x/(q:ℕ)))
      {r : Nat.Primes} (hr : r ∈ S) : (r:ℕ) < p := by
    have qp : (0:ℝ) ≤ (q:ℕ) := Nat.cast_nonneg _
    have h := (bin_member (div_nonneg xp qp) hp).2.1
    have m : (↑(r:ℕ):ℝ) ≤ M := by exact_mod_cast (le_sup (f := fun q : Nat.Primes => (q:ℕ)) hr)
    exact_mod_cast (show (↑(r:ℕ):ℝ) < p by linarith [(sc q hq).1])
  have disjointQ : (↑S : Set Nat.Primes).PairwiseDisjoint (binProducts x) := by
    intro a ha b hb ne
    apply disjoint_left.mpr
    intro n an bn
    obtain ⟨p,hp,ap⟩ := mem_image.mp an
    obtain ⟨r,hr,br⟩ := mem_image.mp bn
    have eq : (a:ℕ)*p = (b:ℕ)*r := ap.trans br.symm
    have dv : (a:ℕ) ∣ (b:ℕ)*r := eq ▸ dvd_mul_right _ _
    rcases a.prop.dvd_mul.mp dv with dv | dv
    · exact ne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq a.prop b.prop).mp dv))
    · have pr := (product_position xp hr).1
      exact (sep hb hr ha).ne ((Nat.prime_dvd_prime_iff_eq a.prop pr).mp dv)
  have dis : Disjoint (binPrimes x) (S.biUnion (binProducts x)) := by
    apply disjoint_left.mpr
    intro n hn hm
    obtain ⟨q,_,h⟩ := mem_biUnion.mp hm
    obtain ⟨p,hp,rfl⟩ := mem_image.mp h
    exact Nat.not_prime_mul q.prop.ne_one (product_position xp hp).1.ne_one (bin_member xp hn).1
  have gain : x/1280*(∑ q ∈ S, (1/(q:ℕ):ℝ)) ≤
      (∑ n ∈ S.biUnion (binProducts x), summand x n)*Real.log x := by
    rw [mul_sum,sum_biUnion disjointQ,sum_mul]
    exact sum_le_sum (fun q hq => product_gain hx q (fun _ hp => sep hq hp hq) (sc q hq).2)
  have budget := mul_le_mul_of_nonneg_left many (by linarith : 0 ≤ x/1280)
  have total : 0 ≤ (∑ n ∈ primeProductSet S x, summand x n)*Real.log x := by
    rw [primeProductSet,sum_union dis,add_mul]
    linarith [prime_loss hx bounds.2]
  exact nonneg_of_mul_nonneg_left total (Real.log_pos (by linarith))

private lemma sq_grows : Tendsto (fun k : ℕ => (k:ℝ)^2) atTop atTop :=
  (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop

/-- The primes alone contribute at most -k²/(1280 log(k²)) throughout all sufficiently large scales. -/
theorem prime_bin_negative : ∀ᶠ k : ℕ in atTop,
    ∑ p ∈ binPrimes ((k:ℝ)^2), tailTerm k p ≤ -(k:ℝ)^2/(1280*Real.log ((k:ℝ)^2)) := by
  filter_upwards [sq_grows.eventually_ge_atTop 4,sq_grows.eventually first_bin_theta_bounds] with k hk bounds
  have lg : 0 < Real.log ((k:ℝ)^2) := Real.log_pos (by linarith)
  apply (le_div_iff₀ (mul_pos (by norm_num) lg)).mpr
  change (∑ p ∈ binPrimes ((k:ℝ)^2), summand ((k:ℝ)^2) p)*(1280*Real.log ((k:ℝ)^2)) ≤ _
  linarith [prime_deficit hk bounds.1]

/-- One fixed finite set of small prime factors suffices to compensate every prime in
the bin, at every sufficiently large square. The union consists of actual tail indices. -/
theorem primes_compensated_by_semiprimes : ∃ S : Finset Nat.Primes, ∀ᶠ k : ℕ in atTop,
    primeProductSet S ((k:ℝ)^2) ⊆ Ioc k (k^2) ∧
      0 ≤ ∑ n ∈ primeProductSet S ((k:ℝ)^2), tailTerm k n := by
  obtain ⟨S,many⟩ := large_reciprocal_sum
  refine ⟨S,?_⟩
  filter_upwards [sq_grows.eventually (balance_real S many),eventually_ge_atTop (2:ℕ)] with k pass hk
  refine ⟨?_,pass⟩
  intro n hn
  have bounds : (k:ℝ)^2/2 < n ∧ (n:ℝ) ≤ 2*(k:ℝ)^2/3 := by
    rcases mem_union.mp hn with prime | semi
    · exact (bin_member (sq_nonneg (k:ℝ)) prime).2
    · obtain ⟨q,_,h⟩ := mem_biUnion.mp semi
      obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      exact (product_position (sq_nonneg (k:ℝ)) hp).2
  have kr : (2:ℝ) ≤ k := by exact_mod_cast hk
  exact mem_Ioc.mpr ⟨by exact_mod_cast (show (k:ℝ) < n by
    nlinarith [mul_le_mul_of_nonneg_right kr (Nat.cast_nonneg (α := ℝ) k)]),
    by exact_mod_cast (show (n:ℝ) ≤ (k:ℝ)^2 by nlinarith [sq_nonneg (k:ℝ)])⟩

#print axioms prime_bin_negative
#print axioms primes_compensated_by_semiprimes
end
end RiemannReduction.DivisorBand
