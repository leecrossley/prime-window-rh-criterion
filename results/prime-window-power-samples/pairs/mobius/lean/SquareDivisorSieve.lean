import PrimeBand

/-! A nonnegative divisor-square majorant for the ordinary prime tent. -/
open Finset
namespace RiemannReduction.DivisorSieve
noncomputable section

/-- A real divisor weight supported through R and normalized on primes above R. -/
def Admissible (R : ℕ) (v : ℕ → ℝ) : Prop :=
  v 1 = 1 ∧ ∀ d > R, v d = 0

def response (v : ℕ → ℝ) (m : ℕ) : ℝ := ∑ d ∈ m.divisors, v d

def weight (j m : ℕ) : ℝ :=
  Real.log m * ThetaTransfer.tent (((j : ℝ) / 4) / m)

def majorant (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ range (j + 1), weight j m * response v m ^ 2

def compositeMass (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ (range (j + 1)).filter (fun n => ¬ n.Prime), weight j m * response v m ^ 2

theorem weight_nonneg (j m : ℕ) : 0 ≤ weight j m := by
  rcases m with _ | m
  · simp [weight]
  · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_pos m))
      (ThetaTransfer.tent_nonneg _)

theorem majorant_eq {j R : ℕ} {v : ℕ → ℝ} (cut : 4*R ≤ j) (hv : Admissible R v) :
    majorant v j = ThetaTransfer.primeSum ((j:ℝ)/4) + compositeMass v j := by
  unfold majorant compositeMass ThetaTransfer.primeSum
  rw [show 4*((j:ℝ)/4)=(j:ℝ) by ring, Nat.floor_natCast]
  rw [← sum_filter_add_sum_filter_not (range (j+1)) Nat.Prime]
  congr 1
  apply sum_congr rfl
  intro p hp
  obtain ⟨_,pp⟩ := mem_filter.mp hp
  by_cases h : R < p
  · simp [weight,response,Nat.Prime.divisors pp,hv.1,hv.2 p h,Ne.symm pp.ne_one]
  · have small : (p:ℝ) ≤ (j:ℝ)/4 := by
      have cp : (4:ℝ)*R ≤ j := by exact_mod_cast cut
      have rp : (p:ℝ) ≤ R := by exact_mod_cast (le_of_not_gt h)
      linarith
    have ratio : 1 ≤ ((j:ℝ)/4)/p := (one_le_div (by exact_mod_cast pp.pos)).2 small
    simp [weight,ThetaTransfer.tent_pieces,ratio]

private theorem divisor_pair {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (h : d ∣ p*q) :
    d = 1 ∨ d = p ∨ d = q ∨ d = p*q := by
  obtain ⟨a,b,ha,hb,rfl⟩ := dvd_mul.mp h
  rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> simp

theorem response_pair {p q R : ℕ} {v : ℕ → ℝ} (hv : Admissible R v)
    (hp : p.Prime) (hq : q.Prime) (hqR : R<q) :
    response v (p*q) = 1+v p := by
  have incl : ({1,p}:Finset ℕ) ⊆ (p*q).divisors := by
    intro d hd
    simp only [mem_insert,mem_singleton] at hd
    rcases hd with rfl | rfl <;>
      simp [Nat.mem_divisors,hp.ne_zero,hq.ne_zero]
  unfold response
  rw [← sum_subset incl]
  · simp [hv.1,Ne.symm hp.ne_one]
  · intro d hd miss
    rcases divisor_pair hp hq (Nat.mem_divisors.mp hd).1 with rfl | rfl | rfl | rfl
    · simp at miss
    · simp at miss
    · exact hv.2 _ hqR
    · exact hv.2 _ (hqR.trans_le (Nat.le_mul_of_pos_left _ hp.pos))

theorem response_triple {p r h R : ℕ} {v : ℕ → ℝ} (hv : Admissible R v)
    (pp : p.Prime) (rp : r.Prime) (hp : h.Prime) (pr : p<r) (rh : r<h)
    (large : R<p*r) : response v (p*r*h) = 1 + v p + v r + v h := by
  have nrh := rh.ne
  have npr := pr.ne
  have nph := (pr.trans rh).ne
  have incl : ({1,p,r,h}:Finset ℕ) ⊆ (p*r*h).divisors := by
    intro d hd
    simp only [mem_insert,mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [Nat.mem_divisors,pp.ne_zero,rp.ne_zero,hp.ne_zero,dvd_mul_of_dvd_left]
  unfold response
  rw [← sum_subset incl]
  · simp [hv.1,Ne.symm pp.ne_one,Ne.symm rp.ne_one,Ne.symm hp.ne_one,npr,nph,nrh]
    ring
  · intro d hd miss
    obtain ⟨a,b,ha,hb,rfl⟩ := dvd_mul.mp (Nat.mem_divisors.mp hd).1
    have phBig : R < p*h := large.trans_le (Nat.mul_le_mul_left p rh.le)
    have rhBig : R < r*h := phBig.trans_le (Nat.mul_le_mul_right h pr.le)
    have allBig : R < p*r*h := large.trans_le (Nat.le_mul_of_pos_right _ hp.pos)
    rcases divisor_pair pp rp ha with rfl | rfl | rfl | rfl <;>
      rcases (Nat.dvd_prime hp).mp hb with rfl | rfl <;>
      simp_all <;> exact hv.2 _ (by assumption)

/-- In these four composite rows every choice of normalized weights pays a squared error. -/
theorem four_composite_rows {p r h q t u R : ℕ} {v : ℕ → ℝ} (hv : Admissible R v)
    (pp : p.Prime) (rp : r.Prime) (hp : h.Prime) (qp : q.Prime) (tp : t.Prime) (up : u.Prime)
    (pr : p<r) (rh : r<h) (large : R<p*r) (qr : R<q) (tr : R<t) (ur : R<u) :
    1 ≤ response v (p*q)^2 + response v (r*t)^2 + response v (h*u)^2 +
      response v (p*r*h)^2 := by
  rw [response_pair hv pp qp qr,response_pair hv rp tp tr,response_pair hv hp up ur,
    response_triple hv pp rp hp pr rh large]
  nlinarith only [sq_nonneg (v p+1/2),sq_nonneg (v r+1/2),sq_nonneg (v h+1/2),
    sq_nonneg (v p+v r+v h+3/2)]

end
end RiemannReduction.DivisorSieve
