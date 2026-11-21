import SquareDivisorSieve

open Finset
namespace RiemannReduction.DivisorSieve
noncomputable section

def box (a b : ℕ) : Finset ℕ := (Ioc a b).filter Nat.Prime

private lemma interior_weight {s m : ℕ} (sp : 0<s)
    (lo : 160*s^3 ≤ m) (hi : m ≤ 336*s^3) :
    1/8 ≤ weight (400*s^3) m := by
  have s1 : 1 ≤ s^3 := Nat.one_le_pow _ _ sp
  have m3 : 3 ≤ m := by omega
  have lg : 1 ≤ Real.log (m:ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).2
      (Real.exp_one_lt_three.le.trans (by exact_mod_cast m3))
  have lo' : 160*(s:ℝ)^3 ≤ m := by exact_mod_cast lo
  have hi' : (m:ℝ) ≤ 336*(s:ℝ)^3 := by exact_mod_cast hi
  have mp : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  let t : ℝ := (400*(s:ℝ)^3/4)/m
  have left : 9/32 ≤ t := (le_div_iff₀ mp).2 (by nlinarith [pow_nonneg (Nat.cast_nonneg (α:=ℝ) s) 3])
  have right : t ≤ 3/4 := (div_le_iff₀ mp).2 (by nlinarith [pow_nonneg (Nat.cast_nonneg (α:=ℝ) s) 3])
  have wt : 1/8 ≤ ThetaTransfer.tent t := by
    rw [ThetaTransfer.tent_pieces]
    split_ifs <;> linarith
  unfold weight
  push_cast
  change _ ≤ Real.log m * ThetaTransfer.tent t
  simpa using mul_le_mul lg wt (by norm_num : (0:ℝ) ≤ 1/8) (by linarith only [lg] : 0 ≤ Real.log m)

private lemma sorted_pair {p q a b : ℕ} (pp : p.Prime) (ap : a.Prime) (bp : b.Prime)
    (pb : p < b) (eq : p*q=a*b) : p=a ∧ q=b := by
  have dv : p ∣ a*b := eq ▸ dvd_mul_right p q
  rcases pp.dvd_mul.mp dv with ha | hb
  · have pa := (Nat.prime_dvd_prime_iff_eq pp ap).mp ha
    subst a
    exact ⟨rfl,Nat.eq_of_mul_eq_mul_left pp.pos eq⟩
  · exact False.elim (pb.ne ((Nat.prime_dvd_prime_iff_eq pp bp).mp hb))

private lemma sorted_triple {p r h a b c : ℕ} (pp : p.Prime) (rp : r.Prime)
    (ap : a.Prime) (bp : b.Prime) (cp : c.Prime)
    (pb : p<b) (bc : b<c) (rc : r<c) (eq : p*r*h=a*b*c) : p=a ∧ r=b ∧ h=c := by
  rw [mul_assoc p,mul_assoc a] at eq
  have dv : p ∣ a*(b*c) := eq ▸ dvd_mul_right p (r*h)
  have pa : p=a := by
    rcases pp.dvd_mul.mp dv with ha | hbc
    · exact (Nat.prime_dvd_prime_iff_eq pp ap).mp ha
    rcases pp.dvd_mul.mp hbc with hb | hc
    · exact False.elim (pb.ne ((Nat.prime_dvd_prime_iff_eq pp bp).mp hb))
    · exact False.elim ((pb.trans bc).ne ((Nat.prime_dvd_prime_iff_eq pp cp).mp hc))
  subst a
  exact ⟨rfl,sorted_pair rp bp cp rc (Nat.eq_of_mul_eq_mul_left pp.pos eq)⟩

private theorem row_sum {T : Type} [Fintype T] (f : T → ℕ) (inj : Function.Injective f)
    {s : ℕ} (sp : 0<s) (v : ℕ → ℝ)
    (bounds : ∀ x, 160*s^3 ≤ f x ∧ f x ≤ 336*s^3 ∧ ¬ (f x).Prime) :
    ∑ x, response v (f x)^2 ≤ 8*compositeMass v (400*s^3) := by
  classical
  let j := 400*s^3
  let g := fun m => weight j m * response v m^2
  have incl : univ.image f ⊆ (range (j+1)).filter (fun n => ¬ n.Prime) := by
    intro m hm
    obtain ⟨x,_,rfl⟩ := mem_image.mp hm
    obtain ⟨_,up,pr⟩ := bounds x
    exact mem_filter.mpr ⟨mem_range.mpr (by dsimp [j]; omega),pr⟩
  have upper := sum_le_sum_of_subset_of_nonneg (f:=g) incl
    (fun m _ _ => mul_nonneg (weight_nonneg j m) (sq_nonneg _))
  rw [sum_image (fun _ _ _ _ e => inj e)] at upper
  change ∑ x, g (f x) ≤ compositeMass v j at upper
  calc _ ≤ ∑ x, 8*g (f x) := by
         apply sum_le_sum
         intro x _
         obtain ⟨lo,hi,_⟩ := bounds x
         have h := mul_le_mul_of_nonneg_right (interior_weight sp lo hi) (sq_nonneg (response v (f x)))
         dsimp [g,j]; linarith
       _ = 8*∑ x, g (f x) := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left upper (by norm_num)

private theorem pair_bounds {s p q : ℕ} (hp : 5*s ≤ p ∧ p ≤ 8*s)
    (hq : 32*s^2 ≤ q ∧ q ≤ 40*s^2) (pp : p.Prime) (qp : q.Prime) :
    160*s^3 ≤ p*q ∧ p*q ≤ 336*s^3 ∧ ¬ (p*q).Prime := by
  refine ⟨?_,?_,Nat.not_prime_mul pp.ne_one qp.ne_one⟩
  · calc _ = (5*s)*(32*s^2) := by ring
         _ ≤ _ := Nat.mul_le_mul hp.1 hq.1
  · calc _ ≤ (8*s)*(40*s^2) := Nat.mul_le_mul hp.2 hq.2
         _ = 320*s^3 := by ring
         _ ≤ _ := by omega

/-- A disjointly indexed supply of prime factors gives a uniform lower bound
for the mass the sieve assigns to composites inside the ordinary tent. -/
theorem composite_rows {M s : ℕ} (sp : 0<s)
    (P : Fin M ↪ ↥(box (5*s) (6*s))) (S : Fin M ↪ ↥(box (6*s) (7*s)))
    (H : Fin M ↪ ↥(box (7*s) (8*s)))
    (Q : (Fin M × Fin M) ↪ ↥(box (32*s^2) (40*s^2)))
    {v : ℕ → ℝ} (hv : Admissible (25*s^2) v) :
    (M:ℝ)^3 ≤ 32 * compositeMass v (400*s^3) := by
  classical
  let p (i : Fin M) := (P i : ℕ)
  let r (i : Fin M) := (S i : ℕ)
  let h (i : Fin M) := (H i : ℕ)
  let q (i : Fin M × Fin M) := (Q i : ℕ)
  have facts {a b : ℕ} (x : ↥(box a b)) : a < x.val ∧ x.val ≤ b ∧ x.val.Prime :=
    let mem := mem_filter.mp x.property
    ⟨(mem_Ioc.mp mem.1).1,(mem_Ioc.mp mem.1).2,mem.2⟩
  have fp (i) : 5*s<p i ∧ p i≤6*s ∧ (p i).Prime := facts (P i)
  have fr (i) : 6*s<r i ∧ r i≤7*s ∧ (r i).Prime := facts (S i)
  have fh (i) : 7*s<h i ∧ h i≤8*s ∧ (h i).Prime := facts (H i)
  have fq (i) : 32*s^2<q i ∧ q i≤40*s^2 ∧ (q i).Prime := facts (Q i)
  have ss : s ≤ s^2 := by simpa [sq] using Nat.le_mul_of_pos_right s sp
  let T := Fin M × Fin M × Fin M
  let f₁ (x : T) := p x.1 * q x.2
  let f₂ (x : T) := r x.2.1 * q (x.1,x.2.2)
  let f₃ (x : T) := h x.2.2 * q (x.1,x.2.1)
  let f₄ (x : T) := p x.1 * r x.2.1 * h x.2.2
  have ip : Function.Injective p := Subtype.val_injective.comp P.injective
  have ir : Function.Injective r := Subtype.val_injective.comp S.injective
  have ih : Function.Injective h := Subtype.val_injective.comp H.injective
  have iq : Function.Injective q := Subtype.val_injective.comp Q.injective
  have bp (i) : 5*s ≤ p i ∧ p i ≤ 8*s := by obtain ⟨a,b,_⟩ := fp i; omega
  have br (i) : 5*s ≤ r i ∧ r i ≤ 8*s := by obtain ⟨a,b,_⟩ := fr i; omega
  have bh (i) : 5*s ≤ h i ∧ h i ≤ 8*s := by obtain ⟨a,b,_⟩ := fh i; omega
  have bq (i) : 32*s^2 ≤ q i ∧ q i ≤ 40*s^2 := ⟨(fq i).1.le,(fq i).2.1⟩
  have row {a : Fin M → ℕ} (ia : Function.Injective a) (apro : ∀ i, (a i).Prime)
      (ab : ∀ i, 5*s ≤ a i ∧ a i ≤ 8*s) :
      Function.Injective (fun z : Fin M × (Fin M × Fin M) => a z.1 * q z.2) := by
    intro x y eq
    have sep : a x.1 < q y.2 := by have u := (ab x.1).2; have l := (fq y.2).1; omega
    obtain ⟨e,d⟩ := sorted_pair (apro _) (apro _) (fq _).2.2 sep eq
    exact Prod.ext (ia e) (iq d)
  have i₁ : Function.Injective f₁ := row ip (fun i => (fp i).2.2) bp
  have i₂ : Function.Injective f₂ := by
    intro ⟨i,j,k⟩ ⟨a,b,c⟩ e
    have d := row ir (fun i => (fr i).2.2) br (a₁:=(j,(i,k))) (a₂:=(b,(a,c))) e
    simp only [Prod.mk.injEq] at d
    exact Prod.ext d.2.1 (Prod.ext d.1 d.2.2)
  have i₃ : Function.Injective f₃ := by
    intro ⟨i,j,k⟩ ⟨a,b,c⟩ e
    have d := row ih (fun i => (fh i).2.2) bh (a₁:=(k,(i,j))) (a₂:=(c,(a,b))) e
    simp only [Prod.mk.injEq] at d
    exact Prod.ext d.2.1 (Prod.ext d.2.2 d.1)
  have i₄ : Function.Injective f₄ := by
    intro ⟨i,j,k⟩ ⟨a,b,c⟩ e
    obtain ⟨u,vv,w⟩ := sorted_triple (fp i).2.2 (fr j).2.2 (fp a).2.2 (fr b).2.2
      (fh c).2.2 ((fp i).2.1.trans_lt (fr b).1) ((fr b).2.1.trans_lt (fh c).1)
      ((fr j).2.1.trans_lt (fh c).1) e
    exact Prod.ext (ip u) (Prod.ext (ir vv) (ih w))
  have b₁ := row_sum f₁ i₁ sp v (fun x => pair_bounds (bp _) (bq _) (fp _).2.2 (fq _).2.2)
  have b₂ := row_sum f₂ i₂ sp v (fun x => pair_bounds (br _) (bq _) (fr _).2.2 (fq _).2.2)
  have b₃ := row_sum f₃ i₃ sp v (fun x => pair_bounds (bh _) (bq _) (fh _).2.2 (fq _).2.2)
  have b₄ := row_sum f₄ i₄ sp v (by
    rintro ⟨i,j,k⟩
    refine ⟨?_,?_,Nat.not_prime_mul (by simp [(fp i).2.2.ne_one])
      (fh k).2.2.ne_one⟩
    · calc 160*s^3 ≤ 210*s^3 := by omega
           _ = (5*s)*(6*s)*(7*s) := by ring
           _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (fp i).1.le (fr j).1.le) (fh k).1.le
    · calc _ ≤ (6*s)*(7*s)*(8*s) := Nat.mul_le_mul (Nat.mul_le_mul (fp i).2.1 (fr j).2.1) (fh k).2.1
           _ = 336*s^3 := by ring)
  have localRows (x : T) : (1:ℝ) ≤ response v (f₁ x)^2 + response v (f₂ x)^2 +
      response v (f₃ x)^2 + response v (f₄ x)^2 := by
    obtain ⟨i,j,k⟩ := x
    have big : 25*s^2 < p i * r j := by
      calc _ = (5*s)*(5*s) := by ring
           _ < _ := (Nat.mul_lt_mul_of_pos_right (fp i).1 (show 0<5*s by omega)).trans_le
             (Nat.mul_le_mul_left _ (br j).1)
    have qr (z) : 25*s^2 < q z := by have l := (fq z).1; omega
    exact four_composite_rows hv (fp i).2.2 (fr j).2.2 (fh k).2.2 (fq _).2.2 (fq _).2.2 (fq _).2.2
      ((fp i).2.1.trans_lt (fr j).1) ((fr j).2.1.trans_lt (fh k).1) big (qr _) (qr _) (qr _)
  have total := sum_le_sum (s:=univ) (fun x _ => localRows x)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul,mul_one,T] at total
  linarith only [total,b₁,b₂,b₃,b₄,show (M:ℝ)^3 = M*(M*M) by ring]

end
end RiemannReduction.DivisorSieve
