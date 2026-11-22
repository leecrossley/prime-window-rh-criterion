import BiquadraticDescent
import OrdinaryDyadicBase
import RationalDyadicInertia

/-! Bounding the ordinary biquadratic tower using quadratic characters of the
pure cyclotomic tower that may ramify only over the two auxiliary primes. -/
noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
namespace RiemannReduction.GaussianTower
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def RayRank (V : Subgroup (G ℚ Ω)) (q d r : ℕ) : Prop :=
  CardLe (CharOff V (ineOff ℚ Ω (q*d)) 2) (2^r)

/-- The common kernel of both quadratic characters has no further ramification
over their product. This argument also applies at a single finite level. -/
theorem descent_at_level (V : Subgroup (G ℚ Ω)) {q d r : ℕ}
    (hq : q.Prime) (hq8 : q%8 = 3) (hd : d.Prime) (hd16 : d%16 = 7)
    (base : CardLe (CharOff V (ineOff ℚ Ω 1) 2) 1) (ray : RayRank Ω V q d (r+2)) :
    CardLe (CharOff ((abU Ω (AbF.quad q) ⊓ abU Ω (AbF.quad d)) ⊓ V) (ineOff ℚ Ω 1) 2)
      (2^(2*r+1)) := by
  let A := abU Ω (AbF.quad q)
  let B := abU Ω (AbF.quad d)
  have D := (abBasic Ω).2.1
  have ia : A.index ∣ 2 := (D _).1 ▸ degBasic.2.2.1 q hq
  have ib : B.index ∣ 2 := (D _).1 ▸ degBasic.2.2.1 d hd
  have awayAt (p : ℕ) (hp : p.Prime) (C : ValuationSubring Ω) (hv : ¬ C.valuation (p : Ω) < 1) :
      Ine (F := ℚ) C ≤ abU Ω (AbF.quad p) := by
    have hm : (AbF.quad p).m = p := max_eq_left hp.pos
    exact (ineChar Ω _ C (by rwa [hm])).trans (D _).2.2.2
  apply RiemannReduction.QuadraticDescent.biquadratic_rank V A B _ _ r
    (D _).2.2.1 (D _).2.2.1 ia ib (fun v _ => (ineConj ℚ Ω v).2.2 1) _ _ _ _ base ray
  · rintro g ⟨C,one,member⟩
    exact ⟨C,one,(Ine (F := ℚ) C).mul_mem member member⟩
  · rintro g ⟨C,_,member⟩
    exact ⟨C,by simp,member⟩
  · rintro g ⟨C,outside,member⟩ _
    have lo (j : ℕ) : C.valuation (j : Ω) ≤ 1 :=
      (C.valuation_le_one_iff _).2 (natCast_mem C j)
    rw [Nat.cast_mul,map_mul] at outside
    have nq : ¬ C.valuation (q : Ω) < 1 := fun h => outside (lt_of_le_of_lt (mul_le_of_le_one_right' (lo d)) h)
    have nd : ¬ C.valuation (d : Ω) < 1 := fun h => outside (lt_of_le_of_lt (mul_le_of_le_one_left' (lo q)) h)
    exact ⟨awayAt q hq C nq member,awayAt d hd C nd member⟩
  · rintro g ⟨C,_,member⟩ _
    by_cases atQ : C.valuation (q : Ω) < 1
    · right
      have q2 : q.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
      have qd : q.Coprime d := (Nat.coprime_primes hq hd).mpr (by omega)
      have cop : q.Coprime (2 * (AbF.quad d).m) := by
        rw [show (AbF.quad d).m = d from max_eq_left hd.pos]
        exact q2.mul_right qd
      have found := (ineTwo Ω (AbF.quad d) q C cop atQ member).1
      rw [withI,(abBasic Ω).1] at found
      exact found.1
    · exact Or.inl (awayAt q hq C atQ member)

theorem pure_char_one : CardLe (CharOff (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) (ineOff ℚ Ω 1) 2) 1 := by
  have h := pure_rank_zero Ω
  rw [← ordinary_tower Ω] at h
  simpa only [XRk,xDual_one,pow_zero] using h

theorem ordinary_ray_six {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d) :
    RayRank Ω (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) q d 6 := by
  let M := AbF.ofChar PChar.one
  obtain ⟨hq,hq8,hd,hd16,cop⟩ := pair
  have q2 : q.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
  have d2 : d.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
  have first := charStep ℚ Ω 2 _ 1 q _ _ q2 (orbTwo Ω M q 2 hq (Or.inl ⟨hq8,rfl⟩))
    (fun C hC => ineTwo Ω M q C (q2.mul_right (Nat.Coprime.coprime_mul_right cop)) hC)
    (pure_char_one Ω)
  have both := charStep ℚ Ω 2 _ (1*q) d _ _ d2 (orbTwo Ω M d 4 hd (Or.inr ⟨hd16,rfl⟩))
    (fun C hC => ineTwo Ω M d C (d2.mul_right (Nat.Coprime.coprime_mul_left cop)) hC) first
  simpa only [RayRank,M,ordinary_degree,Nat.mul_one,Nat.one_mul,← pow_add] using both

theorem host_rank_of_ray {q d r : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (ray : RayRank Ω (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) q d (r+2)) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) (2*r+1) := by
  obtain ⟨hq,hq8,hd,hd16,_⟩ := pair
  let M := AbF.ofChar PChar.one
  let V := cycU 2 (abU Ω (withI M))
  have bound := descent_at_level Ω V hq hq8 hd hd16 (pure_char_one Ω) ray
  have field_eq : cycU 2 (abU Ω (base2 M q d)) =
      (abU Ω (AbF.quad q) ⊓ abU Ω (AbF.quad d)) ⊓ V := by
    ext g
    simp only [cycU,base2,(abBasic Ω).1,V,Subgroup.mem_inf]
    tauto
  change CardLe _ _
  rw [xDual_one,field_eq]
  exact bound

theorem host_rank_nine {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 9 :=
  host_rank_of_ray Ω (r := 4) pair (ordinary_ray_six Ω pair)

theorem host_rank_three_of_eight_ray_characters {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (ray : RayRank Ω (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) q d 3) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 3 :=
  host_rank_of_ray Ω (r := 1) pair ray

#print axioms host_rank_nine
#print axioms host_rank_three_of_eight_ray_characters
end RiemannReduction.GaussianTower
