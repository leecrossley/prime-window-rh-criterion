import MizusawaCharacters
import MizusawaGenusField
import NineIntegralTower

/-! Mizusawa, Lemma 4.2, in the Galois-quotient presentation of X(K∞),
and its use as the rank input to the geometric window. -/

noncomputable section

open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base
  UpperTheory.V.Kum UpperTheory.V.Two UpperTheory.V.Win

namespace RiemannReduction.Mizusawa

/-- The rank-three clause of Mizusawa's Lemma 4.2 for the genus field. The
isomorphism retains only the underlying groups of his free 2-adic modules. -/
def RankThree : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (q d : ℕ), q.Prime → q % 8 = 3 → d.Prime → d % 16 = 7 →
    ∀ a b c : Ω, a ^ 2 = (q : Ω) → b ^ 2 = (d : Ω) → c ^ 2 = -((q : Ω) * d) →
    Nonempty (OrdinaryQuotient (genusHost Ω a b c) (ineOff ℚ Ω 1) ≃*
      Multiplicative (Fin 3 → ℤ_[2]))

theorem host_rank_three (rank : RankThree) (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 3 := by
  obtain ⟨hq, hq8, hd, hd16, _⟩ := pair
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (q : Ω) (by decide : 0 < 2)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (d : Ω) (by decide : 0 < 2)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-((q : Ω) * d)) (by decide : 0 < 2)
  obtain ⟨e⟩ := rank Ω q d hq hq8 hd hd16 a b c ha hb hc
  rw [XRk, xDual_one, host_eq_radicals Ω hq hq8 hd hd16 a b ha hb,
    radical_eq_genus Ω hq hd a b c ha hb hc]
  exact character_bound_of_free e

theorem host_tower_three (rank : RankThree) {q d : ℕ}
    (pair : PrimePair (AbF.ofChar PChar.one).m q d) (L : Type) [Field L] [NumberField L]
    (field : IsAbField (base2 (AbF.ofChar PChar.one) q d) L) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) 3 ∧ Tower.IsTower 2 L 3 := by
  have := isAlgClosure_rat L (AlgebraicClosure L)
  exact RiemannReduction.GaussianTower.host_tower_of_rank (by decide) L field
    (host_rank_three rank (AlgebraicClosure L) pair)

theorem ordinary_three_input (rank : RankThree) (bounds : TowerBound) :
    RiemannReduction.GaussianTower.TwoInputAt (AbF.ofChar PChar.one) := by
  refine ⟨3, fun q d pair => ?_⟩
  obtain ⟨L, _, _, field⟩ := abExists (base2 (AbF.ofChar PChar.one) q d)
  exact ⟨L, inferInstance, inferInstance, twoBase _ q d pair L field,
    bounds 2 L 3 (host_tower_three rank pair L field).2⟩

#print axioms host_rank_three
#print axioms ordinary_three_input

end RiemannReduction.Mizusawa
