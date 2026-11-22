import RealUnitPrimeSigns

/-! The cubic automorphism exchanges the two residue-sign classes over d. -/
noncomputable section
open NumberField
open scoped Pointwise
namespace RiemannReduction.UnitSigns
open UnitResidue CyclotomicUnits

abbrev Above (K : Type*) [Field K] (p : ℕ) := (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)
variable {K : Type*} [Field K] [NumberField K] {j : ℕ} [IsCyclotomicExtension {2^(j+4)} ℚ K]

private theorem cube_automorphism (z : (𝓞 K)ˣ) (hz : IsPrimitiveRoot (z : 𝓞 K) (2^(j+4))) :
    ∃ σ : Gal(K/ℚ), (galRestrict ℤ ℚ K (𝓞 K) σ) (realUnitFactor z) = realUnitFactor (z^3) := by
  let N := 2^(j+4)
  have hn : 3 < N := by dsimp [N]; rw [pow_add]; have := Nat.two_pow_pos j; omega
  let a := ZMod.unitOfCoprime 3 ((by decide : Nat.Coprime 3 2).pow_right (j+4))
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm a
  let f := galRestrict ℤ ℚ K (𝓞 K) σ
  have rootK : (algebraMap (𝓞 K) K (z : 𝓞 K)) ^ N = 1 := by rw [← map_pow,hz.pow_eq_one,map_one]
  have act := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ rootK
  have exp : ((IsCyclotomicExtension.Rat.galEquivZMod N K σ).val).val = 3 := by
    rw [show IsCyclotomicExtension.Rat.galEquivZMod N K σ = a from (IsCyclotomicExtension.Rat.galEquivZMod N K).apply_symm_apply a,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hn]
  rw [exp] at act
  have images : Units.map f.toMonoidHom z = z^3 := by
    apply Units.ext
    apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    change algebraMap (𝓞 K) K (f (z : 𝓞 K)) = algebraMap (𝓞 K) K ((z : 𝓞 K)^3)
    rw [map_pow,algebraMap_galRestrict_apply]
    exact act
  refine ⟨σ,?_⟩
  change f (realUnitFactor z) = _
  rw [← images]
  simp only [realUnitFactor,map_add,map_one,← map_inv]
  rfl

private theorem square_transport {p : ℕ} (σ : Gal(K/ℚ)) (P : Above K p) (x : 𝓞 K) :
    squareAt (σ • P).1 ((galRestrict ℤ ℚ K (𝓞 K) σ) x) ↔ squareAt P.1 x := by
  let f := galRestrict ℤ ℚ K (𝓞 K) σ
  let e := Ideal.quotientEquiv P.1 (σ • P).1 f.toRingEquiv
    (Ideal.coe_smul_primesOver_eq_map_galRestrict ℚ K σ P)
  change IsSquare (e (Ideal.Quotient.mk P.1 x)) ↔ _
  refine ⟨?_,fun h => h.map e⟩
  rintro ⟨b,hb⟩
  exact ⟨e.symm b,by rw [← map_mul,← hb,e.symm_apply_apply]⟩

/-- The actual four primes above d split two and two by the sign of the real unit.
The other real unit has the complementary signs at every one of those primes. -/
theorem row_counts {q d : ℕ} (hq : q.Prime) (q8 : q%8=3) (hd : d.Prime) (d16 : d%16=7)
    (z : (𝓞 K)ˣ) (hz : IsPrimitiveRoot (z : 𝓞 K) (2^(j+4))) :
    Nat.card (Above K q) = 2 ∧
    Nat.card {P : Above K d // squareAt P.1 (realUnitFactor z)} = 2 ∧
    Nat.card {P : Above K d // ¬ squareAt P.1 (realUnitFactor z)} = 2 := by
  classical
  obtain ⟨qc,dc⟩ := prime_counts (j := j) hq q8 hd d16 K
  change Nat.card (Above K q) = 2 at qc
  change Nat.card (Above K d) = 4 at dc
  have : Nonempty (Above K q) := Nat.card_pos_iff.mp (by omega : 0 < Nat.card (Above K q)) |>.1
  let P := Classical.choice this
  let positive := fun Q : Above K d => squareAt Q.1 (realUnitFactor z)
  obtain ⟨σ,hσ⟩ := cube_automorphism z hz
  let move : Equiv.Perm (Above K d) := MulAction.toPerm σ
  have swap (Q : Above K d) : positive Q ↔ ¬ positive (move Q) := by
    have a := square_transport σ Q (realUnitFactor z)
    rw [hσ] at a
    have b := (signs_at_primes hq q8 hd d16 P.1 (move Q).1 z hz).2
    change squareAt Q.1 (realUnitFactor z) ↔ ¬ squareAt (move Q).1 (realUnitFactor z)
    change squareAt (move Q).1 (realUnitFactor (z^3)) ↔ _ at a
    tauto
  let e := Equiv.subtypeEquiv (p := positive) (q := fun Q => ¬ positive Q) move swap
  have eq := Nat.card_congr e
  have : Finite (Above K d) := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card (Above K d))).2
  have sum := Nat.card_congr (Equiv.sumCompl positive)
  rw [Nat.card_sum,dc] at sum
  change Nat.card (Subtype positive) + Nat.card {Q // ¬ positive Q} = 4 at sum
  change Nat.card (Subtype positive) = Nat.card {Q // ¬ positive Q} at eq
  exact ⟨qc, by change Nat.card (Subtype positive) = 2; omega,
    by change Nat.card {Q // ¬ positive Q} = 2; omega⟩

end RiemannReduction.UnitSigns
