import OrdinaryDyadicBase
import Mathlib.NumberTheory.Padics.RingHoms

/-! Ordinary unramified quadratic characters of a Galois subgroup factor
through its maximal unramified abelian pro-2 quotient. -/

noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Two

namespace RiemannReduction.Mizusawa

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- The kernels defining the unramified abelian pro-2 quotient. Openness and
2-power index specify finite continuous 2-quotients. The last two conditions
kill commutators and the chosen inertia elements. -/
def OrdinaryKernel (U : Subgroup Γ) (S : Set Γ) (N : Subgroup U) : Prop :=
  N.Normal ∧ IsOpen (N : Set U) ∧ (∃ n : ℕ, N.index = 2 ^ n) ∧
    (∀ a b : U, a * b * a⁻¹ * b⁻¹ ∈ N) ∧ (∀ u : U, u.val ∈ S → u ∈ N)

def ordinaryKernel (U : Subgroup Γ) (S : Set Γ) : Subgroup U :=
  ⨅ N : {N : Subgroup U // OrdinaryKernel U S N}, N.val

instance (U : Subgroup Γ) (S : Set Γ) : (ordinaryKernel U S).Normal :=
  Subgroup.normal_iInf_normal fun N => N.property.1

/-- For a profinite Galois group and its inertia set, this is the ordinary
unramified abelian pro-2 Galois group, presented by its finite quotients. -/
abbrev OrdinaryQuotient (U : Subgroup Γ) (S : Set Γ) :=
  U ⧸ ordinaryKernel U S

variable {U : Subgroup Γ} {S : Set Γ}

private def characterHom (φ : CharOff U S 2) : U →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (φ.val x)
  map_one' := by
    have h := φ.property.2.1 1 1
    rw [one_mul] at h
    exact congrArg Multiplicative.ofAdd (by simpa using h.symm : φ.val 1 = 0)
  map_mul' := fun a b => congrArg Multiplicative.ofAdd (φ.property.2.1 a b)

private theorem characterKernel (φ : CharOff U S 2) :
    OrdinaryKernel U S (characterHom φ).ker := by
  let f := characterHom φ
  refine ⟨f.normal_ker, φ.property.1.isOpen_fiber 0, ?_, ?_, φ.property.2.2⟩
  · rw [Subgroup.index_ker]
    have h : Nat.card f.range ∣ 2 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card] using f.range.card_subgroup_dvd_card
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro a b
    change f (a * b * a⁻¹ * b⁻¹) = 1
    simp [mul_assoc]

/-- A quadratic character trivial at the specified inertia descends to the
ordinary quotient, and its pullback is the original character. -/
def descend (φ : CharOff U S 2) : OrdinaryQuotient U S →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (characterHom φ)
    (iInf_le (fun N : {N : Subgroup U // OrdinaryKernel U S N} => N.val)
      ⟨(characterHom φ).ker, characterKernel φ⟩)

@[simp] theorem descend_mk (φ : CharOff U S 2) (u : U) :
    descend φ (QuotientGroup.mk u) = Multiplicative.ofAdd (φ.val u) := rfl

theorem descend_injective : Function.Injective (descend (U := U) (S := S)) := by
  intro φ ψ h
  apply Subtype.ext
  funext u
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h (QuotientGroup.mk u))

/-- Every additive map from the 2-adic integers to the group of order two
is determined by its value at one. This only uses reduction modulo two. -/
private theorem padic_ext {f g : ℤ_[2] →+ ZMod 2} (h : f 1 = g 1) : f = g := by
  ext x
  let n := (PadicInt.toZMod x).val
  have mem := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at mem
  obtain ⟨w, hw⟩ := mem
  have hx : x = n • (1 : ℤ_[2]) + (w + w) := by
    change x - (n : ℤ_[2]) = 2 * w at hw
    simpa [nsmul_eq_mul, two_mul] using (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
  have twice (a : ZMod 2) : a + a = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  simp only [hx, map_add, map_nsmul, twice, add_zero, h]

/-- Coordinate evaluations distinguish all homomorphisms from a finite free
2-adic module to the group of order two. -/
theorem evaluations_injective (r : ℕ) :
    Function.Injective (fun f : (Fin r → ℤ_[2]) →+ ZMod 2 =>
      fun i : Fin r => f (Pi.single i 1)) := by
  intro f g h
  apply AddMonoidHom.ext
  intro x
  have coordinate (i : Fin r) :
      f.comp (AddMonoidHom.single (fun _ : Fin r => ℤ_[2]) i) =
      g.comp (AddMonoidHom.single (fun _ : Fin r => ℤ_[2]) i) :=
    padic_ext (congrFun h i)
  calc
    f x = ∑ i, f (Pi.single i (x i)) := by rw [← map_sum, Finset.univ_sum_single]
    _ = ∑ i, g (Pi.single i (x i)) := by
      exact Finset.sum_congr rfl fun i _ => DFunLike.congr_fun (coordinate i) (x i)
    _ = g x := by rw [← map_sum, Finset.univ_sum_single]

/-- A free rank-r ordinary module gives at most 2^r everywhere-unramified
quadratic characters. An abstract group isomorphism suffices. -/
theorem character_bound_of_free {r : ℕ}
    (e : OrdinaryQuotient U S ≃* Multiplicative (Fin r → ℤ_[2])) :
    CardLe (CharOff U S 2) (2 ^ r) := by
  let pull (f : OrdinaryQuotient U S →* Multiplicative (ZMod 2)) :
      (Fin r → ℤ_[2]) →+ ZMod 2 := (f.comp e.symm.toMonoidHom).toAdditive
  have inj : Function.Injective pull := by
    intro f g h
    apply DFunLike.ext
    intro x
    have eq := DFunLike.congr_fun h (e x)
    change f (e.symm (e x)) = g (e.symm (e x)) at eq
    simpa using eq
  have values : CardLe (Fin r → ZMod 2) (2 ^ r) := ⟨inferInstance, by simp [Nat.card_eq_fintype_card]⟩
  exact CardLe.of_injective values _ ((evaluations_injective r).comp (inj.comp descend_injective))

end RiemannReduction.Mizusawa
