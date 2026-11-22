import CofinalRayLayers

/-! A finite-level criterion for the three-generator bound using the values
of the actual ray characters on six representatives of the tame inertia. -/
noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise
namespace RiemannReduction.GaussianTower
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

structure TameSites (V : Subgroup (G ℚ Ω)) (q d : ℕ) where
  place : Fin 3 → Bool → ValuationSubring Ω
  odd : ∀ i j, ¬ (place i j).valuation (2 : Ω) < 1
  inside : ∀ i j, Ine (F := ℚ) (place i j) ≤ V
  covers : ∀ A : ValuationSubring Ω, A.valuation ((q*d : ℕ) : Ω) < 1 →
    ∃ i j, ∃ v : V, v.1 • place i j = A

namespace TameSites
variable {V : Subgroup (G ℚ Ω)} {q d : ℕ} (S : TameSites V q d)

private def generator (i : Fin 3) (j : Bool) := (tameGen ℚ Ω 2 (S.place i j) (S.odd i j)).choose

def value (χ : CharOff V (ineOff ℚ Ω (q*d)) 2) (i : Fin 3) (j : Bool) : ZMod 2 :=
  χ.1 ⟨(S.generator i j).1, S.inside i j (S.generator i j).2⟩

def pairSum (χ : CharOff V (ineOff ℚ Ω (q*d)) 2) (i : Fin 3) : ZMod 2 :=
  S.value χ i false + S.value χ i true

/-- Vanishing at the chosen tame generator detects precisely vanishing on the full inertia. -/
theorem value_zero_iff (χ : CharOff V (ineOff ℚ Ω (q*d)) 2) (i : Fin 3) (j : Bool) :
    S.value χ i j = 0 ↔ ∀ g : Ine (F := ℚ) (S.place i j), χ.1 ⟨g.1,S.inside i j g.2⟩ = 0 := by
  let inc : Ine (F := ℚ) (S.place i j) → V := fun t => ⟨t.1,S.inside i j t.2⟩
  refine ⟨fun h => (tameGen ℚ Ω 2 (S.place i j) (S.odd i j)).choose_spec (χ.1 ∘ inc)
    (χ.2.1.comp_continuous (Continuous.subtype_mk continuous_subtype_val _))
    (fun a b => χ.2.2.1 (inc a) (inc b)) h, fun h => h (S.generator i j)⟩

/-- The three unit-sign rows in paired coordinates, with the two primes
over d ordered so that the real unit has signs (1,1,0). -/
def UnitRelations : Prop :=
  ∀ χ : CharOff V (ineOff ℚ Ω (q*d)) 2,
    S.pairSum χ 0 + S.pairSum χ 1 = 0 ∧
    S.pairSum χ 0 + S.pairSum χ 2 = 0 ∧
    S.pairSum χ 0 + S.pairSum χ 1 + S.pairSum χ 2 = 0

private theorem detects (base : CardLe (CharOff V (ineOff ℚ Ω 1) 2) 1) :
    Function.Injective S.value := by
  intro φ ψ eq
  let χ : V → ZMod 2 := φ.1 - ψ.1
  obtain ⟨lc,add,off⟩ := (φ-ψ).2
  have unram : χ ∈ CharOff V (ineOff ℚ Ω 1) 2 := by
    refine ⟨lc,add,fun u hu => ?_⟩
    obtain ⟨A,_,member⟩ := hu
    by_cases bad : A.valuation ((q*d : ℕ) : Ω) < 1
    · obtain ⟨i,j,v,rfl⟩ := S.covers A bad
      let B := S.place i j
      let embed : Ine (F := ℚ) B → V := fun t => ⟨t.1,S.inside i j t.2⟩
      have cont : Continuous embed := Continuous.subtype_mk continuous_subtype_val _
      have loc : IsLocallyConstant (χ ∘ embed) := lc.comp_continuous cont
      have mul (a b : Ine (F := ℚ) B) : (χ ∘ embed) (a*b) = (χ ∘ embed) a + (χ ∘ embed) b := add (embed a) (embed b)
      have atGen : (χ ∘ embed) (S.generator i j) = 0 := sub_eq_zero.mpr (congrFun (congrFun eq i) j)
      have inB := (ineConj ℚ Ω v.1).1 B u member
      have all := (tameGen ℚ Ω 2 B (S.odd i j)).choose_spec (χ ∘ embed) loc mul atGen ⟨_,inB⟩
      have conj : χ (v⁻¹*u*v) = 0 := all
      change ∀ a b, χ (a*b) = χ a + χ b at add
      have identity : χ 1 = 0 := by have e := add 1 1; rw [mul_one] at e; linear_combination -e
      have inv : χ v⁻¹ + χ v = 0 := by rw [← add,inv_mul_cancel,identity]
      rw [add,add] at conj
      linear_combination conj - inv
    · exact off u ⟨A,bad,member⟩
  have : Finite (CharOff V (ineOff ℚ Ω 1) 2) := base.1
  have subs : Subsingleton (CharOff V (ineOff ℚ Ω 1) 2) := Finite.card_le_one_iff_subsingleton.mp base.2
  have zero := congrArg Subtype.val (subs.elim (⟨χ,unram⟩ : CharOff V (ineOff ℚ Ω 1) 2) 0)
  exact Subtype.ext (sub_eq_zero.mp zero)

theorem ray_rank_three (base : CardLe (CharOff V (ineOff ℚ Ω 1) 2) 1)
    (relations : S.UnitRelations) : RayRank Ω V q d 3 := by
  let f (χ : CharOff V (ineOff ℚ Ω (q*d)) 2) (i : Fin 3) := S.value χ i false
  have zero (χ : CharOff V (ineOff ℚ Ω (q*d)) 2) (i : Fin 3) : S.pairSum χ i = 0 := by
    obtain ⟨ab,ac,abc⟩ := relations χ
    fin_cases i
    · change S.pairSum χ 0 = 0
      linear_combination ac - abc + ab
    · change S.pairSum χ 1 = 0
      linear_combination abc - ac
    · change S.pairSum χ 2 = 0
      linear_combination abc - ab
  have inject : Function.Injective f := by
    intro φ ψ e
    apply S.detects base
    funext i j
    have l : S.value φ i false = S.value ψ i false := congrFun e i
    cases j
    · exact l
    · have a := zero φ i
      have b := zero ψ i
      unfold pairSum at a b
      linear_combination a - b - l
  exact ⟨Finite.of_injective f inject, (Nat.card_le_card_of_injective f inject).trans_eq
    (by rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin])⟩
end TameSites

theorem host_rank_three_of_cofinal_unit_relations {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (witness : ∀ start : ℕ, ∃ n ≥ start, ∃ S : TameSites (galChar Ω (2^n)).ker q d, S.UnitRelations) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 3 := by
  apply host_rank_of_cofinal_finite_ray Ω (r := 1) pair
  intro start
  obtain ⟨n,late,S,hs⟩ := witness (max 1 start)
  exact ⟨n,(le_max_right _ _).trans late, S.ray_rank_three (pure_layer_one Ω (lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans late))) hs⟩

#print axioms host_rank_three_of_cofinal_unit_relations
end RiemannReduction.GaussianTower
