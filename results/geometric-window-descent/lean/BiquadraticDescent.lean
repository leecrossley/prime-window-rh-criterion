import QuadraticGenus

/-! Descent through the diagonal quadratic subfield of a biquadratic extension.
The two quadratic characters have disjoint ramification. Their common kernel is
unramified over the kernel of their product. -/
noncomputable section
open UpperTheory.V.Two
namespace RiemannReduction.QuadraticDescent
variable {Γ : Type} [Group Γ]

private theorem character_of_index (A : Subgroup Γ) (hA : A.index ∣ 2) :
    ∃ a : Γ →* Multiplicative (ZMod 2), a.ker = A := by
  classical
  rcases (Nat.dvd_prime Nat.prime_two).1 hA with h | h
  · rw [Subgroup.index_eq_one] at h
    exact ⟨1,by rw [h]; simp⟩
  let a : Γ →* Multiplicative (ZMod 2) :=
    { toFun g := Multiplicative.ofAdd (if g ∈ A then 0 else 1)
      map_one' := by simp
      map_mul' x y := by
        apply Multiplicative.toAdd.injective
        change (if x*y ∈ A then (0 : ZMod 2) else 1) =
          (if x ∈ A then 0 else 1) + (if y ∈ A then 0 else 1)
        have hab := Subgroup.mul_mem_iff_of_index_two h (a := x) (b := y)
        by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx,hy,hab]
        decide }
  refine ⟨a,?_⟩
  ext g
  change Multiplicative.ofAdd (if g ∈ A then (0 : ZMod 2) else 1) = 1 ↔ g ∈ A
  by_cases h : g ∈ A <;> simp [h]

private theorem index_bit (a : Γ →* Multiplicative (ZMod 2)) : a.ker.index ∣ 2 := by
  rw [Subgroup.index_ker]
  have h : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  exact dvd_trans a.range.card_subgroup_dvd_card (by rw [h])

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- If the permitted ramified character rank is s ≥ 2, then the ordinary
unramified character rank over the biquadratic field is at most 2s−3. -/
theorem biquadratic_rank (V A B : Subgroup Γ) (S T : Set Γ) (r : ℕ)
    (hA : IsOpen (A : Set Γ)) (hB : IsOpen (B : Set Γ))
    (ia : A.index ∣ 2) (ib : B.index ∣ 2)
    (stable : ∀ v ∈ V, ∀ s ∈ S, v⁻¹*s*v ∈ S) (squares : ∀ s ∈ S, s*s ∈ S)
    (incl : T ⊆ S) (away : ∀ g ∈ T, g ∈ V → g ∈ A ∧ g ∈ B)
    (disjoint : ∀ g ∈ S, g ∈ V → g ∈ A ∨ g ∈ B)
    (base : CardLe (CharOff V S 2) 1) (ray : CardLe (CharOff V T 2) (2^(r+2))) :
    CardLe (CharOff ((A ⊓ B) ⊓ V) S 2) (2^(2*r+1)) := by
  classical
  obtain ⟨a,ha⟩ := character_of_index A ia
  obtain ⟨b,hb⟩ := character_of_index B ib
  let diagonal := (a*b).ker
  let W := diagonal ⊓ V
  let U := A ⊓ W
  have adiag {g : Γ} : g ∈ diagonal ↔ a g * b g = 1 := Iff.rfl
  have av {g : Γ} : g ∈ A ↔ a g = 1 := ha ▸ Iff.rfl
  have bv {g : Γ} : g ∈ B ↔ b g = 1 := hb ▸ Iff.rfl
  have both : A ⊓ B ≤ diagonal := by
    rintro g ⟨ga,gb⟩
    exact adiag.mpr (by rw [av.mp ga,bv.mp gb,one_mul])
  have openDiag := Subgroup.isOpen_mono both (hA.inter hB)
  have WD : IsOpen (W.subgroupOf V : Set V) := by
    change IsOpen ((diagonal ⊓ V).subgroupOf V : Set V)
    rw [Subgroup.inf_subgroupOf_right,Subgroup.coe_subgroupOf]
    exact openDiag.preimage continuous_subtype_val
  have wi : W.relIndex V ∣ 2 := by
    change (diagonal ⊓ V).relIndex V ∣ 2
    rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_dvd_index_of_normal diagonal V).trans (index_bit (a*b))
  have off (g : Γ) (hT : g ∈ T) (hv : g ∈ V) : g ∈ W := ⟨both (away g hT hv),hv⟩
  have lower := quadratic_genus_bound W V S T (r+1) inf_le_right WD wi
    stable squares incl off base ray
  have openUpper : IsOpen (U.subgroupOf W : Set W) := by
    change IsOpen ((A ⊓ W).subgroupOf W : Set W)
    rw [Subgroup.inf_subgroupOf_right,Subgroup.coe_subgroupOf]
    exact hA.preimage continuous_subtype_val
  have ui : U.relIndex W ∣ 2 := by
    change (A ⊓ W).relIndex W ∣ 2
    rw [Subgroup.inf_relIndex_right,← ha]
    exact (Subgroup.relIndex_dvd_index_of_normal a.ker W).trans (index_bit a)
  have allInertia (g : Γ) (hS : g ∈ S) (hw : g ∈ W) : g ∈ U := by
    have eq := adiag.mp hw.1
    rcases disjoint g hS hw.2 with ga | gb
    · exact ⟨ga,hw⟩
    · rw [bv.mp gb,mul_one] at eq
      exact ⟨av.mpr eq,hw⟩
  have upper := rank_le_twice_sub_one U W S r inf_le_right openUpper ui
    (fun v hv => stable v hv.2) allInertia lower
  have same : U = (A ⊓ B) ⊓ V := by
    ext g
    constructor
    · rintro ⟨ga,diag,gv⟩
      have eq := adiag.mp diag
      rw [av.mp ga,one_mul] at eq
      exact ⟨⟨ga,bv.mpr eq⟩,gv⟩
    · rintro ⟨⟨ga,gb⟩,gv⟩
      exact ⟨ga,both ⟨ga,gb⟩,gv⟩
  exact Eq.mp (congrArg (fun H : Subgroup Γ => CardLe (CharOff H S 2) (2^(2*r+1))) same) upper

#print axioms biquadratic_rank
end RiemannReduction.QuadraticDescent
