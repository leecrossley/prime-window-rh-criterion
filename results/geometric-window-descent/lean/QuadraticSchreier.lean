import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.InvTwo

/-! Schreier's index-two bound for continuous mod-two characters with prescribed
inertia conditions. The image of the conjugation difference extends across
the index-two subgroup, with the value at a coset representative fixed to zero. -/
noncomputable section
open UpperTheory.V.Two
namespace RiemannReduction.QuadraticDescent
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem sign_character (U V : Subgroup Γ) (S : Set Γ)
    (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hS : ∀ s ∈ S, s ∈ V → s ∈ U) (σ : V) (hn : σ.1 ∉ U) :
    ∃ ε : CharOff V S 2, ε.1 σ = 1 ∧ ∀ v : V, v.1 ∈ U → ε.1 v = 0 := by
  classical
  let H := U.subgroupOf V
  have hcl : IsClosed (H : Set V) := H.isClosed_of_isOpen ho
  let ε : V → ZMod 2 := fun v => if v ∈ H then 0 else 1
  have hmem : ε ∈ CharOff V S 2 := by
    refine ⟨?_, ?_, fun v hv => if_pos (hS _ hv v.2)⟩
    · rw [IsLocallyConstant.iff_isOpen_fiber_apply]
      intro x
      by_cases hx : x ∈ H
      · have openH : IsOpen (H : Set V) := ho
        convert openH using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε,hx,hv]
      · convert hcl.isOpen_compl using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε,hx,hv]
    · intro a b
      have hab := Subgroup.mul_mem_iff_of_index_two (H := H) hi (a := a) (b := b)
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;>
        simp [ε,ha,hb,hab]
      decide
  exact ⟨⟨ε,hmem⟩, if_neg hn, fun _ hv => if_pos hv⟩

theorem card_of_normalized_extensions (U V : Subgroup Γ) (S : Set Γ)
    (sub : U ≤ V) (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hS : ∀ s ∈ S, s ∈ V → s ∈ U) (σ : V) (hn : σ.1 ∉ U)
    {X : Type} (read : X → U → ZMod 2) (separates : Function.Injective read)
    (extensions : ∀ x : X, ∃ ψ : CharOff V S 2,
      ψ.1 σ = 0 ∧ ∀ u : U, ψ.1 ⟨u.1,sub u.2⟩ = read x u)
    {n : ℕ} (bound : CardLe (CharOff V S 2) n) : CardLe (X × ZMod 2) n := by
  choose extend extσ extU using extensions
  obtain ⟨ε,signσ,signU⟩ := sign_character U V S ho hi hS σ hn
  let code (z : X × ZMod 2) : CharOff V S 2 := extend z.1 + z.2 • ε
  apply CardLe.of_injective bound code
  rintro ⟨y,a⟩ ⟨z,b⟩ eq
  have val (v : V) : (extend y).1 v + a * ε.1 v = (extend z).1 v + b * ε.1 v :=
    congrArg (fun φ : CharOff V S 2 => φ.1 v) eq
  have ab := val σ
  rw [extσ,extσ,signσ] at ab
  refine Prod.ext (separates ?_) (by simpa using ab)
  funext u
  simpa only [extU,signU ⟨u.1,sub u.2⟩ u.2,mul_zero,add_zero] using val ⟨u.1,sub u.2⟩

omit [IsTopologicalGroup Γ] in
theorem char_inner {U : Subgroup Γ} {S : Set Γ} (χ : CharOff U S 2) (s u : U) :
    χ.1 (s⁻¹*u*s) = χ.1 u := by
  have add := χ.2.2.1
  have zero : χ.1 1 = 0 := by simpa using (add 1 1).symm
  have inv : χ.1 s⁻¹ + χ.1 s = 0 := by rw [← add,inv_mul_cancel,zero]
  rw [add,add]
  linear_combination inv

private theorem exact_two (U V : Subgroup Γ) (S : Set Γ) (n : ℕ) (sub : U ≤ V)
    (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (stable : ∀ v ∈ V, ∀ s ∈ S, v⁻¹*s*v ∈ S) (hS : ∀ s ∈ S, s ∈ V → s ∈ U)
    (bound : CardLe (CharOff V S 2) n) :
    Finite (CharOff U S 2) ∧ 2 * Nat.card (CharOff U S 2) ≤ n * n := by
  classical
  have not_le : ¬ V ≤ U := fun h => by
    have h1 := Subgroup.relIndex_eq_one.2 h
    omega
  obtain ⟨σ,hσ,hn⟩ := SetLike.not_le_iff_exists.1 not_le
  have idx : (U.subgroupOf V).index = 2 := hi
  have normal := Subgroup.normal_of_index_eq_two idx
  have preserve (u : U) : σ⁻¹*u.1*σ ∈ U := by
    have e := normal.conj_mem (⟨u.1,sub u.2⟩ : V) (Subgroup.mem_subgroupOf.2 u.2) (⟨σ,hσ⟩ : V)⁻¹
    simpa [Subgroup.mem_subgroupOf] using e
  have hσσ : σ*σ ∈ U := Subgroup.mul_self_mem_of_index_two idx (⟨σ,hσ⟩ : V)
  let σ₂ : U := ⟨σ*σ,hσσ⟩
  let c : U → U := fun u => ⟨σ⁻¹*u.1*σ,preserve u⟩
  have hc : Continuous c := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have cmul (a b : U) : c (a*b) = c a * c b := by
    apply Subtype.ext
    change σ⁻¹*(a.1*b.1)*σ = (σ⁻¹*a.1*σ)*(σ⁻¹*b.1*σ)
    group
  have cc (u : U) : c (c u) = σ₂⁻¹*u*σ₂ := by
    apply Subtype.ext
    change σ⁻¹*(σ⁻¹*u.1*σ)*σ = (σ*σ)⁻¹*u.1*(σ*σ)
    group
  have cs : c σ₂ = σ₂ := by
    apply Subtype.ext
    change σ⁻¹*(σ*σ)*σ = σ*σ
    group
  let P := CharOff U S 2
  let trace : P →+ P :=
    { toFun χ := ⟨fun u => χ.1 u + χ.1 (c u),
        χ.2.1.add (χ.2.1.comp_continuous hc), fun a b => by
          simp only [cmul,χ.2.2.1]; ring,
        fun u hu => by simp only [χ.2.2.2 u hu,χ.2.2.2 (c u) (stable σ hσ _ hu),add_zero]⟩
      map_zero' := by ext; simp
      map_add' a b := by ext; simp only [Submodule.coe_add,Pi.add_apply]; ring }
  have tr (χ : P) (u : U) : (trace χ).1 u = χ.1 u + χ.1 (c u) := rfl
  have invBound := invTwo Γ U V S σ n sub hσ ho hi hn hS bound
  have kernelBound : CardLe trace.ker n := by
    refine CardLe.of_injective invBound (fun χ => ⟨χ.1, fun u u' hu => ?_⟩) ?_
    · have e : χ.1.1 u + χ.1.1 (c u) = 0 := congrArg (fun φ : P => φ.1 u) χ.2
      rw [show u' = c u from Subtype.ext hu]
      revert e
      generalize χ.1.1 u = a
      generalize χ.1.1 (c u) = b
      revert a b
      decide
    · intro a b h
      have e := congrArg Subtype.val h
      exact Subtype.ext e
  have extn (y : trace.range) : ∃ ψ : CharOff V S 2,
      ψ.1 ⟨σ,hσ⟩ = 0 ∧ ∀ u : U, ψ.1 ⟨u.1,sub u.2⟩ = y.1.1 u := by
    obtain ⟨χ,eq⟩ := y.2
    have invariant (u u' : U) (hu : u'.1 = σ⁻¹*u.1*σ) : y.1.1 u' = y.1.1 u := by
      rw [← eq, tr, tr, show u' = c u from Subtype.ext hu, cc, char_inner]
      exact add_comm _ _
    have van : y.1.1 σ₂ = 0 := by
      rw [← eq,tr,cs]
      generalize χ.1 σ₂ = b
      revert b
      decide
    obtain ⟨ψ,hψ,hσψ,hUψ⟩ := extTwo Γ U V S sub σ hσ hσσ ho hi hn hS y.1.1 y.1.2 invariant van
    exact ⟨⟨ψ,hψ⟩,hσψ,hUψ⟩
  have prodBound := card_of_normalized_extensions U V S sub ho hi hS ⟨σ,hσ⟩ hn
    (fun y : trace.range => y.1.1) (fun _ _ h => Subtype.ext (Subtype.ext h)) extn bound
  have : Finite (trace.range × ZMod 2) := prodBound.1
  have : Finite trace.range := Finite.of_injective (fun y : trace.range => (y,(0 : ZMod 2)))
    (fun _ _ e => congrArg Prod.fst e)
  have : Finite trace.ker := kernelBound.1
  have size := prodBound.2
  rw [Nat.card_prod,Nat.card_zmod,mul_comm] at size
  have total := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup trace.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange trace).toEquiv] at total
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · change Nat.card P ≠ 0
    rw [total]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  rw [show Nat.card (CharOff U S 2) = Nat.card P by rfl,total,← Nat.mul_assoc]
  exact Nat.mul_le_mul size kernelBound.2

/-- Adjoining a quadratic field raises a positive character rank r by at most r−1. -/
theorem rank_le_twice_sub_one (U V : Subgroup Γ) (S : Set Γ) (r : ℕ) (sub : U ≤ V)
    (ho : IsOpen (U.subgroupOf V : Set V)) (index : U.relIndex V ∣ 2)
    (stable : ∀ v ∈ V, ∀ s ∈ S, v⁻¹*s*v ∈ S) (hS : ∀ s ∈ S, s ∈ V → s ∈ U)
    (bound : CardLe (CharOff V S 2) (2^(r+1))) :
    CardLe (CharOff U S 2) (2^(2*r+1)) := by
  rcases (Nat.dvd_prime Nat.prime_two).1 index with e | e
  · have same := le_antisymm sub (Subgroup.relIndex_eq_one.1 e)
    subst V
    exact bound.mono (Nat.pow_le_pow_right (by decide) (by omega))
  · have h := exact_two U V S (2^(r+1)) sub ho e stable hS bound
    have fact : 2^(r+1) * 2^(r+1) = 2 * 2^(2*r+1) := by
      rw [← pow_add, show r+1+(r+1) = (2*r+1)+1 by omega, pow_succ, mul_comm]
    obtain ⟨finite,size⟩ := h
    rw [fact] at size
    exact ⟨finite, by omega⟩

#print axioms rank_le_twice_sub_one
end RiemannReduction.QuadraticDescent
