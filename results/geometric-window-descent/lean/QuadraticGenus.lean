import QuadraticSchreier

/-! Quadratic transfer with local vanishing conditions. A quadratic character
over an index-two subgroup transfers on an outer coset by evaluating at the
square. This gives a genus bound when the base has trivial unramified dual. -/
noncomputable section
open UpperTheory.V.Two
namespace RiemannReduction.QuadraticDescent
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem exists_quadratic_transfer (U V : Subgroup Γ) (S : Set Γ)
    (sub : U ≤ V) (ho : IsOpen (U.subgroupOf V : Set V)) (idx : U.relIndex V = 2)
    (stable : ∀ v ∈ V, ∀ s ∈ S, v⁻¹*s*v ∈ S) (squares : ∀ s ∈ S, s*s ∈ S)
    (σ : V) (hn : σ.1 ∉ U) (χ : CharOff U S 2) :
    ∃ Φ : CharOff V S 2,
      (∀ u u' : U, u'.1 = σ.1⁻¹*u.1*σ.1 → Φ.1 ⟨u.1,sub u.2⟩ = χ.1 u + χ.1 u') ∧
      ∀ (v : V) (h : v.1*v.1 ∈ U), v.1 ∉ U → Φ.1 v = χ.1 ⟨v.1*v.1,h⟩ := by
  classical
  have hi : (U.subgroupOf V).index = 2 := idx
  have normal := Subgroup.normal_of_index_eq_two hi
  have preserve (u : U) : σ.1⁻¹*u.1*σ.1 ∈ U := by
    have e := normal.conj_mem (⟨u.1,sub u.2⟩ : V) (Subgroup.mem_subgroupOf.2 u.2) σ⁻¹
    simpa [Subgroup.mem_subgroupOf] using e
  let c : U → U := fun u => ⟨σ.1⁻¹*u.1*σ.1,preserve u⟩
  have hc : Continuous c := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have cmul (a b : U) : c (a*b) = c a * c b := by
    apply Subtype.ext
    change σ.1⁻¹*(a.1*b.1)*σ.1 = (σ.1⁻¹*a.1*σ.1)*(σ.1⁻¹*b.1*σ.1)
    group
  have square (v : V) : v.1*v.1 ∈ U := Subgroup.mul_self_mem_of_index_two hi v
  let z : U := ⟨σ.1*σ.1,square σ⟩
  have cc (u : U) : c (c u) = z⁻¹*u*z := by
    apply Subtype.ext
    change σ.1⁻¹*(σ.1⁻¹*u.1*σ.1)*σ.1 = (σ.1*σ.1)⁻¹*u.1*(σ.1*σ.1)
    group
  have cz : c z = z := by
    apply Subtype.ext
    change σ.1⁻¹*(σ.1*σ.1)*σ.1 = σ.1*σ.1
    group
  let f : U → ZMod 2 := fun u => χ.1 u + χ.1 (c u)
  have localChar : f ∈ CharOff U ∅ 2 := by
    refine ⟨χ.2.1.add (χ.2.1.comp_continuous hc), fun a b => ?_, by simp⟩
    simp only [f,cmul,χ.2.2.1]
    ring
  have inv (u u' : U) (hu : u'.1 = σ.1⁻¹*u.1*σ.1) : f u' = f u := by
    rw [show u' = c u from Subtype.ext hu]
    simp only [f,cc,char_inner χ,add_comm]
  have zero : f z = 0 := by
    simp only [f,cz]
    generalize χ.1 z = t
    revert t
    decide
  obtain ⟨ψ,hψ,hψσ,hψU⟩ := extTwo Γ U V ∅ sub σ.1 σ.2 (square σ) ho idx hn
    (by simp) f localChar inv zero
  obtain ⟨ε,εσ,εU⟩ := sign_character U V ∅ ho idx (by simp) σ hn
  let τ : CharOff V ∅ 2 := ⟨ψ,hψ⟩ + χ.1 z • ε
  have res (u : U) : τ.1 ⟨u.1,sub u.2⟩ = χ.1 u + χ.1 (c u) := by
    change ψ _ + χ.1 z * ε.1 _ = f u
    rw [hψU,εU ⟨u.1,sub u.2⟩ u.2,mul_zero,add_zero]
  have rep : τ.1 σ = χ.1 z := by
    change ψ σ + χ.1 z * ε.1 σ = _
    rw [hψσ,εσ,mul_one,zero_add]
  have outside (v : V) (hv : v.1 ∉ U) : τ.1 v = χ.1 ⟨v.1*v.1,square v⟩ := by
    have hσi : σ⁻¹ ∉ U.subgroupOf V := fun h => hn (Subgroup.mem_subgroupOf.mp (by simpa using (U.subgroupOf V).inv_mem h))
    have hmem : σ⁻¹*v ∈ U.subgroupOf V :=
      (Subgroup.mul_mem_iff_of_index_two hi).2 (by simp [hσi,show v ∉ U.subgroupOf V from hv])
    let a : U := ⟨σ.1⁻¹*v.1,hmem⟩
    have form : v = σ * ⟨a.1,sub a.2⟩ := by
      apply Subtype.ext
      change v.1 = σ.1 * (σ.1⁻¹*v.1)
      group
    have sq : (⟨v.1*v.1,square v⟩ : U) = z * c a * a := by
      apply Subtype.ext
      change v.1*v.1 = (σ.1*σ.1)*(σ.1⁻¹*(σ.1⁻¹*v.1)*σ.1)*(σ.1⁻¹*v.1)
      group
    calc
      τ.1 v = τ.1 σ + τ.1 ⟨a.1,sub a.2⟩ := (congrArg τ.1 form).trans (τ.2.2.1 _ _)
      _ = χ.1 ⟨v.1*v.1,square v⟩ := by rw [rep,res,sq,χ.2.2.1,χ.2.2.1]; ring
  have unram : τ.1 ∈ CharOff V S 2 := by
    refine ⟨τ.2.1,τ.2.2.1, fun v hv => ?_⟩
    by_cases inside : v.1 ∈ U
    · let u : U := ⟨v.1,inside⟩
      change τ.1 ⟨u.1,sub u.2⟩ = 0
      rw [res,χ.2.2.2 u hv,χ.2.2.2 (c u) (stable σ.1 σ.2 _ hv),add_zero]
    · rw [outside v inside,χ.2.2.2 _ (squares _ hv)]
  exact ⟨⟨τ.1,unram⟩, fun u u' h => (res u).trans (by rw [show u' = c u from Subtype.ext h]),
    fun v _ hv => outside v hv⟩

/-- If the base has no unramified quadratic characters, permitting ramification
at the defining quadratic primes costs one character less after restriction. -/
theorem quadratic_genus_bound (U V : Subgroup Γ) (S T : Set Γ) (r : ℕ)
    (sub : U ≤ V) (ho : IsOpen (U.subgroupOf V : Set V)) (index : U.relIndex V ∣ 2)
    (stable : ∀ v ∈ V, ∀ s ∈ S, v⁻¹*s*v ∈ S) (squares : ∀ s ∈ S, s*s ∈ S)
    (incl : T ⊆ S) (off : ∀ s ∈ T, s ∈ V → s ∈ U)
    (base : CardLe (CharOff V S 2) 1) (ray : CardLe (CharOff V T 2) (2^(r+1))) :
    CardLe (CharOff U S 2) (2^r) := by
  classical
  rcases (Nat.dvd_prime Nat.prime_two).1 index with e | e
  · have same := le_antisymm sub (Subgroup.relIndex_eq_one.1 e)
    subst V
    exact base.mono (Nat.one_le_two_pow)
  have not_le : ¬ V ≤ U := fun h => by
    have h1 := Subgroup.relIndex_eq_one.2 h
    omega
  obtain ⟨σ,hσ,hn⟩ := SetLike.not_le_iff_exists.1 not_le
  have : Finite (CharOff V S 2) := base.1
  have : Subsingleton (CharOff V S 2) := (Finite.card_le_one_iff_subsingleton (α := CharOff V S 2)).mp base.2
  have sq : σ*σ ∈ U := Subgroup.mul_self_mem_of_index_two (H := U.subgroupOf V) e (⟨σ,hσ⟩ : V)
  have extension (χ : CharOff U S 2) : ∃ ψ : CharOff V T 2,
      ψ.1 ⟨σ,hσ⟩ = 0 ∧ ∀ u : U, ψ.1 ⟨u.1,sub u.2⟩ = χ.1 u := by
    obtain ⟨Φ,res,out⟩ := exists_quadratic_transfer U V S sub ho e stable squares ⟨σ,hσ⟩ hn χ
    have zero (v : V) : Φ.1 v = 0 := congrArg (fun θ : CharOff V S 2 => θ.1 v) (Subsingleton.elim Φ 0)
    have inv (u u' : U) (hu : u'.1 = σ⁻¹*u.1*σ) : χ.1 u' = χ.1 u := by
      have h := (res u u' hu).symm.trans (zero _)
      revert h
      generalize χ.1 u = a
      generalize χ.1 u' = b
      revert a b
      decide
    have vanish := (out ⟨σ,hσ⟩ sq hn).symm.trans (zero _)
    have hχ : χ.1 ∈ CharOff U T 2 := ⟨χ.2.1,χ.2.2.1, fun u hu => χ.2.2.2 u (incl hu)⟩
    obtain ⟨ψ,hψ,hσψ,hUψ⟩ := extTwo Γ U V T sub σ hσ sq ho e hn off χ.1 hχ inv vanish
    exact ⟨⟨ψ,hψ⟩,hσψ,hUψ⟩
  have b := card_of_normalized_extensions U V T sub ho e off ⟨σ,hσ⟩ hn
    (fun χ : CharOff U S 2 => χ.1) Subtype.val_injective extension ray
  have : Finite (CharOff U S 2 × ZMod 2) := b.1
  have fin : Finite (CharOff U S 2) := Finite.of_injective (fun x : CharOff U S 2 => (x,(0 : ZMod 2)))
    (fun _ _ h => congrArg Prod.fst h)
  have size := b.2
  rw [Nat.card_prod,Nat.card_zmod,pow_succ] at size
  exact ⟨fin,by omega⟩

#print axioms quadratic_genus_bound
end RiemannReduction.QuadraticDescent
