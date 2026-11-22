import SingleInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkAbs

/-! The pure dyadic tower over the rationals has no everywhere unramified
quadratic characters. The group argument uses the generation of the rational
absolute Galois group by finite inertia, and the single orbit above two. -/
noncomputable section
open scoped Pointwise
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Kum UpperTheory.V.Base UpperTheory.V.Two
namespace RiemannReduction.GaussianTower
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

private theorem one_dyadic_orbit (A₀ A : ValuationSubring Ω)
    (h₀ : A₀.valuation (2 : Ω) < 1) (h : A.valuation (2 : Ω) < 1) :
    ∃ g : G ℚ Ω, g • A₀ = A := by
  obtain ⟨T, hT, _, cover⟩ := orbIndex Ω 2 ⊤ A₀ Nat.prime_two h₀ (by simp)
  obtain ⟨B, hB, u, _, hu⟩ := cover A₀ h₀
  obtain ⟨C, hC, v, _, hv⟩ := cover A h
  have hsize : T.card ≤ 1 := by simpa using hT
  have e := Finset.card_le_one.mp hsize B hB C hC
  subst C
  exact ⟨v * u⁻¹, by rw [← hu, mul_smul, inv_smul_smul, hv]⟩

private theorem level_character_zero (m : ℕ) :
    let H := (galChar Ω (2^(m+1))).ker
    ∀ (φ : H → ZMod 2), φ ∈ XDual 1 H (ZMod 2) (ZMod 2) → ∀ x : H, φ x = 0 := by
  classical
  let H := (galChar Ω (2^(m+1))).ker
  change ∀ φ : H → ZMod 2, φ ∈ XDual 1 H (ZMod 2) (ZMod 2) → ∀ x : H, φ x = 0
  intro φ hφ
  rw [xDual_one] at hφ
  let f : H →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (φ x)
      map_one' := by
        change φ 1 = 0
        have e := hφ.2.1 1 1
        rw [one_mul] at e
        exact (add_eq_left.mp e.symm)
      map_mul' := fun a b => hφ.2.1 a b }
  let K := f.ker.map H.subtype
  have ksub : K ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have openH : IsOpen (H : Set (G ℚ Ω)) := by
    obtain ⟨_, deg, _, cyc⟩ := abBasic Ω
    simpa only [cyc] using (deg (AbF.cyc (2^(m+1)))).2.2.1
  have openK : IsOpen (K : Set (G ℚ Ω)) :=
    openH.isOpenMap_subtype_val _ (hφ.1.isOpen_fiber 0)
  let ko : OpenSubgroup (G ℚ Ω) := ⟨K, openK⟩
  have hf : f.ker.FiniteIndex := inferInstance
  have hh : H.FiniteIndex := inferInstanceAs ((galChar Ω (2^(m+1))).ker.FiniteIndex)
  have : K.FiniteIndex := ⟨by
    rw [show K.index = f.ker.index * H.index from Subgroup.index_map_subtype _]
    exact mul_ne_zero hf.index_ne_zero hh.index_ne_zero⟩
  have openN := K.normalCore.isOpen_of_isClosed_of_finiteIndex (K.normalCore_isClosed ko.isClosed)
  have powH (g : G ℚ Ω) : g ^ (2^m) ∈ H := by
    change galChar Ω (2^(m+1)) (g ^ (2^m)) = 1
    rw [map_pow]
    simpa only [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_two,
      Nat.reduceSub, mul_one] using (pow_card_eq_one (x := galChar Ω (2^(m+1)) g))
  have squareK (g : G ℚ Ω) (hg : g ∈ H) : g ^ 2 ∈ K := by
    let u : H := ⟨g,hg⟩
    refine ⟨u ^ 2, ?_, rfl⟩
    change φ (u ^ 2) = 0
    rw [pow_two, hφ.2.1, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have inertia_mem (A : ValuationSubring Ω) {g : G ℚ Ω} (hg : g ∈ H) (hi : g ∈ Ine (F := ℚ) A) :
      g ∈ K := ⟨⟨g,hg⟩, hφ.2.2 _ ⟨A,by simp,hi⟩, rfl⟩
  have away (A : ValuationSubring Ω) (ha : ¬A.valuation (2 : Ω) < 1) : Ine (F := ℚ) A ≤ K.normalCore := by
    intro g hg b
    let B := b • A
    have hb : ¬B.valuation (2 : Ω) < 1 := fun e => ha (((ineConj ℚ Ω b).2.1 A 2).mp e)
    have hB : b * g * b⁻¹ ∈ Ine (F := ℚ) B := by
      have h := (ineConj ℚ Ω b⁻¹).1 B g (by simpa [B] using hg)
      simpa using h
    exact inertia_mem B ((levChar Ω 2 (m+1) ⊤).2 ((places ℚ Ω 2 B).2.2.2 hb hB)) hB
  have all : H ≤ K := by
    by_cases dyadic : ∃ A₀ : ValuationSubring Ω, A₀.valuation (2 : Ω) < 1
    · obtain ⟨A₀, ha⟩ := dyadic
      let I := Ine (F := ℚ) A₀
      let π := QuotientGroup.mk' K.normalCore
      have surj : I.map π = ⊤ := by
        apply inertia_surjects K.normalCore I (core_is_two_group H K m powH squareK) openN
        intro U normal hop hN hI
        apply UpperTheory.V.CF.minkAbs Ω U hop
        intro A
        by_cases hA : A.valuation (2 : Ω) < 1
        · obtain ⟨v, rfl⟩ := one_dyadic_orbit Ω A₀ A ha hA
          intro g hg
          have ec := normal.conj_mem _ (hI ((ineConj ℚ Ω v).1 A₀ g hg)) v
          rwa [show v * (v⁻¹ * g * v) * v⁻¹ = g by group] at ec
        · exact (away A hA).trans hN
      intro x hx
      have image : π x ∈ I.map π := by rw [surj]; trivial
      obtain ⟨i, hi, he⟩ := image
      have hn : x * i⁻¹ ∈ K.normalCore := by
        apply (QuotientGroup.eq_one_iff _).mp
        change π (x * i⁻¹) = 1
        rw [map_mul, map_inv, he, mul_inv_cancel]
      have hk := K.normalCore_le hn
      have ih : i ∈ H := by
        rw [show i = (x * i⁻¹)⁻¹ * x by group]
        exact H.mul_mem (H.inv_mem (ksub hk)) hx
      have final := K.mul_mem hk (inertia_mem A₀ ih hi)
      simpa only [inv_mul_cancel_right] using final
    · have full := UpperTheory.V.CF.minkAbs Ω K openK
        fun A => (away A (fun h => dyadic ⟨A,h⟩)).trans K.normalCore_le
      rw [full]
      exact le_top
  intro x
  obtain ⟨y, hy, e⟩ := all x.2
  have eq : y = x := Subtype.ext e
  subst y
  exact hy

theorem pure_rank_zero :
    XRk 2 1 (cycU 2 (⊤ : Subgroup (G ℚ Ω))) 0 := by
  apply infRk ℚ Ω 2 1 0 ⊤ one_ne_zero isClosed_univ
  intro n hn
  rcases n with _ | m
  · omega
  rw [(levChar Ω 2 (m+1) ⊤).1, top_inf_eq]
  let H := (galChar Ω (2^(m+1))).ker
  have : Subsingleton (XDual 1 H (ZMod 2) (ZMod 2)) := by
    constructor
    intro φ ψ
    apply Subtype.ext
    funext x
    exact (level_character_zero Ω m φ.1 φ.2 x).trans (level_character_zero Ω m ψ.1 ψ.2 x).symm
  exact ⟨inferInstance, by simp only [pow_zero, Nat.card_unique, le_refl]⟩

#print axioms pure_rank_zero
end RiemannReduction.GaussianTower
