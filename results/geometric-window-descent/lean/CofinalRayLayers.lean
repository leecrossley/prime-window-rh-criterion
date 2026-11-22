import OrdinaryRayDescent
import AtCharacter

/-! A cofinal set of finite cyclotomic levels suffices for the tower rank.
The existing single-inertia proof already proves the finite-layer assertion
as a helper; the alias below preserves its checked proof term. -/
noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open Lean Elab Command in
run_cmd liftTermElabM do
  RiemannReduction.CharacterRestriction.nameHelper `RationalDyadicInertia
    `RiemannReduction.GaussianTower.level_character_zero `RiemannReduction.GaussianTower.pure_layer_character_zero

namespace RiemannReduction.GaussianTower
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem rank_on_cofinal_layers (U : Subgroup (G ℚ Ω)) (r : ℕ) (closed : IsClosed (U : Set (G ℚ Ω)))
    (good : ∀ start : ℕ, ∃ n ≥ start, XRk 2 1 (levU 2 U n) r) :
    XRk 2 1 (cycU 2 U) r := by
  have down {n m : ℕ} (h : n ≤ m) : levU 2 U m ≤ levU 2 U n :=
    inf_le_inf_left _ (Subgroup.comap_mono (KStar.TotallyRealRoots.princ_anti h))
  let X := XDual 1 (cycU 2 U) (ZMod 2) (ZMod 2)
  let Xn (n : ℕ) := XDual 1 (levU 2 U n) (ZMod 2) (ZMod 2)
  let res (n : ℕ) (ψ : Xn n) : X :=
    ⟨restr (ZMod 2) (ZMod 2) (cycU_le_levU 2 U n) ψ.1,
      (restrMem ℚ Ω 1 _ _ (cycU_le_levU 2 U n) (ZMod 2) (ZMod 2) 1).1 (Submodule.mem_map_of_mem ψ.2)⟩
  have inc {n m : ℕ} (h : n ≤ m) : Set.range (res n) ⊆ Set.range (res m) := by
    rintro _ ⟨ψ,rfl⟩
    exact ⟨⟨restr (ZMod 2) (ZMod 2) (down h) ψ.1,
      (restrMem ℚ Ω 1 _ _ (down h) (ZMod 2) (ZMod 2) 1).1 (Submodule.mem_map_of_mem ψ.2)⟩,rfl⟩
  apply cardUnion X (fun n => Set.range (res n)) (2^r) (fun _ _ h => inc h)
  · intro φ
    obtain ⟨n,ψ,hψ,eq⟩ := xdualExt ℚ Ω 2 1 U (ZMod 2) (ZMod 2) one_ne_zero closed φ.1 φ.2
    exact ⟨n,⟨⟨ψ,hψ⟩,Subtype.ext eq⟩⟩
  · intro k
    obtain ⟨n,late,finite,card⟩ := good k
    have : Finite (Xn n) := finite
    exact ⟨((Set.finite_range (res n)).subset (inc late)).to_subtype,
      (Nat.card_mono (Set.finite_range (res n)) (inc late)).trans ((Finite.card_range_le (res n)).trans card)⟩

theorem pure_layer_one {n : ℕ} (pos : 0 < n) :
    CardLe (CharOff (galChar Ω (2^n)).ker (ineOff ℚ Ω 1) 2) 1 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  let H := (galChar Ω (2^(m+1))).ker
  have : Subsingleton (CharOff H (ineOff ℚ Ω 1) 2) := by
    constructor
    intro φ ψ
    have z (φ : CharOff H (ineOff ℚ Ω 1) 2) (v : H) : φ.1 v = 0 := by
      apply pure_layer_character_zero Ω m φ.1 _ v
      rw [xDual_one]
      exact φ.2
    exact Subtype.ext (funext fun v => (z φ v).trans (z ψ v).symm)
  exact ⟨inferInstance, le_of_eq Nat.card_unique⟩

private theorem host_finite_layer {q d n : ℕ} (hn : 2 ≤ n) :
    levU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d)) n =
      (abU Ω (AbF.quad q) ⊓ abU Ω (AbF.quad d)) ⊓ (galChar Ω (2^n)).ker := by
  have root : abU Ω (AbF.ofChar PChar.one) = ⊤ :=
    Subgroup.index_eq_one.mp (((abBasic Ω).2.1 _).1.trans ordinary_degree)
  have h4 : (galChar Ω (2^n)).ker ≤ (galChar Ω 4).ker := by
    intro g hg
    rw [MonoidHom.mem_ker,← (galCharBasic Ω 4).2.2.2 _ (show 4 ∣ 2^n from pow_dvd_pow 2 hn) g]
    rw [MonoidHom.mem_ker.mp hg,map_one]
  ext g
  simp only [(levChar Ω 2 n _).1,base2,withI,(abBasic Ω).1,root,top_inf_eq,(abBasic Ω).2.2.2,
    Subgroup.mem_inf]
  exact ⟨fun h => ⟨⟨h.1.1.2,h.1.2⟩,h.2⟩,fun h => ⟨⟨⟨h4 h.2,h.1.1⟩,h.1.2⟩,h.2⟩⟩

/-- Only cofinally many finite pure cyclotomic ray bounds are needed. -/
theorem host_rank_of_cofinal_finite_ray {q d r : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (ray : ∀ start : ℕ, ∃ n ≥ start, RayRank Ω (galChar Ω (2^n)).ker q d (r+2)) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) (2*r+1) := by
  let M := AbF.ofChar PChar.one
  let U := abU Ω (base2 M q d)
  have closed : IsClosed (U : Set (G ℚ Ω)) := U.isClosed_of_isOpen ((abBasic Ω).2.1 _).2.2.1
  apply rank_on_cofinal_layers Ω U _ closed
  intro start
  obtain ⟨n,hn,hRay⟩ := ray (max 2 start)
  have late := (le_max_left 2 start).trans hn
  obtain ⟨hq,mq,hd,md,_⟩ := pair
  refine ⟨n,(le_max_right 2 start).trans hn,?_⟩
  change CardLe _ _
  rw [xDual_one,show levU 2 U n = _ from host_finite_layer Ω (q := q) (d := d) late]
  exact descent_at_level Ω _ hq mq hd md (pure_layer_one Ω (by omega)) hRay

#print axioms host_rank_of_cofinal_finite_ray
end RiemannReduction.GaussianTower
