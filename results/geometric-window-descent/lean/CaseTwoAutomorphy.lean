import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularityRankFourOfPromodularity

/-! The ordinary-character geometry uses only the second symplectic case.
The rank-four argument in this case uses the second promodular seed directly. -/
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal
  IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV
  UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace RiemannReduction.SymplecticTwo

def CaseTwoAutomorphy : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} (D : Raw Ω c), Ctx2 D →
    D.Fin0 ∧ D.NoEnd ∧ ∃ ι : PadicAlgCl l ≃+* ℂ, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι)

theorem automorphy_of_second_seed (hP : CohomologyHyp) (fw : UpperTheory.V.Published.FerreroWashington)
    (seed : UpperTheory.V.Ws.SeedIIAlt) (pm : UpperTheory.V.Ws.PMExAlt) : CaseTwoAutomorphy := by
  intro Ω _ _ _ l _ c D ctx
  have hD : D.Good := ctx.1
  obtain ⟨ι⟩ := (UpperTheory.V.Ws.ambZero l).2
  have hA : ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) →
      _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r := fun 𝔞 r u hK hS =>
    _root_.UpperTheory.V.Ws.proMod_of_pmEx_of_ctx2_of_kPair_of_star hP fw seed pm D ctx ι 𝔞 r u hK hS
  have hcon : Con D := fun 𝔞 hch r u hK hS =>
    _root_.UpperTheory.V.Ws.contradiction_star_promodular D hD ι 𝔞 hch r u hK (hA 𝔞 r u hK hS) hS
  have hpur : _root_.UpperTheory.V.Ws.PurityAtPoints D ι := fun 𝔞 e' he' r u hK hS =>
    _root_.UpperTheory.V.Ws.pureW_of_proModular_of_isZero D hD ι 𝔞 e' he' r (hA 𝔞 r u hK hS)
  have haut : _root_.UpperTheory.V.Ws.AutmAlt D ι := fun 𝔞 e' he' r u hK hI =>
    _root_.UpperTheory.V.Ws.aut_n_alt D hD ι 𝔞 e' he' r u hK (hA 𝔞 r u hK (Or.inl hI)) hI
  obtain ⟨hF, hN, hAll⟩ := _root_.UpperTheory.V.Ws.fin0_no_end_all_irr_of_good_con_purity_aut hP D hD ι hcon hpur haut
  exact ⟨hF, hN, ι, hAll⟩

#print axioms automorphy_of_second_seed
end RiemannReduction.SymplecticTwo
