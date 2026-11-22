import PrincipalCountWindow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PublishedHypothesesFromPatching
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEndsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftingOfCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KatoTwoWOfPublishedH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CohInp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.HasOfSplit

/-! Discharge the counting arguments of the dyadic principal window using the
    same literature inputs as the archived general window. The final assembly
    follows WindowBoundOfLiteratureLevel and HVCore up to the choice of minus
    estimate, which is supplied by the dyadic field argument in PrincipalCountWindow. -/

noncomputable section
open Formalism.HC UpperTheory.Top UpperTheory.V
namespace RiemannReduction.ConductorOne

theorem principal_window_of_literature
    (lit : GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) :
    VWinAt PChar.one 401 := by
  let H := HV.DescentVanishingReductions.published_hypotheses_from_patching_alt lit Z.Tf.SR.descWeak
  have generators := ZK.lemmaK_litN_alt H.litN
  have ends := Z.Win.Dn.ends0_alt H
  have symplectic := HV.DescentVanishingReductions.countII_and_countIII_of_printsH_of_sp4In H
    generators (HV.DescentVanishingReductions.sp4In0_alt H)
  have first := Z.J.count_i_of_printed_bound_k_kato_automorphy H generators
    (Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH H)
    (HV.Core0.automorphyUnramified_of_litN_of_gdEnd H.litN ends.1)
  have fifth := Z.J.count_v_of_printed_bound_k_reduced_unitary_lift H generators ends.2
  have duality := HV.U.pt_s H.litN
  obtain ⟨B, layers⟩ := Win.thmBab_of_lemmaK duality H.litN.coh.lfK H.litN.coh.ltK
    FW.ferreroWashington generators
  obtain ⟨c, gc⟩ := generators
  exact principal_window_from_counts duality H.litN.coh.lfK H.litN.coh.ltK gc
    (layers 401 (by norm_num)) first symplectic.1 symplectic.2 fifth (HV.countZ X.propZ)

end RiemannReduction.ConductorOne
