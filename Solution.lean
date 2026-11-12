module
public import Theorem23
public import JohnsonMain
public import JohnsonACFMain
@[expose] public section
open FirstOrder FirstOrder.Language
/-- Pure ACF has bounded quantifier elimination in every characteristic. -/
theorem PalomarQE.acf : QECriterion.HasQEb (L := Language.ring) ACFValidation.acf := JohnsonACF.hasQEb
#print axioms PalomarQE.acf
/-- Nontrivially valued algebraically closed fields have bounded QE. -/
theorem PalomarQE.nontrivial_acvf : QECriterion.HasQEb (L := Language.val) ValPM.ACVF_val := hasQEb_ACVF_val
#print axioms PalomarQE.nontrivial_acvf
/-- Nontrivial ACVF has well-sorted QE in the corrected RV language. -/
theorem PalomarQE.rv_acvf : SpecialTransformations.Milestone0.HasQE SpecialTransformations.Milestone0.Axioms.ACVF := SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination
#print axioms PalomarQE.rv_acvf
