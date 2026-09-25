import OddMath.Frontier.EKLSectionTwo
import OddMath.Frontier.EKLSectionTwoB
import OddMath.Frontier.EKLSectionTwoC
import OddMath.Frontier.EKLSectionTwoD
import OddMath.Frontier.EKLSectionTwoE
import OddMath.Frontier.EKLSectionTwoF
import OddMath.Frontier.EKLSectionTwoG
import OddMath.Frontier.EKLSectionTwoH
import OddMath.Frontier.Categorification
import OddMath.Frontier.OddCategorification
import OddMath.Frontier.EKLMisc
import OddMath.Frontier.EKLMisc2
import OddMath.Frontier.OnhStructure
import OddMath.Frontier.OnhStructure2

/-! Audit for EKL arXiv:1111.1320v1 §2 (remaining items) and §6 (6.1)–(6.3): transitive axioms. -/
namespace OddMath.Frontier.EKLSectionTwoAudit
open OddMath.Frontier
#print axioms EKLSectionTwo.qrk_symmetric
#print axioms EKLSectionTwo.qfactorial_eq
#print axioms EKLSectionTwo.box_qcard
#print axioms EKLSectionTwo.qrkPol_eq
#print axioms EKLSectionTwo.printed_qrk_quotient_false
#print axioms EKLSectionTwo.polynomialModTwo
#print axioms EKLSectionTwo.symmetricModTwo
#print axioms EKLSectionTwo.reorder_even
#print axioms EKLSectionTwo.reorder_odd
#print axioms EKLSectionTwo.mixed_even
#print axioms EKLSectionTwo.mixed_odd
#print axioms EKLSectionTwo.complete_last
#print axioms EKLSectionTwo.psi_homotopy
#print axioms EKLSectionTwo.schubert_identity_action
#print axioms EKLSectionTwo.s_elementary_one_not_mem
#print axioms EKLSectionTwo.horizontal_pieri
#print axioms EKLSectionTwo.schur_two_two
#print axioms EKLSectionTwo.printed_schur_two_two_false
#print axioms EKLSectionTwo.complete_two_two
#print axioms EKLSectionTwo.complete_three_one
#print axioms EKLSectionTwo.printed_complete_determinant_false
#print axioms EKLSectionTwo.elementary_four_not_mem
#print axioms EKLSectionTwo.schur_ne_elementary_determinant
#print axioms EKLSectionTwo.schur_ne_complete_determinant
#print axioms EKLSectionTwo.printed_leading_term_false
#print axioms Categorification.eq_6_1
#print axioms Categorification.eq_6_2
#print axioms Categorification.eq_6_1_row_mul_col
#print axioms Categorification.eq_6_2_col_mul_row
#print axioms Categorification.cyclotomic_vanish
#print axioms OddCategorification.eq_6_3
#print axioms OddCategorification.eq_6_3_UA
#print axioms OddCategorification.eq_6_1_K0
#print axioms OddCategorification.eq_6_1_qFact
#print axioms OddCategorification.eq_6_1_printed_false
#print axioms OddCategorification.eq_6_2_K0
#print axioms OddCategorification.basisE
#print axioms OddCategorification.rankEquiv_Eclass
#print axioms EKLSectionTwo.reverse_sK
#print axioms EKLSectionTwo.psi3_not_diagonal
#print axioms EKLSectionTwo.left_vertical_pieri
#print axioms EKLSectionTwo.left_horizontal_pieri
#print axioms EKLSectionTwo.left_vertical_pieri_Q
#print axioms EKLSectionTwo.eq_2_49_printed_fails
#print axioms EKLSectionTwo.eq_2_49_sum_from_zero
#print axioms EKLSectionTwo.eq_2_50_printed_fails
#print axioms EKLSectionTwo.eq_2_50_sum_from_zero
#print axioms EKLSectionTwo.eq_2_51
#print axioms EKLSectionTwo.eq_2_63
#print axioms EKLSectionTwo.eq_2_53
#print axioms EKLSectionTwo.cor_2_6_rank_two
#print axioms EKLMisc.prop_4_5_rank
#print axioms EKLMisc.left_noetherian
#print axioms EKLMisc.right_noetherian
#print axioms EKLMisc.eq_2_44
#print axioms EKLMisc.chi_col
#print axioms EKLMisc.signX_col_mod_two
#print axioms EKLMisc.eq_4_52_false
#print axioms EKLMisc.signX_col_self_even
#print axioms EKLMisc.complete_parts_not_basis
#print axioms EKLMisc.elementary_basis
#print axioms OnhStructure.cornerEquiv
#print axioms OnhStructure.matrixEquiv
#print axioms OnhStructure.endProjectorEquiv
#print axioms OnhStructure.projector_primitive
#print axioms OnhStructure.leftIdeal_projector_indecomposable
#print axioms OnhStructure.tensorMap_injective
#print axioms OnhStructure.tensorMap_mul
end OddMath.Frontier.EKLSectionTwoAudit
