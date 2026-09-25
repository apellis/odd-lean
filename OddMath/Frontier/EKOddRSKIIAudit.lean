import OddMath.Frontier.EKOddRSKII
import OddMath.Frontier.EKOddRSKIIControls

/-! Axiom audit (EK1107.5610v2 p.30, Cor 3.12 (3.14), Cor 3.13 (3.15)).

1. Literal `#print axioms` for every non-private named owned declaration.
2. Exhaustive sweep over EVERY constant whose defining module is `OddMath.Frontier.EKOddRSKII`
   or `OddMath.Frontier.EKOddRSKIIControls` (private, auxiliary, equation lemmas included):
   the build FAILS unless each depends only on propext, Classical.choice, Quot.sound.
3. Type-level restatement checks of the headline results (unconditional vs CONDITIONAL). -/

open OddMath.Frontier
open OddMath.Frontier.EKOddRSKII

#print axioms OddMath.Frontier.EKOddRSKII.transposeChoose_eq
#print axioms OddMath.Frontier.EKOddRSKII.cells_fst_sum_cols
#print axioms OddMath.Frontier.EKOddRSKII.cells_fst_sum_rows
#print axioms OddMath.Frontier.EKOddRSKII.evenParts_rowLens
#print axioms OddMath.Frontier.EKOddRSKII.sign_bridge
#print axioms OddMath.Frontier.EKOddRSKII.ell_transpose
#print axioms OddMath.Frontier.EKOddRSKII.card_transpose
#print axioms OddMath.Frontier.EKOddRSKII.transposeShape_invol
#print axioms OddMath.Frontier.EKOddRSKII.wordSign_eq
#print axioms OddMath.Frontier.EKOddRSKII.wordSign_hPartition
#print axioms OddMath.Frontier.EKOddRSKII.psi12_hPartition
#print axioms OddMath.Frontier.EKOddRSKII.psi12_ePartition
#print axioms OddMath.Frontier.EKOddRSKII.schur
#print axioms OddMath.Frontier.EKOddRSKII.schur_eq_sC
#print axioms OddMath.Frontier.EKOddRSKII.schur_defining
#print axioms OddMath.Frontier.EKOddRSKII.schur_val_unique
#print axioms OddMath.Frontier.EKOddRSKII.Lemma311
#print axioms OddMath.Frontier.EKOddRSKII.Cor39
#print axioms OddMath.Frontier.EKOddRSKII.First312
#print axioms OddMath.Frontier.EKOddRSKII.Second312
#print axioms OddMath.Frontier.EKOddRSKII.OddRSKII
#print axioms OddMath.Frontier.EKOddRSKII.DualRSK
#print axioms OddMath.Frontier.EKOddRSKII.first312_of_lemma311
#print axioms OddMath.Frontier.EKOddRSKII.lemma311_of_first312
#print axioms OddMath.Frontier.EKOddRSKII.first312_iff_lemma311
#print axioms OddMath.Frontier.EKOddRSKII.second312_of_dualRSK
#print axioms OddMath.Frontier.EKOddRSKII.pair_e_schur_of_second
#print axioms OddMath.Frontier.EKOddRSKII.dualRSK_of_second312
#print axioms OddMath.Frontier.EKOddRSKII.second312_iff_dualRSK
#print axioms OddMath.Frontier.EKOddRSKII.pair_e_schur_of_first_cor39
#print axioms OddMath.Frontier.EKOddRSKII.dualRSK_of_first_cor39
#print axioms OddMath.Frontier.EKOddRSKII.oddRSKII_of_first_cor39
#print axioms OddMath.Frontier.EKOddRSKII.schur_span
#print axioms OddMath.Frontier.EKOddRSKII.first312_of_second312_cor39
#print axioms OddMath.Frontier.EKOddRSKII.equivalences_of_cor39
#print axioms OddMath.Frontier.EKOddRSKII.CONDITIONAL_cor_3_12_first
#print axioms OddMath.Frontier.EKOddRSKII.CONDITIONAL_cor_3_12_second
#print axioms OddMath.Frontier.EKOddRSKII.CONDITIONAL_cor_3_13
#print axioms OddMath.Frontier.EKOddRSKII.first312_le_four
#print axioms OddMath.Frontier.EKOddRSKII.second312_le_four
#print axioms OddMath.Frontier.EKOddRSKII.dualRSK_le_four
#print axioms OddMath.Frontier.EKOddRSKII.oddRSKII_le_four
#print axioms OddMath.Frontier.EKOddRSKII.lemma311_le_four
#print axioms OddMath.Frontier.EKOddRSKIIControls.evenParts
#print axioms OddMath.Frontier.EKOddRSKIIControls.transposeChoose
#print axioms OddMath.Frontier.EKOddRSKIIControls.validFill
#print axioms OddMath.Frontier.EKOddRSKIIControls.words
#print axioms OddMath.Frontier.EKOddRSKIIControls.KW
#print axioms OddMath.Frontier.EKOddRSKIIControls.cellsOf
#print axioms OddMath.Frontier.EKOddRSKIIControls.KL
#print axioms OddMath.Frontier.EKOddRSKIIControls.signedKostka_eq_KW
#print axioms OddMath.Frontier.EKOddRSKIIControls.rowCells_eq_of
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_cells
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_transpose
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_signs
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_0_0
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_1_1
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_2_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_2_11
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_11_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_11_11
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_3_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_3_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_3_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_21_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_21_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_21_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_111_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_111_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_111_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_4_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_4_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_4_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_4_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_4_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_31_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_31_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_31_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_31_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_31_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_22_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_22_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_22_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_22_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_22_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_211_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_211_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_211_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_211_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_211_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_1111_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_1111_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_1111_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_1111_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.K_1111_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.shape_eq_iff
#print axioms OddMath.Frontier.EKOddRSKIIControls.small_partition
#print axioms OddMath.Frontier.EKOddRSKIIControls.sum_list
#print axioms OddMath.Frontier.EKOddRSKIIControls.exhaust0
#print axioms OddMath.Frontier.EKOddRSKIIControls.sum0
#print axioms OddMath.Frontier.EKOddRSKIIControls.exhaust1
#print axioms OddMath.Frontier.EKOddRSKIIControls.sum1
#print axioms OddMath.Frontier.EKOddRSKIIControls.exhaust2
#print axioms OddMath.Frontier.EKOddRSKIIControls.sum2
#print axioms OddMath.Frontier.EKOddRSKIIControls.exhaust3
#print axioms OddMath.Frontier.EKOddRSKIIControls.sum3
#print axioms OddMath.Frontier.EKOddRSKIIControls.exhaust4
#print axioms OddMath.Frontier.EKOddRSKIIControls.sum4
#print axioms OddMath.Frontier.EKOddRSKIIControls.yd_eq_of_rowLens
#print axioms OddMath.Frontier.EKOddRSKIIControls.PM
#print axioms OddMath.Frontier.EKOddRSKIIControls.ms_singleton
#print axioms OddMath.Frontier.EKOddRSKIIControls.ms_zeroRows
#print axioms OddMath.Frontier.EKOddRSKIIControls.matrixSum_eq_PM
#print axioms OddMath.Frontier.EKOddRSKIIControls.PML
#print axioms OddMath.Frontier.EKOddRSKIIControls.ms_rows
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_eq_PML
#print axioms OddMath.Frontier.EKOddRSKIIControls.M_eq_PML
#print axioms OddMath.Frontier.EKOddRSKIIControls.rowChoose
#print axioms OddMath.Frontier.EKOddRSKIIControls.Esrc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sigmaSrc
#print axioms OddMath.Frontier.EKOddRSKIIControls.Xsrc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sC
#print axioms OddMath.Frontier.EKOddRSKIIControls.sC_defining
#print axioms OddMath.Frontier.EKOddRSKIIControls.pair_ee
#print axioms OddMath.Frontier.EKOddRSKIIControls.pair_e_sC
#print axioms OddMath.Frontier.EKOddRSKIIControls.ext_e
#print axioms OddMath.Frontier.EKOddRSKIIControls.neg_one_sq
#print axioms OddMath.Frontier.EKOddRSKIIControls.second_of_dual
#print axioms OddMath.Frontier.EKOddRSKIIControls.first_of_numeric
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh0_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_0_0
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_0_0
#print axioms OddMath.Frontier.EKOddRSKIIControls.dual0
#print axioms OddMath.Frontier.EKOddRSKIIControls.first0
#print axioms OddMath.Frontier.EKOddRSKIIControls.odd_rsk_II_0
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_1_1
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_1_1
#print axioms OddMath.Frontier.EKOddRSKIIControls.dual1
#print axioms OddMath.Frontier.EKOddRSKIIControls.first1
#print axioms OddMath.Frontier.EKOddRSKIIControls.odd_rsk_II_1
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh2_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh11_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_2_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_2_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_2_11
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_2_11
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_11_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_11_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_11_11
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_11_11
#print axioms OddMath.Frontier.EKOddRSKIIControls.dual2
#print axioms OddMath.Frontier.EKOddRSKIIControls.first2
#print axioms OddMath.Frontier.EKOddRSKIIControls.odd_rsk_II_2
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh3_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh21_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh111_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_3_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_3_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_3_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_3_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_3_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_3_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_21_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_21_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_21_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_21_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_21_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_21_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_111_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_111_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_111_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_111_21
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_111_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_111_111
#print axioms OddMath.Frontier.EKOddRSKIIControls.dual3
#print axioms OddMath.Frontier.EKOddRSKIIControls.first3
#print axioms OddMath.Frontier.EKOddRSKIIControls.odd_rsk_II_3
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh4_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh31_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh22_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh211_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_T
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_ell
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_rc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_cc
#print axioms OddMath.Frontier.EKOddRSKIIControls.sh1111_ev
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_4_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_4_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_4_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_4_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_4_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_4_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_4_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_4_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_4_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_4_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_31_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_31_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_31_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_31_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_31_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_31_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_31_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_31_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_31_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_31_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_22_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_22_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_22_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_22_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_22_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_22_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_22_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_22_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_22_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_22_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_211_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_211_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_211_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_211_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_211_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_211_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_211_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_211_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_211_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_211_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_1111_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_1111_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_1111_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_1111_31
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_1111_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_1111_22
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_1111_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_1111_211
#print axioms OddMath.Frontier.EKOddRSKIIControls.Me_1111_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.Meh_1111_1111
#print axioms OddMath.Frontier.EKOddRSKIIControls.dual4
#print axioms OddMath.Frontier.EKOddRSKIIControls.first4
#print axioms OddMath.Frontier.EKOddRSKIIControls.odd_rsk_II_4
#print axioms OddMath.Frontier.EKOddRSKIIControls.dual_le_four
#print axioms OddMath.Frontier.EKOddRSKIIControls.first_le_four
#print axioms OddMath.Frontier.EKOddRSKIIControls.cor_3_12_first_le_four
#print axioms OddMath.Frontier.EKOddRSKIIControls.cor_3_12_second_le_four
#print axioms OddMath.Frontier.EKOddRSKIIControls.cor_3_13_le_four
#print axioms OddMath.Frontier.EKOddRSKIIControls.omitted_transpose_3_15_fails
#print axioms OddMath.Frontier.EKOddRSKIIControls.omitted_transpose_3_14_fails

open Lean Elab Command in
/-- Exhaustive per-module axiom sweep; throws on any non-standard axiom. -/
elab "#audit_module_axioms " mod:ident : command => do
  let env ← getEnv
  let modName := mod.getId
  let some idx := env.getModuleIdx? modName
    | throwError "module {modName} is not imported"
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut bad : Array (Name × Array Name) := #[]
  let mut stages : Array Name := #[]
  for n in names do
    let some info := env.find? n | throwError "missing {n}"
    -- Code-generator stages are UNSAFE constants; the kernel forbids any safe declaration
    -- (theorem/def) from referring to them, so they cannot enter a proof.  Only these are
    -- separated, and only if they really are unsafe compiler stages.
    let compiler := (n.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if info.isUnsafe && compiler then
      stages := stages.push n
      continue
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => std.contains a) do
      bad := bad.push (n, axs)
  logInfo m!"{modName}: {names.size} constants; unsafe compiler stages separated: {stages.size} {stages.toList}; audited logical: {names.size - stages.size}; non-standard: {bad.size}"
  unless bad.isEmpty do
    throwError m!"non-standard axioms: {bad.toList}"

#audit_module_axioms OddMath.Frontier.EKOddRSKII
#audit_module_axioms OddMath.Frontier.EKOddRSKIIControls

/-! Headline restatements (types checked against the exact definitions). -/

-- UNCONDITIONAL, every degree
example (d : ℕ) : First312 d ↔ Lemma311 d := first312_iff_lemma311 d
example (d : ℕ) : Second312 d ↔ DualRSK d := second312_iff_dualRSK d
example (μ : YoungDiagram) : EKSemiorthogonality.ell μ.transpose = EKSemiorthogonality.ell μ :=
  ell_transpose μ
-- UNCONDITIONAL, d ≤ 4
example (d : ℕ) (hd : d ≤ 4) : First312 d ∧ Second312 d ∧ OddRSKII d :=
  ⟨first312_le_four d hd, second312_le_four d hd, oddRSKII_le_four d hd⟩
-- CONDITIONAL on exactly (3.13) and (3.11)
example (d : ℕ) (h313 : Lemma311 d) (h311 : Cor39 d) : First312 d ∧ Second312 d ∧ OddRSKII d :=
  ⟨CONDITIONAL_cor_3_12_first d h313, CONDITIONAL_cor_3_12_second d h313 h311,
   CONDITIONAL_cor_3_13 d h313 h311⟩
-- Negative controls (transposition omitted) are refuted
example := EKOddRSKIIControls.omitted_transpose_3_15_fails
example := EKOddRSKIIControls.omitted_transpose_3_14_fails
