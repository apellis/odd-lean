import OddMath.Frontier.OddLREliminationControls
import OddMath.Frontier.OddLRElimination

/-! Axiom audit: every owned declaration (production and controls)
must depend only on propext, Classical.choice, Quot.sound.  Main statements re-checked below. -/

#print axioms OddMath.Frontier.OddLRElimination.rowFun
#print axioms OddMath.Frontier.OddLRElimination.rowFun_antitone
#print axioms OddMath.Frontier.OddLRElimination.rowFun_pos
#print axioms OddMath.Frontier.OddLRElimination.cellsOf
#print axioms OddMath.Frontier.OddLRElimination.mem_cellsOf
#print axioms OddMath.Frontier.OddLRElimination.toYoung
#print axioms OddMath.Frontier.OddLRElimination.toYoung_column
#print axioms OddMath.Frontier.OddLRElimination.ofYoung
#print axioms OddMath.Frontier.OddLRElimination.toYoung_ofYoung
#print axioms OddMath.Frontier.OddLRElimination.directNorth_column
#print axioms OddMath.Frontier.OddLRElimination.sp_column
#print axioms OddMath.Frontier.OddLRElimination.lemma_3_5
#print axioms OddMath.Frontier.OddLRElimination.colLen
#print axioms OddMath.Frontier.OddLRElimination.colLen_le
#print axioms OddMath.Frontier.OddLRElimination.colVec
#print axioms OddMath.Frontier.OddLRElimination.le_width
#print axioms OddMath.Frontier.OddLRElimination.trunc
#print axioms OddMath.Frontier.OddLRElimination.topSet
#print axioms OddMath.Frontier.OddLRElimination.increment_trunc_top
#print axioms OddMath.Frontier.OddLRElimination.topStrip
#print axioms OddMath.Frontier.OddLRElimination.strip_top_eq
#print axioms OddMath.Frontier.OddLRElimination.increment_inj
#print axioms OddMath.Frontier.OddLRElimination.strip_le
#print axioms OddMath.Frontier.OddLRElimination.subsetExp_iff
#print axioms OddMath.Frontier.OddLRElimination.downset_eq
#print axioms OddMath.Frontier.OddLRElimination.strip_lex
#print axioms OddMath.Frontier.OddLRElimination.RightPieri
#print axioms OddMath.Frontier.OddLRElimination.column_zero_eq
#print axioms OddMath.Frontier.OddLRElimination.isolate
#print axioms OddMath.Frontier.OddLRElimination.eliminate
#print axioms OddMath.Frontier.OddLRElimination.schur_rightPieri
#print axioms OddMath.Frontier.OddLRElimination.Pieri310Bounded
#print axioms OddMath.Frontier.OddLRElimination.sp_eq_schur_of_pieri310Bounded
#print axioms OddMath.Frontier.OddLRElimination.sp_eq_schur_diagram_of_pieri310Bounded
#print axioms OddMath.Frontier.OddLRElimination.belowRows
#print axioms OddMath.Frontier.OddLRElimination.rowInc
#print axioms OddMath.Frontier.OddLRElimination.diagramOf
#print axioms OddMath.Frontier.OddLRElimination.mem_diagramOf
#print axioms OddMath.Frontier.OddLRElimination.stripRows
#print axioms OddMath.Frontier.OddLRElimination.addStrip
#print axioms OddMath.Frontier.OddLRElimination.rowLen_pos
#print axioms OddMath.Frontier.OddLRElimination.rowLen_beyond
#print axioms OddMath.Frontier.OddLRElimination.stripRows_bound
#print axioms OddMath.Frontier.OddLRElimination.stripRows_complete
#print axioms OddMath.Frontier.OddLRElimination.mem_addStrip
#print axioms OddMath.Frontier.OddLRElimination.Pieri310
#print axioms OddMath.Frontier.OddLRElimination.sp_tall
#print axioms OddMath.Frontier.OddLRElimination.rowLen_toYoung
#print axioms OddMath.Frontier.OddLRElimination.colLen_toYoung
#print axioms OddMath.Frontier.OddLRElimination.belowRows_toYoung
#print axioms OddMath.Frontier.OddLRElimination.strRows
#print axioms OddMath.Frontier.OddLRElimination.rowInc_strRows
#print axioms OddMath.Frontier.OddLRElimination.strRows_mem
#print axioms OddMath.Frontier.OddLRElimination.finRows
#print axioms OddMath.Frontier.OddLRElimination.finRows_map
#print axioms OddMath.Frontier.OddLRElimination.finRows_strip
#print axioms OddMath.Frontier.OddLRElimination.pieri310_bounded
#print axioms OddMath.Frontier.OddLRElimination.sp_eq_schur_of_pieri310
#print axioms OddMath.Frontier.OddLRElimination.sp_eq_schur_diagram_of_pieri310

#print axioms OddMath.Frontier.OddLREliminationControls.north_col2
#print axioms OddMath.Frontier.OddLREliminationControls.dnorth_col2
#print axioms OddMath.Frontier.OddLREliminationControls.north_col3
#print axioms OddMath.Frontier.OddLREliminationControls.dnorth_col3
#print axioms OddMath.Frontier.OddLREliminationControls.north_col1
#print axioms OddMath.Frontier.OddLREliminationControls.dnorth_col1
#print axioms OddMath.Frontier.OddLREliminationControls.north_col0
#print axioms OddMath.Frontier.OddLREliminationControls.dnorth_col0
#print axioms OddMath.Frontier.OddLREliminationControls.sp_col_of
#print axioms OddMath.Frontier.OddLREliminationControls.sp_eq_schur_col_N3
#print axioms OddMath.Frontier.OddLREliminationControls.sp_eq_schur_col_N2
#print axioms OddMath.Frontier.OddLREliminationControls.col3_sign
#print axioms OddMath.Frontier.OddLREliminationControls.colLenC
#print axioms OddMath.Frontier.OddLREliminationControls.lamC
#print axioms OddMath.Frontier.OddLREliminationControls.betaC
#print axioms OddMath.Frontier.OddLREliminationControls.nuC
#print axioms OddMath.Frontier.OddLREliminationControls.strip_terms
#print axioms OddMath.Frontier.OddLREliminationControls.lam_decomp
#print axioms OddMath.Frontier.OddLREliminationControls.column_lex_holds
#print axioms OddMath.Frontier.OddLREliminationControls.row_lex_variant_fails
#print axioms OddMath.Frontier.OddLREliminationControls.shifted_column_variant_fails

namespace OddMath.Frontier.OddLREliminationAudit
open OddMath.Frontier OddSymmetrizer OddSchurPieri OddLRElimination

/-- (a) Lemma 3.5, restated. -/
example (n k : ℕ) (hk : k ≤ n+2) :
    CompleteTableauExpansion.sp (n+2) (TableauExtremal.columnShape k) = schur n (column n k) ∧
    schur n (column n k) =
      (-1 : ℤ) ^ (k * (k-1) / 2) • FiniteCompleteElementary.elementaryPoly (n+2) k := by
  have h := lemma_3_5 n k hk
  rw [toYoung_column n k hk] at h
  exact h

/-- (b) abstract elimination, restated. -/
example (n : ℕ) {R : Type*} [Ring R] (F G : PartitionExponent n → R)
    (hcol : ∀ k, k ≤ n+2 → F (column n k) = G (column n k))
    (hF : RightPieri F) (hG : RightPieri G) : F = G := funext (eliminate F G hcol hF hG)

/-- (c) CONDITIONAL on the named all-shapes printed (3.10) hypothesis only. -/
example (n : ℕ) (h310 : Pieri310 (n+2)) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n+2) :
    CompleteTableauExpansion.sp (n+2) μ = schur n (ofYoung μ) :=
  sp_eq_schur_diagram_of_pieri310 n h310 μ hμ

end OddMath.Frontier.OddLREliminationAudit
