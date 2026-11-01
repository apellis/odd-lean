# Shifted coefficient and actual parity restriction

Status: proposed Lean implementation; unchecked. Target: DeformedMatrixComparison (3), (5).

ELVOldAppendSuperfunctor equips the existing full-coefficient old append with its actual superfunctor structure. ELVShiftedCoefficientComparison compares the prescribed coefficient(1) functor with actual parity-shifted restriction of oldRepresentable. Their underlying coefficient map is identity, their projections agree, and the defining actions agree by append/representable preservation of total twist. The ordinary natural isomorphism has even components.

Next: package this even comparison as an actual supermodule isomorphism, apply existing balanced induction to it, and compose with the canonical actual-module parity source comparison. Compare the resulting whole actual counit with the raw input contraction; then transport through coefficient truncation and exact content. No arbitrary kernel comparison or completed factor action is claimed.
