# Canonical old-content induction comparison on tensors

Supports SwappedVacuumCoordinates §6 and the pending content-adjunction compatibility step. `oldContentAppendExtensionIso_hom` normalizes the established #910 E comparison as canonical induction-composition flattening followed by canonical insertion. `oldContentAppendExtensionIso_tensor` computes its total map on every nested generator `[h ⊗ [g ⊗ b]]`: the coefficient arrow is `g ≫ h`, and the output is `[g ≫ h ⊗ [id ⊗ b]]` in old append of the content extension. `BalancedInduction.inductionInsertedTensor` fixes this nested value at its induced superspace endpoint. `inductionInsertedTensor_balance` is the existing balance relation in these coordinates.

Both moving parities and full coefficient modules are retained. Source coefficients are unchanged. Producer and paired concrete mixed-parity consumer passed strict direct Lean; all13 owned declarations audited against propext, Classical.choice, Quot.sound. Proofs use separate opaque flatten/insertion equalities rather than increased budgets. Full integrated CI pending.

The actual E/F unit and counit compatibility remains to be proved. No completed content factor action is claimed.
