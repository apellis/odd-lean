# Coefficient-kernel matrix bijectivity

This develops the coefficient-kernel transfer needed for DeformedMatrixComparison, section 4, equations (1.13) and (1.14). The proposed coefficient maps are exactly `actualPositiveKernelMap` and `actualNegativeKernelMap`, with the ordered mate, ordinary unscaled unit/dot columns, and ordinary cap rows.

## Proposed argument

Fix the target old word (t). Use `contentUnitCount` or `contentCapCount` computed from its content; this count remains constant over the source presheaf. For source words with the same content, `oldContent_unitCount_height` or `oldContent_capCount_height` supplies the exact degree equation. The checked odd/even finite component inverses then conjugate through `positiveKernelCoordinates`, `negativeKernelCoordinates`, and `kernelSourceCoordinates`. For source words with different content, every source and target coefficient space vanishes by `ELVOffContentZero`.

The final proposed declarations `actualPositiveKernelMap_bijective` and `actualNegativeKernelMap_bijective` handle every moving colour and every source word. They require only the corresponding sign of the target-content height. They take no assumed inverse, bijectivity, finite-colour, field, or flatness premise.

## Current scope

The new coordinate, conjugation, off-content-matrix, and final bijectivity sources are unfinished and are not scoped-checked results. Their concrete consumer covers both parities, both height signs, reordered same-content endpoints and off-content sources. It is also unfinished. No new source is exported from the umbrella.

The checked source-kernel natural maps and off-content-zero results are retained from their independent developments. This branch proposes an encoding refactor of `ELVMateKernelNaturality`: the coefficient map stores the already prescribed `matrixMateRow` and its source equivalence at literal boxed word endpoints. Its signed tensor and all-arrow covariance statements remain unchanged. The refactor and the boxed `actualMateKernelComponent_row` getter still require strict source and consumer verification.

The separate arbitrary-module coend realizations and forward-matrix comparisons do not by themselves establish the proposed coefficient bijectivity; that implication is not assumed here.
