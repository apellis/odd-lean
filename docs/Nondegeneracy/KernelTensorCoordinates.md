# Kernel tensor endpoints of the prescribed matrices

The all-module step of [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4, uses explicit coefficient-kernel tensor coordinates. ELVKernelTensorCoordinates supplies these in the nested namespace CyclotomicCrossingTensor.TensorMatrixCoordinates, distinct from coefficient-level coordinates.

The identity-Hom kernel evaluates on M by the existing induction counit; identity insertion is its inverse by fullness of the identity functor. The IndRes kernel evaluates by the checked double-coend equivalence, and the upper Hom kernel is the existing balanced-induction quotient.

Finite source and target kernel products commute with tensor by piEquiv. Each slot then uses exactly the named canonical parity isomorphism from the actual shifted family: the first source/target isomorphism for the mate, and homParityShiftDatum for each ordinary unit/cap slot. Thus positiveKernelCoordinates and negativeKernelCoordinates land in the literal unitMatrixSourceSpace and capMatrixTargetSpace used by the actual finite matrices. These coordinates introduce no rescaling of unit columns or cap rows.

The producer and concrete closed old-quotient consumer await checking. Literal forward matrix identification and coefficientwise matrix bijectivity are separate inputs. Once they are supplied, these underlying linear equivalences transfer bijectivity to all M; the actual all-M forward matrices already have an independent evenness proof, so no abstract categorical colimit assumption is needed.
