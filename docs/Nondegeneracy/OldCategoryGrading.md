# Integer degree on the old coefficient category

`oldCategoryGradedSupercategory` packages the existing `oldDegree` on
`OldCategory` as an integer graded supercategory. It uses the quotient
image grading already supplied by `ELVOldGrading`; composition adds
degrees, and total-parity projection preserves each integer component.
`oldAppend_mem_degree` proves that the chosen right append preserves
this degree. `oldAppendGraded` retains that same append functor as a
graded superfunctor, with no extra compatibility hypothesis.

This is the source-category prerequisite for the represented
induction-restriction kernels in `ReservoirClosureDegree.md`. The
hypotheses are the actual symmetrizer and homogeneous parameters.
No grading on Homs between arbitrary, ungraded reservoir modules is
introduced. The integer grading of the balanced represented kernel,
the shifted finite matrix, its chosen inverse principal entry, and
source-realized positive closures are further attachment steps.

The paired consumer uses rational asymmetric parameters with two odd
colours and symmetrizer `(2,1)`, both append colours, a mixed word,
arbitrary homogeneous quotient arrows, identity degree zero, and
independent total-parity projection.
