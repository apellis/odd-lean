# Literal scalar images of the ELV dot polynomials

`ELVScalarPolynomial.lean` computes the actual signed affine scalar specialization at every strand as ordinary evaluation of the literal scalar coefficient polynomial. It identifies both odd and even original first-strand relations, and proves compatibility with rightContext. A concrete rational odd cutoff-four consumer sets chi1=-2 and chi2=1 to obtain precisely (X²-1)².

The polynomial comparisons are full-CI verified in #765. The general cofinal binomial coefficient identity is verified in #813, and descent to the prescribed ordinary cyclotomic quotients in #814. These affine polynomial comparisons do not imply any preservation of positive-weight truncation or integer grading. CI status and integration establish which declarations are checked.
