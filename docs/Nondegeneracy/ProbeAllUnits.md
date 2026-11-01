# All-position units in actual cofinal probes

The source `ProbeAllUnits.lean` performs induction over dot positions simultaneously in every actual word corner. Equal colours use direct nilHecke unit propagation; distinct colours use the source and swapped preceding dots, actual signed crossing slides, and separate positive-dot Q remainders. The first dot is supplied by the prescribed cofinal cyclotomic relation.

The proof is directly over the given commutative ground ring. It uses no finite-dimensionality, residue fields, coefficient truncation, or Nakayama descent. Its hypotheses are the existing datum, scalars, finite colour type, and chosen powers. A concrete two-odd-colour rational three-strand mixed-word consumer supplies all inputs.

This is source in progress until its CI checks pass. It concerns actual algebra dots, not the specialized module-category action or preservation of the whole prescribed inverse matrices. Those action comparisons and the broader fusion/nondegeneracy obligations remain separate.
