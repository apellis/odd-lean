# Braid relations in the functor bicategory

Brundan–Ellis Definition 1.5, the three-strand braid relation (1.9), is
assembled by `ProbeReservoir.braidRelationsOfDenominatorUnits` in
`SwappedAssembly/BraidAssembly.lean`. The scalar ring and the object,
one-morphism and two-morphism universes of the ambient bicategory are
independent parameters throughout its braid dependency modules.

This separation is needed for the chosen cyclotomic construction. Its
ambient bicategory is `PiSCat.{u,u,u+1} k` for `k : Type u`; its objects
live above the scalar universe. Equating every bicategory universe with
the scalar universe prevents the generic braid theorem from applying
to that construction. The separation changes the ambient parameters
and the universes of private algebraic helpers, leaving the braid
statements and mathematical arguments unchanged.

The paired consumer `scripts/NonVacuity/ELVProbeBraidUniverses.lean`
instantiates the full braid theorem in `PiSCat.{0,0,1} ℚ`. It uses the
weighted Boolean datum with one odd colour, the constructed probe and
reservoir families, and their proved crossing inverse and denominator
units. It also applies the braid relation in the resulting layer
representation and retains nonzero vacuum append vectors in both
colours. Its audit traverses all imported braid modules and checks
their owned declarations against the standard axiom allowlist.
