# Separated-factor block inversion

This conditional calculation treats the identity-summand Schur maps for all weight signs. The signed categorical comparison remains to be proved. The factor actions and mixed mates below are explicit inputs; no constructed SKM action or nondegeneracy theorem is asserted.

## Algebraic conventions

Write q=-1 for the odd nilHecke slide and q=1 for the even slide. For each factor, X=EE*, Y=E*E, sigma:X→Y, u:Id→Y, v:X→Id, with dots x on X and y on Y, require

    sigma x = u v + q y sigma.                         (1)

Set u_s=y^s u, v_s=v x^s. The second-factor dots are invertible, so negative subscripts are allowed there. The first-factor dots are nilpotent. All identities use the actual Pi comparisons; the equations below are equations of the resulting ordered maps, not unsigned tensor products.

Use A for the first factor, B for the second. On the diagonal part of EF→FE the matrix is

    [ sigma_A   C       ]
    [ D         sigma_B ],

with the proposed finite ordered mate expansions

    C= sum_(r>=0) q^r u_A,r v_B,-r-1,
    D=-sum_(r>=0) q^(r+1) u_B,-r-1 v_A,r.              (2)

For odd q=-1 these two sums have the same alternating coefficients; for even q=1 their signs are opposite. This distinction matters. Formula (2), especially D, must be proved from the actual adjunctions and parity-line identifications. The block argument assumes (2); it does not establish the adjunction and parity comparisons needed for that formula.

Assume the first-factor companion coefficients and closed loops generate a nilpotent supercentral ideal J, as required by the [nilpotent closed-loop argument](BlockNilpotence.md). Gaussian elimination of the common first-factor summand is valid: the feedback correction lies in J and 1-feedback has a finite geometric inverse.

It suffices to invert the remaining matrix modulo J. An inverse modulo a nilpotent ideal lifts by a finite geometric correction. Here J means finite sums of first-factor central coefficients times second-factor maps; it is stable under all the intervening second-factor maps, with Koszul signs.

## Modulo-J first-factor coordinates

If h_A=-a≤0, use P_A=[sigma_A,u_A,0,...,u_A,a-1]:X_A⊕Id^a→Y_A. Its inverse has crossing component r_A and coordinate rows t_j. The companion recurrence modulo J gives

    t_j u_A,s = delta_js (0≤s<a), and 0 (s≥a),
    v_A,r r_A u_A,s=0.

Thus t_j C=q^j v_B,-j-1. All cap/cup correction terms containing r_A disappear modulo J.

If h_A=a≥0, use Q_A=[sigma_A;v_A,0;...;v_A,a-1]:X_A→Y_A⊕Id^a with inverse columns r_A,k_j. Then

    v_A,s k_j = delta_sj (0≤s<a), and 0 (s≥a),
    v_A,r r_A u_A,s=0.

Consequently D k_j=-q^(j+1)u_B,-j-1. Again the common-summand correction terms vanish modulo J.

## Two invertible-dot lemmas for factor B

Equation (1) gives, for n≥0,

    (q y)^n sigma x^(-n)
      =sigma-sum_(j=0)^(n-1) q^j u_j v_-j-1,         (3)

    (q y)^(-n) sigma x^n
      =sigma+sum_(j=0)^(n-1) q^(j+1) u_-j-1 v_j.    (4)

The signs were derived from (1); no scalar CRT identity is used.

**Negative cap windows.** If Q=[sigma;v_0;...;v_m-1]:X→Y⊕Id^m is invertible and x,y are invertible, then for 0≤s≤m,

    Q_(-s)=[sigma;v_-s;...;v_m-s-1]

is invertible. Induct by one negative shift. As long as the old window contains v_0, the upper-left block of Q_window x Q_window^-1 is q y: the uv_0 term vanishes on the crossing inverse column. It is invertible. The whole conjugate x is invertible, so its Schur complement and the lower-right block of its inverse are invertible. Replacing all cap rows by their composites with x^-1 produces Q_next; relative to Q_window it is block lower triangular with identity upper-left and that invertible lower-right block. The step s=m-1→m is allowed because the old window ends at v_0.

This does NOT claim arbitrary positive shifts of cap windows with unchanged sigma are invertible; the correction in (3)/(4) is essential outside the stated range.

**Negative cup windows.** Dually, if P=[sigma,u_0,...,u_b-1]:X⊕Id^b→Y is invertible, then for 0≤s≤b,

    P_(-s)=[sigma,u_-s,...,u_b-s-1]

is invertible. Conjugate y through the current P; its upper-left block is q x as long as the window contains u_0. Apply the same inverse-Schur argument to the columns.

The zero-length window means sigma itself is invertible.

## All weight signs

All row/column orders below may be changed by signed permutation isomorphisms. The extra source columns when h<0 are the total dotted cups; extra target rows when h>0 are the total dotted caps. These actual identifications are part of the comparison obligation, not a dimension count.

### h_A=-a, h_B=m≥0

Let h=m-a.

If h≥0, after canceling the common A summand, the rows are

    sigma_B;  q^j v_B,-j-1 (0≤j<a);
              v_B,s (0≤s<h).

Up to signed row order this is Q_B,(-a), hence invertible since a≤m.

If h<0, put d=a-m. The d extra total cup columns have identity entries in the first d A-coordinate rows. Eliminate those columns and rows. The remaining matrix has crossing row

    sigma_B-sum_(j=0)^(d-1) q^j u_B,j v_B,-j-1
      =(q y_B)^d sigma_B x_B^-d

and cap rows with indices -a,...,-d-1. Hence it is

    diag((q y_B)^d,1) Q_B,(-m) x_B^-d,

which is invertible.

The second-factor part of the added cup columns is essential here. It produces the correction to sigma_B in (3); it does not vanish merely because the first-factor bubble ideal does. For example, the companion

    T=[1 1; -1 0]

has an invertible leading block and is invertible, but the lower-right entry of T^-2 is zero. With q=-1, a=2 and m=1, the full matrix including its added cup column is instead

    [ 1 1 1 ]
    [-1 0 0 ],
    [ 1 0 1 ]

which is invertible. Replacing its bottom-right cup entry by zero makes it singular. Thus the calculation does not use an unjustified raw window beyond m.

### h_A=-a, h_B=-b≤0

Now h=-(a+b). Eliminate the first a added cup columns using the A-coordinate rows. What remains is

    [ (q y_B)^a sigma_B x_B^-a,
      u_B,a,...,u_B,a+b-1 ].

This is y_B^a P_B with invertible signed scaling of the crossing column and precomposition x_B^-a. It is invertible. No global left adjunction or reversal of the tensor action is assumed.

### h_A=a, h_B=m≥0

The first a total cap rows eliminate the Id^a source columns. The remaining crossing is

    sigma_B+sum_(j=0)^(a-1) q^(j+1) u_B,-j-1 v_B,j
      =(q y_B)^-a sigma_B x_B^a,

with cap rows v_B,a,...,v_B,a+m-1. This is an invertible rescaling of Q_B x_B^a.

### h_A=a, h_B=-b≤0

If a≥b, let d=a-b. Eliminate the first d identity columns with the d added total cap rows. The remaining crossing is (q y_B)^-d sigma_B x_B^d, with cup columns indexed -a,...,-d-1. Up to invertible signed scaling and x_B^d on the crossing source, this is y_B^-d P_B,(-b), hence invertible.

If a<b, the a negative cup columns and the b-a added nonnegative cup columns give exactly the consecutive window -a,...,b-a-1. The reduced map is P_B,(-a), hence invertible.

## Boundary of the conclusion

This proves an abstract all-weight block inversion CONDITIONAL on: actual factor inversions and slides, nilpotence/invertibility of the respective dots, the first-factor central nilpotence lemma, both actual mate expansions (2), and the signed identification of total cups/caps in the block coordinates. It does not establish those categorical comparisons by fiat. It does not compute normalized BE2 vacuum bubbles, prove the factor actions for every allowed parameter, or prove matching independence.

## Exact block calculations

`python3 scripts/Nondegeneracy/separated_block_inversion.py` checks the ordered block equations with pure nilpotent first-factor cup/cap blocks and second-factor companions. It covers both slide signs and all first- and second-factor heights from -4 through 4. It also checks the displayed beyond-window example and detects the mutation deleting its cup term. These are tests of the stated block algebra, not tests of superfunctor coherence or a construction of BE2 actions.

## Actual nonvacuum mate in the degree-two odd towers

Run the separate right-supermodule calculation with its declared SymPy dependency:

```sh
uv run --no-project --script scripts/Nondegeneracy/nonvacuum_rankone.py
```

This uses one odd colour and two factors, at component (1,1), on the regular module of `A_1 ⊗̂ B_1`, where `A_1=Q[x]/(x²)` and `B_1=Q[y]/(y²-1)` with x and y odd. It constructs balanced induction and constrained-Hom coinduction, their actual units and counits, the parity shifts, and the local crossing. The mixed mate is then computed as the cup–crossing–cap composite, not selected by dimension.

The resulting matrix is 36 by 36, of rank 36 and determinant 1; both inverse products are checked. Its central block is 16 by 16, and `D sigma_A^-1 C=0`, so the feedback pivot is `I_8`. Both ordered expansions in (2) are checked against their actual dotted-unit and dotted-counit composites. The separate pure-right mate is 4 by 4, of rank 4 and determinant -1.

The same execution checks both adjunction triangles, the relevant two-strand nilHecke relations, right-linearity and parity of the mate blocks, and supernaturality against all homogeneous basis endomorphisms of the regular input. The restriction-dot square is computed from its definition and has the negative raw-right-multiplication sign. These checks do not establish three-strand coherence, other cyclotomic degrees, independent exterior parameters, or mixed-colour nondegeneracy.
