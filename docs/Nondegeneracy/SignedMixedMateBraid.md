# Three right adjunctions and the mixed braid

**Status: proposed written proof; not a Lean theorem.** The two-mate expansion
has a Koszul coefficient, but the resulting mixed braid and `sig_capCross`
have coefficient **one**, also for odd crossings. This supplies the general
mathematical input to the crossing component of cap-swap, not the remaining
cap-swap calculation or the left-adjunction triangles.

## 1. Data, conventions and exact statement

Work in a linear 2-supercategory over a commutative ring. Composition `f ≫ g`
is diagrammatic (first `f`). Let

```
E₁ : a → b, E₂ : b → c, E₃ : c → d,
F₁ : b → a, F₂ : c → b, F₃ : d → c,
Aⱼ : SuperAdjunction Eⱼ Fⱼ,
ηⱼ = Aⱼ.unit : 1 → Eⱼ Fⱼ,
εⱼ = Aⱼ.counit : Fⱼ Eⱼ → 1.
```

The units and counits are even. Both triangles belong to these *right*
adjunctions. In particular `A₂.left_triangle` means the E₂ triangle of
`E₂ ⊣ F₂`; it does NOT mean the left-adjunction conclusion being constructed.
Let `t₁₂ : E₁ E₂ → E₁ E₂` and `t₂₃ : E₂ E₃ → E₂ E₃` have parity `p`.
Write `s = koszulSign p p` (integer scalar action). Put

```
σ₁₂ = rouquierMate A₁ A₂ t₁₂ : F₁ E₁ → E₂ F₂,
σ₂₃ = rouquierMate A₂ A₃ t₂₃ : F₂ E₂ → E₃ F₃.
```

These are the prescribed cup–crossing–cap maps, not extra chosen maps.
Their parity is `p`, directly from the displayed definition of `rouquierMate`.
Use `α`, `λ`, `ρ` for associator, left unitor, right unitor. On
`T = E₁ ≫ (E₂ ≫ E₃)` define

```
A = α(E₁,E₂,E₃).inv ≫ (t₁₂ ▷ E₃) ≫ α(E₁,E₂,E₃).hom,
B = E₁ ◁ t₂₃.
hB : B ≫ A ≫ B = A ≫ B ≫ A.
```

This is precisely `RouquierFamily.braid`, with no sign on either side.
On `X = (F₁ ≫ E₁) ≫ E₂` and `Y = E₂ ≫ (E₃ ≫ F₃)` define

```
C = α(F₁,E₁,E₂).hom ≫ (F₁ ◁ t₁₂) ≫ α(F₁,E₁,E₂).inv : X → X,
D = α(E₂,E₃,F₃).inv ≫ (t₂₃ ▷ F₃) ≫ α(E₂,E₃,F₃).hom : Y → Y,
P = (σ₁₂ ▷ E₂) ≫ α(E₂,F₂,E₂).hom ≫ (E₂ ◁ σ₂₃) : X → Y.
```

**Mixed braid:**

```
C ≫ P = P ≫ D.                                      (MB)
```

All bracketing in this statement is explicit. No assumption on dots, weights,
square-zero crossings, inversion matrices, left cups/caps, or left zigzags is
needed. Indeed, the direct proof below uses only the E₂ triangle, evenness of
`η₂, ε₂, ε₁, η₃`, homogeneity of the two crossings, and `hB`.

## 2. A fully typed outer mate

Put `g = E₁ ≫ E₂ : a → c` and `h = E₂ ≫ E₃ : b → d`.
For `r : g ≫ E₃ → E₁ ≫ h` define the rectangular outer mate explicitly:

```
H(r) = F₁ ◁ (ρ(g).inv ≫ (g ◁ η₃) ≫ α(g,E₃,F₃).inv ≫
                (r ▷ F₃) ≫ α(E₁,h,F₃).hom) ≫
       α(F₁,E₁,h ≫ F₃).inv ≫ (ε₁ ▷ (h ≫ F₃)) ≫ λ(h ≫ F₃).hom
       : F₁ ≫ g → h ≫ F₃.
M(z) = α(F₁,E₁,E₂).hom ≫ H(α(E₁,E₂,E₃).hom ≫ z) ≫
       α(E₂,E₃,F₃).hom : X → Y.
```

The input of `H` has type
`(E₁ ≫ E₂) ≫ E₃ → E₁ ≫ (E₂ ≫ E₃)`; its output has type
`F₁ ≫ (E₁ ≫ E₂) → (E₂ ≫ E₃) ≫ F₃`. Thus every associator
in `M` is forced, not an implicit identification. This is the composite of
the post-adjunction transpose for `A₃` and the pre-adjunction transpose for
`A₁`, with their intervening associator. It is a Hom-space bijection under
the stated right adjunctions. It is linear directly from the formula.

**API distinction:** existing `homMateEquiv` specializes to adjacent
adjunctions sharing a middle object. Here `A₁` and `A₃` need not share that
object, so `homMateEquiv A₁ A₃` is not a well-typed application of the current
API. `H` is its explicitly defined rectangular generalization, not a new
arbitrarily chosen crossing. One may prove (SS) directly from the displayed
formula without first extending the Hom-equivalence API.

For displaying its expansion, a word denotes its right-associated composite.
An elementary layer is conjugated by the canonical even associators/unitors
to that bracketing. This convention is only notation: equivalently insert
`α.hom/α.inv` until the operated subword is bracketed together, apply the
specified whiskering, and restore right bracketing; remove an empty subword
with `λ.hom` or `ρ.hom`. Coherence of these **even structural maps** makes
this independent of the chosen reassociation path. Naturality with a single
homogeneous map is used where necessary; no ordinary interchange of two odd
maps is included in this convention.

Under this convention `M(z)` is the following typed chain, with the initial
`X → F₁(E₁E₂)` and final output bracketing as above:

```
F₁ E₁ E₂ -- insert η₃ on the right --> F₁ E₁ E₂ E₃ F₃
          -- F₁ ◁ z ▷ F₃ ----------> F₁ E₁ E₂ E₃ F₃
          -- close ε₁ on the left --> E₂ E₃ F₃.
```

Expansion of the definitions of the two Hom adjunctions gives this formula;
the prefix and suffix use only even coherence, exactly as in
`RouquierMate.homMateEquiv_eq` (the declaration is `homMateEquiv_eq` in
namespace `OddMath.SKM`).

Naturality gives the two identities

```
C ≫ M(z) = M(A ≫ z),       M(z) ≫ D = M(z ≫ B).       (N)
```

For the first, move `F₁ ◁ t₁₂` past the insertion of `η₃`, costing
`(-1)^(p·0)=1`; the associator naturality is precisely the definition of `A`.
For the second, move `t₂₃ ▷ F₃` past the closure `ε₁`, costing
`(-1)^(0·p)=1`; the definition of `D` gives the output associators. These are
the rectangular analogues of `homMateEquiv_left` and `homMateEquiv_right`,
with the same direct naturality proof. Neither identity moves a crossing
past another crossing.

## 3. The signed two-mate expansion

The necessary identity is

```
P = s • M(B ≫ A).                                    (SS)
```

Here is a layer-by-layer proof and the complete interchange ledger.
First record the uncapped-to-capped pitchfork, with all endpoint coherence:

```
(σ₁₂ ▷ E₂) ≫ α(E₂,F₂,E₂).hom ≫ (E₂ ◁ ε₂) ≫ ρ(E₂).hom
 = α(F₁,E₁,E₂).hom ≫ (F₁ ◁ t₁₂) ≫ α(F₁,E₁,E₂).inv
     ≫ (ε₁ ▷ E₂) ≫ λ(E₂).hom.                       (PF)
```

To prove (PF), expand `σ₁₂`, obtaining the chronological layers
`η₂, t₁₂, ε₁, ε₂` on the word `F₁ E₁ E₂ F₂ E₂` after insertion.
Move the closure `ε₂` before `ε₁` (disjoint supports, exponent `0·0`).
Move it before `t₁₂` (supports `F₂ E₂` and `E₁ E₂`, exponent `p·0`).
The adjacent insertion/closure now constitute the E₂ triangle of `A₂`,
whiskered by `F₁ E₁`; remove it. The remaining layers are `t₁₂, ε₁`.
Associator and unitor naturality give exactly the two sides displayed in
(PF). These are its only two interchanges.

Now expand only `σ₂₃` in `P`. The chronological layers are

```
σ₁₂ on F₁ E₁;  insert η₃ after E₂;
t₂₃ on the last E₂ E₃;  close ε₂ on F₂ E₂.
```

1. Move `η₃` before `σ₁₂`. They have disjoint supports; the exponent
   is `p·0`, so the coefficient is one. The word after insertion is
   `F₁ E₁ E₂ E₃ F₃`.
2. Move the layer `t₂₃` before `σ₁₂`. On this word their supports are
   respectively the trailing `E₂ E₃` and the initial `F₁ E₁`.
   Super interchange contributes **exactly `s`**. After this interchange
   the chronological crossing order is `t₂₃`, then `σ₁₂`.
3. Apply (PF) to `σ₁₂` followed by `ε₂`, with spectator `E₃ F₃`.
   Its two interchange coefficients are one, as proved above.

The resulting chronological layers are `η₃, t₂₃, t₁₂, ε₁`, exactly
`M(B ≫ A)`. Thus (SS) follows. This enumerates all four interchanges
in the expansion: exponents `p·0`, `p·p`, `0·0`, `p·0`. Associators,
unitors, whiskering functoriality and the right-adjunction triangle account
for all other steps. In particular using the ordinary even `sigma_sigma`
without its new coefficient would be incorrect.

## 4. Proof of the mixed braid

Use linearity, (N), (SS), and the specified upward braid:

```
C ≫ P = s • (C ≫ M(B ≫ A))
      = s • M(A ≫ B ≫ A)
      = s • M(B ≫ A ≫ B)       by hB
      = s • (M(B ≫ A) ≫ D)
      = P ≫ D.
```

There is **no global `s` in (MB)**. Both sides acquire the same single
factor `s` when expanded. There is not even a need to divide by a scalar:
the final equality simply substitutes (SS) back. For even crossings (SS)
is the ordinary two-mate formula; for odd crossings it has a minus sign on
both expanded sides of (MB). No finite-dimensional model is used.

## 5. Consequence for the prescribed left cap

Let `L : SuperRouquierLoc A₁ A₂ x₁ x₂ t₁₂ p h` and
`U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ p h'`. Thus `L.sig = σ₁₂`
and `U.sig = σ₂₃`. Define the cap composite exactly as in the pitchfork
calculation:

```
U.capCross = α(E₂,F₂,E₂).hom ≫ (E₂ ◁ U.sig) ≫
  α(E₂,E₃,F₃).inv ≫ (t₂₃ ▷ F₃) ≫ α(E₂,E₃,F₃).hom ≫
  (E₂ ◁ U.capL) ≫ ρ(E₂).hom.
```

Postcompose (MB) with `K = (E₂ ◁ U.capL) ≫ ρ(E₂).hom : Y → E₂`
and reverse the resulting equality. Expanding `C,P,D` gives

```
(L.sig ▷ E₂) ≫ U.capCross =
  α(F₁,E₁,E₂).hom ≫ (F₁ ◁ t₁₂) ≫ α(F₁,E₁,E₂).inv ≫
  (L.sig ▷ E₂) ≫ α(E₂,F₂,E₂).hom ≫
  (E₂ ◁ (U.sig ≫ U.capL)) ≫ ρ(E₂).hom.             (SC)
```

Only associativity and whiskering functoriality are used in this last step.
In particular `U.capL`, possibly odd, is never interchanged with another
map. Its parity adds no sign. Formula (SC) is valid at arbitrary `h,h'`;
no weight relation or low-dot truncation is used. The relation between
successive heights becomes relevant only in the later cap-swap proof.

## 6. Lean targets and dependency boundary

Suggested generic declarations are `rouquierMate_comp_mate` for (SS) and
`rouquierMate_mixed_braid` for (MB), followed by
`SuperRouquierLoc.sig_capCross` for (SC). Prove the signed expansion in
`TwoSupercategory`, using `super_interchange` for its unique odd–odd move;
use the even underlying bicategory only for the structural prefix/suffix.
`homMateEquiv_left/right` provide the adjacent-object templates for the
rectangular outer naturality laws; the displayed formula for `H` supplies
the required generalization. No formal implementation or new kernel-checked
claim is made here.

The missing hypothesis in two *isolated* `SuperRouquierLoc` records is the
explicit cross-edge braid `hB`: neither record contains it. It is already
supplied by a `RouquierFamily`. This is a genuine input to (MB), not a new
left-zigzag or cap-swap assumption. Local inversion data are irrelevant to
(MB) and enter (SC) only to specify the prescribed cap. The full cap-swap,
its weight-dependent correction, and the left-adjunction triangles remain
downstream obligations.

Code comparisons read for this proof:

- `Categorification/TwoRep/RightwardCrossing.lean`, `sigma_eq`,
  `pitchfork_cap`, `sigma_sigma`, `mixed_braid` (lines 139–252).
- `Categorification/TwoRep/RouqPitchfork.lean`, `capCross` and
  `sig_capCross` (lines 97–132).
- `OddMath/SKM/RouquierData.lean`, `SuperAdjunction`, `rouquierMate`,
  `SuperRouquierLoc`, `RouquierFamily.braid`.
- `OddMath/SKM/RouquierMate.lean`, `homMateEquiv`, `homMateEquiv_eq`,
  `homMateEquiv_left`, `homMateEquiv_right`.
- `OddMath/SKM/RouquierInverseRelations.lean`, `SuperRouquierLoc.sig`.

These are implementation comparisons, not claims to have checked additional
paper locators. The proof above concerns exactly the same-colour braid
specified here, not an unrestricted multicolour braid with correction terms.
