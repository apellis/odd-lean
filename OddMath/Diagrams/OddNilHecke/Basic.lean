import StringDiagrams.Interpretation

/-!
# The odd nilHecke category as a presented super 2-category

Source: A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its
diagrammatics*, arXiv:1111.1320v1, §2.2, Proposition 2.1, relations (2.7)–(2.10).

The signature has one region, one strand colour and two generators, a dot and a crossing,
both **odd**. The defining relations imposed here are only those of (2.7), (2.8) and (2.10)
that involve at most one generator at a time on disjoint strands:

* `square`: a double crossing vanishes (`ψ_i ψ_i = 0`, (2.7));
* `braid`: `ψ_i ψ_{i+1} ψ_i = ψ_{i+1} ψ_i ψ_{i+1}` ((2.7));
* `mixedRight`: `x_i ψ_i + ψ_i x_{i+1} = 1` ((2.10));
* `mixedLeft`: `ψ_i x_i + x_{i+1} ψ_i = 1` ((2.10)).

The anticommutation relations (2.8), (2.9) and the spectator case of (2.10) (distinct dots
anticommute, distant crossings anticommute, a dot anticommutes with a crossing it does not
touch) are **not** imposed: they are instances of the super interchange law of
`StringDiagrams.Presentation`, whose Koszul sign is `-1` because both generators are odd.

Conventions. Strands are numbered from `0`: `ψ n i` is the crossing of strands `i` and
`i + 1` among `n`, and `x n i` is a dot on strand `i`; these are EKL's `∂_{i+1}` and
`x_{i+1}`. Products in `End` are composition of operators (`f * g = g ≫ f`: `g` is drawn
below `f`), matching `OddMath.Frontier.NilHeckeAction`, where the left factor acts last.

## Main declarations

* `sig`, `pres R`, `ONH R`, `strands n`: the signature, the presentation over a commutative
  ring `R`, the presented category and the object of `n` strands.
* `x R n i`, `ψ R n i`: a dot and a crossing at a symbolic position in a symbolic width
  (zero when out of range).
* The seven relation families of EKL Prop. 2.1 at every width and position (in
  `OddMath.Diagrams.OddNilHecke.Relations`).
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams

/-- The generators: a dot and a crossing. -/
inductive Gen
  | dot
  | cross
  deriving DecidableEq

/-- Number of strands at the bottom (and top) of a generator. -/
def Gen.arity : Gen → ℕ
  | .dot => 1
  | .cross => 2

/-- The odd nilHecke signature: one region, one colour, an odd dot and an odd crossing. -/
def sig : Signature where
  Region := Unit
  Colour := Unit
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Gen
  dom g := List.replicate g.arity ()
  cod g := List.replicate g.arity ()
  left _ := ()
  right _ := ()
  odd _ := true

instance : Subsingleton sig.Region := inferInstanceAs (Subsingleton Unit)

/-- `n` strands. -/
def strands (n : ℕ) : Obj sig := ⟨(), List.replicate n ()⟩

@[simp] theorem strands_word_length (n : ℕ) : (strands n).word.length = n := by
  simp [strands]

theorem list_unit_ext {l₁ l₂ : List Unit} (h : l₁.length = l₂.length) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih => cases l₂ with
    | nil => simp at h
    | cons b l₂ => rw [ih (by simpa using h)]

/-- Words in the single colour are determined by their length. -/
@[simp] theorem word_eq_iff {l₁ l₂ : List sig.Colour} : l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_unit_ext⟩

theorem obj_ext {a b : Obj sig} (h : a.word.length = b.word.length) : a = b :=
  Obj.ext (Subsingleton.elim (α := Unit) _ _) (list_unit_ext h)

/-- Every object is `strands` of its width. -/
theorem eq_strands (a : Obj sig) : a = strands a.word.length :=
  obj_ext (by simp)

theorem layer_ext {L₁ L₂ : Layer sig} (hl : L₁.left.length = L₂.left.length)
    (hg : L₁.gen = L₂.gen) (hr : L₁.right.length = L₂.right.length) : L₁ = L₂ :=
  Layer.ext (Subsingleton.elim (α := Unit) _ _) (list_unit_ext hl) hg (list_unit_ext hr)

@[simp] theorem sig_dom_length (g : Gen) : (sig.dom g).length = g.arity := by
  simp [sig]

@[simp] theorem sig_cod_length (g : Gen) : (sig.cod g).length = g.arity := by
  simp [sig]

/-- Every layer preserves the number of strands. -/
theorem layer_cod_length (L : Layer sig) : L.cod.word.length = L.dom.word.length := by
  simp

/-- Every diagram preserves the number of strands. -/
theorem chain_length_eq {a b : Obj sig} {ls : List (Layer sig)} (h : Chain a ls b) :
    b.word.length = a.word.length := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, layer_cod_length, h.2.1]

/-- The generator `g` with `i` strands to its left, in a diagram on `n` strands. -/
def lay (n i : ℕ) (g : Gen) : Layer sig :=
  ⟨(), List.replicate i (), g, List.replicate (n - i - g.arity) ()⟩

theorem lay_valid (n i : ℕ) (g : Gen) : (lay n i g).Valid := Layer.valid_of_subsingleton _

theorem lay_dom {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) : (lay n i g).dom = strands n :=
  obj_ext (by simp [lay, Layer.dom, strands, sig]; omega)

theorem lay_cod {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) : (lay n i g).cod = strands n :=
  obj_ext (by simp [lay, Layer.cod, strands, sig]; omega)

/-- The layer `lay n i g` as an endomorphism of `n` strands in the free 2-category. -/
def dlay {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) : strands n ⟶ strands n :=
  Diagram.layer (lay n i g) (lay_valid n i g) (lay_dom h) (lay_cod h)

@[simp] theorem layers_dlay {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) :
    Diagram.layers (dlay h) = [lay n i g] := rfl

/-! ## The presentation -/

/-- The defining relations besides the (super) interchange law. -/
inductive Rel
  | square
  | braid
  | mixedRight
  | mixedLeft

/-- Width of the defining relations. -/
def Rel.width : Rel → ℕ
  | .square => 2
  | .braid => 3
  | .mixedRight => 2
  | .mixedLeft => 2

variable (R : Type*) [CommRing R]

open LinDiagram in
/-- The defining relations, in the free 2-category (`f ≫ g` means `f` below `g`; in `End`,
`f ≫ g = g * f`):
* `square` (`ψ₀ ψ₀ = 0`): `ψ₀ ≫ ψ₀`;
* `braid` (`ψ₀ ψ₁ ψ₀ = ψ₁ ψ₀ ψ₁`): `ψ₀ ≫ ψ₁ ≫ ψ₀ - ψ₁ ≫ ψ₀ ≫ ψ₁`;
* `mixedRight` (`x₀ ψ₀ + ψ₀ x₁ = 1`): `ψ₀ ≫ x₀ + x₁ ≫ ψ₀ - 1`;
* `mixedLeft` (`ψ₀ x₀ + x₁ ψ₀ = 1`): `x₀ ≫ ψ₀ + ψ₀ ≫ x₁ - 1`. -/
def relation : (r : Rel) → LinDiagram R (strands r.width) (strands r.width)
  | .square =>
      of (dlay (g := .cross) (i := 0) (by decide) ≫ dlay (g := .cross) (i := 0) (by decide))
  | .braid =>
      of (dlay (g := .cross) (i := 0) (by decide) ≫ dlay (g := .cross) (i := 1) (by decide) ≫
          dlay (g := .cross) (i := 0) (by decide)) -
        of (dlay (g := .cross) (i := 1) (by decide) ≫ dlay (g := .cross) (i := 0) (by decide) ≫
          dlay (g := .cross) (i := 1) (by decide))
  | .mixedRight =>
      of (dlay (g := .cross) (i := 0) (by decide) ≫ dlay (g := .dot) (i := 0) (by decide)) +
        of (dlay (g := .dot) (i := 1) (by decide) ≫ dlay (g := .cross) (i := 0) (by decide)) -
        of (𝟙 _)
  | .mixedLeft =>
      of (dlay (g := .dot) (i := 0) (by decide) ≫ dlay (g := .cross) (i := 0) (by decide)) +
        of (dlay (g := .cross) (i := 0) (by decide) ≫ dlay (g := .dot) (i := 1) (by decide)) -
        of (𝟙 _)

/-- The odd nilHecke presentation over `R`. -/
def pres : Presentation sig R where
  Rel := Rel
  dom r := strands r.width
  cod r := strands r.width
  rel := relation R

/-- The odd nilHecke category over `R`. -/
abbrev ONH : Type _ := (pres R).Presented

/-- A dot on strand `i` of `n` (zero if `i ≥ n`). -/
def x (n i : ℕ) : End ((pres R).obj (strands n)) :=
  if h : i < n then (pres R).diag (dlay (g := .dot) h) else 0

/-- The crossing of strands `i` and `i + 1` of `n` (zero if `i + 1 ≥ n`). -/
def ψ (n i : ℕ) : End ((pres R).obj (strands n)) :=
  if h : i + 1 < n then (pres R).diag (dlay (g := .cross) h) else 0

theorem x_def {n i : ℕ} (h : i < n) : x R n i = (pres R).diag (dlay (g := .dot) h) := dif_pos h

theorem ψ_def {n i : ℕ} (h : i + 1 < n) : ψ R n i = (pres R).diag (dlay (g := .cross) h) :=
  dif_pos h

theorem x_of_le {n i : ℕ} (h : n ≤ i) : x R n i = 0 := dif_neg (by omega)

theorem ψ_of_le {n i : ℕ} (h : n ≤ i + 1) : ψ R n i = 0 := dif_neg (by omega)

end OddMath.Diagrams.OddNilHecke

end
