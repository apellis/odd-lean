import OddMath.Diagrams.OddNilHecke.Relations
import OddMath.Frontier.NilHeckeAction

/-!
# The polynomial representation of the diagrammatic odd nilHecke category

The object with `m` strands is sent to the `ℤ`-module `SkewPolynomial m` of odd
polynomials in `m` variables; a dot on strand `i` acts by left multiplication by the
generator `x_i`, and a crossing of strands `i`, `i + 1` acts by odd-lean's all-rank odd
divided difference `OddMath.Frontier.AllRankDivided.divided` (EKL, arXiv:1111.1320v1,
§2.1.1, (2.4)–(2.5), and §2.2). On `n + 2` strands these are exactly the operators of
`OddMath.Frontier.NilHeckeAction.freeAction n`.

The interpretation (`interp`) has width-dependent objects. The layer operators are defined
once, as a function of a width `m` and a position `i` (`layerOp m i g`); every diagram is
then computed, after transport along the equality of its width with `m`, as the product of
the operators of its layers (`conj_map`). This reduces the soundness conditions of
`StringDiagrams.Presentation.lift` to operator identities at width `m = k + 2`, which are the
images of odd-lean's relators under `freeAction k` and are discharged by
`OddMath.Frontier.NilHeckeAction.relation_killed`: the defining relations at every whiskered
position, and the three anticommutation relators for every whiskered instance of the super
interchange law (Koszul sign `-1`).

## Main declarations

* `layerOp m i g`: the operator of generator `g` with `i` strands to its left, on `m`
  strands.
* `interp`: the interpretation in `ModuleCat ℤ`; `respects`: soundness hypotheses.
* `polyFunctor : ONH ℤ ⥤ ModuleCat ℤ`: the representation of the presented category.
* `realize m : End (strands m) →+* Module.End ℤ (SkewPolynomial m)`, with
  `realize_x`, `realize_ψ` computing it on dots and crossings.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams
open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier NilHeckeAction

/-- The `ℤ`-module of odd polynomials in `k` variables, as an object of `ModuleCat ℤ`. -/
abbrev polyModule (k : ℕ) : ModuleCat.{0} ℤ := ModuleCat.of ℤ (SkewPolynomial k)

/-- A dot on strand `i` of `m`: left multiplication by the generator `x_i` (zero if out of
range). -/
def dotOp (m i : ℕ) : Module.End ℤ (SkewPolynomial m) :=
  if h : i < m then LinearMap.mulLeft ℤ (generator ⟨i, h⟩) else 0

/-- A crossing of strands `i` and `i + 1` of `m`: the odd divided difference `∂_i` (zero if
out of range). -/
def crossOp : (m : ℕ) → ℕ → Module.End ℤ (SkewPolynomial m)
  | k + 2, i => if h : i < k + 1 then AllRankDivided.divided ⟨i, h⟩ else 0
  | _, _ => 0

/-- The operator of the generator `g` with `i` strands to its left, on `m` strands. -/
def layerOp (m i : ℕ) : Gen → Module.End ℤ (SkewPolynomial m)
  | .dot => dotOp m i
  | .cross => crossOp m i

theorem layerOp_dot (k p : ℕ) (h : p < k + 2) :
    layerOp (k + 2) p .dot = freeAction k (dotFree k ⟨p, h⟩) := by
  simp [layerOp, dotOp, h, dotOperator]

theorem layerOp_cross (k p : ℕ) (h : p < k + 1) :
    layerOp (k + 2) p .cross = freeAction k (crossingFree k ⟨p, h⟩) := by
  simp [layerOp, crossOp, h]

/-! ## Operator identities at arbitrary width and position -/

section Operators

theorem exists_add_two {m p : ℕ} (h : p + 2 ≤ m) : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩

theorem op_square {m p : ℕ} (h : p + 2 ≤ m) :
    layerOp m p .cross * layerOp m p .cross = 0 := by
  obtain ⟨k, rfl⟩ := exists_add_two h
  rw [layerOp_cross k p (by omega), ← map_mul]
  exact relation_killed k _ (Relator.square ⟨p, by omega⟩)

theorem op_braid {m p : ℕ} (h : p + 3 ≤ m) :
    layerOp m p .cross * layerOp m (p + 1) .cross * layerOp m p .cross -
      layerOp m (p + 1) .cross * layerOp m p .cross * layerOp m (p + 1) .cross = 0 := by
  obtain ⟨k, rfl⟩ := exists_add_two (show p + 2 ≤ m by omega)
  rw [layerOp_cross k p (by omega), layerOp_cross k (p + 1) (by omega), ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, ← map_sub]
  exact relation_killed k _ (Relator.braid ⟨p, by omega⟩ ⟨p + 1, by omega⟩ rfl)

theorem op_mixedRight {m p : ℕ} (h : p + 2 ≤ m) :
    layerOp m p .dot * layerOp m p .cross + layerOp m p .cross * layerOp m (p + 1) .dot -
      1 = 0 := by
  obtain ⟨k, rfl⟩ := exists_add_two h
  rw [layerOp_cross k p (by omega), layerOp_dot k p (by omega),
    layerOp_dot k (p + 1) (by omega), ← map_mul, ← map_mul, ← map_add,
    ← map_one (freeAction k), ← map_sub]
  exact relation_killed k _ (Relator.mixedRight ⟨p, by omega⟩)

theorem op_mixedLeft {m p : ℕ} (h : p + 2 ≤ m) :
    layerOp m p .cross * layerOp m p .dot + layerOp m (p + 1) .dot * layerOp m p .cross -
      1 = 0 := by
  obtain ⟨k, rfl⟩ := exists_add_two h
  rw [layerOp_cross k p (by omega), layerOp_dot k p (by omega),
    layerOp_dot k (p + 1) (by omega), ← map_mul, ← map_mul, ← map_add,
    ← map_one (freeAction k), ← map_sub]
  exact relation_killed k _ (Relator.mixedLeft ⟨p, by omega⟩)

/-- The operators of odd generators at disjoint positions anticommute: EKL (2.8), (2.9) and
the spectator case of (2.10). -/
theorem op_interchange (g h : Gen) {m p q : ℕ} (hpq : p + g.arity ≤ q)
    (hq : q + h.arity ≤ m) :
    layerOp m q h * layerOp m p g + layerOp m p g * layerOp m q h = 0 := by
  cases g <;> cases h <;> simp only [Gen.arity] at hpq hq
  · obtain ⟨k, rfl⟩ := exists_add_two (show 0 + 2 ≤ m by omega)
    rw [layerOp_dot k p (by omega), layerOp_dot k q (by omega), ← map_mul, ← map_mul,
      ← map_add]
    exact relation_killed k _ (Relator.dots ⟨q, by omega⟩ ⟨p, by omega⟩
      (Fin.ne_of_val_ne (by simp; omega)))
  · obtain ⟨k, rfl⟩ := exists_add_two (show 0 + 2 ≤ m by omega)
    rw [layerOp_dot k p (by omega), layerOp_cross k q (by omega), ← map_mul, ← map_mul,
      add_comm (freeAction k _), ← map_add]
    exact relation_killed k _ (Relator.spectator ⟨q, by omega⟩ ⟨p, by omega⟩
      (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega)))
  · obtain ⟨k, rfl⟩ := exists_add_two (show 0 + 2 ≤ m by omega)
    rw [layerOp_cross k p (by omega), layerOp_dot k q (by omega), ← map_mul, ← map_mul,
      ← map_add]
    exact relation_killed k _ (Relator.spectator ⟨p, by omega⟩ ⟨q, by omega⟩
      (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega)))
  · obtain ⟨k, rfl⟩ := exists_add_two (show 0 + 2 ≤ m by omega)
    rw [layerOp_cross k p (by omega), layerOp_cross k q (by omega), ← map_mul, ← map_mul,
      ← map_add]
    exact relation_killed k _ (Relator.distant ⟨q, by omega⟩ ⟨p, by omega⟩
      (Or.inr (by simp; omega)))

end Operators

/-! ## The interpretation -/

/-- The polynomial interpretation: `m` strands go to `SkewPolynomial m`, a layer to the
operator of its generator at its position. -/
abbrev interp : Interpretation sig (ModuleCat.{0} ℤ) where
  obj a := polyModule a.word.length
  layer L _ := ModuleCat.ofHom (layerOp L.dom.word.length L.left.length L.gen) ≫
    eqToHom (congrArg polyModule (layer_cod_length L).symm)

/-- The product of the operators of a list of layers on `m` strands; the first (bottom)
layer acts first. -/
def opList (m : ℕ) : List (Layer sig) → Module.End ℤ (SkewPolynomial m)
  | [] => 1
  | L :: ls => opList m ls * layerOp m L.left.length L.gen

@[simp] theorem opList_nil (m : ℕ) : opList m [] = 1 := rfl

@[simp] theorem opList_cons (m : ℕ) (L : Layer sig) (ls : List (Layer sig)) :
    opList m (L :: ls) = opList m ls * layerOp m L.left.length L.gen := rfl

/-- The operator of a linear combination of diagrams, on `m` strands. -/
def linOp (m : ℕ) {a b : Obj sig} (X : LinDiagram ℤ a b) : Module.End ℤ (SkewPolynomial m) :=
  Finsupp.linearCombination ℤ (fun d : a ⟶ b => opList m (Diagram.layers d)) X

section LinOp

variable (m : ℕ) {a b : Obj sig}

@[simp] theorem linOp_zero : linOp m (0 : LinDiagram ℤ a b) = 0 := map_zero _

@[simp] theorem linOp_add (X Y : LinDiagram ℤ a b) : linOp m (X + Y) = linOp m X + linOp m Y :=
  map_add _ X Y

@[simp] theorem linOp_sub (X Y : LinDiagram ℤ a b) : linOp m (X - Y) = linOp m X - linOp m Y :=
  map_sub _ X Y

@[simp] theorem linOp_single (d : a ⟶ b) (r : ℤ) :
    linOp m (Finsupp.single d r : LinDiagram ℤ a b) = r • opList m (Diagram.layers d) :=
  Finsupp.linearCombination_single ℤ r d

@[simp] theorem linOp_of (d : a ⟶ b) :
    linOp m (LinDiagram.of d : LinDiagram ℤ a b) = opList m (Diagram.layers d) := by
  rw [LinDiagram.of, linOp_single, one_smul]

end LinOp

/-- Transport of a morphism between modules equal to `polyModule m` to an endomorphism of
`polyModule m`. -/
def conj {m : ℕ} {A B : ModuleCat.{0} ℤ} (hA : polyModule m = A) (hB : B = polyModule m)
    (X : A ⟶ B) : polyModule m ⟶ polyModule m :=
  eqToHom hA ≫ X ≫ eqToHom hB

section Conj

variable {m : ℕ} {A B C : ModuleCat.{0} ℤ} (hA : polyModule m = A) (hB : B = polyModule m)

@[simp] theorem conj_add (X Y : A ⟶ B) : conj hA hB (X + Y) = conj hA hB X + conj hA hB Y := by
  simp [conj]

@[simp] theorem conj_zero : conj hA hB (0 : A ⟶ B) = 0 := by
  simp [conj]

@[simp] theorem conj_smul (r : ℤ) (X : A ⟶ B) : conj hA hB (r • X) = r • conj hA hB X := by
  simp [conj]

theorem conj_id (hA' : A = polyModule m) : conj hA hA' (𝟙 A) = 𝟙 _ := by
  simp [conj]

theorem conj_comp (hB' : polyModule m = B) (hC : C = polyModule m) (X : A ⟶ B) (Y : B ⟶ C) :
    conj hA hC (X ≫ Y) = conj hA hB X ≫ conj hB' hC Y := by
  simp [conj]

theorem conj_eq_zero_iff (X : A ⟶ B) : conj hA hB X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have e : X = eqToHom hA.symm ≫ conj hA hB X ≫ eqToHom hB.symm := by simp [conj]
    rw [e, h]; simp
  · rintro rfl; exact conj_zero hA hB

end Conj

theorem transport_layerOp {k m : ℕ} (e : k = m) (i : ℕ) (g : Gen) :
    eqToHom (congrArg polyModule e.symm) ≫ ModuleCat.ofHom (layerOp k i g) ≫
      eqToHom (congrArg polyModule e) = ModuleCat.ofHom (layerOp m i g) := by
  subst e; simp

theorem ofHom_mul {m : ℕ} (f g : Module.End ℤ (SkewPolynomial m)) :
    ModuleCat.ofHom (f * g) = (ModuleCat.ofHom g ≫ ModuleCat.ofHom f : polyModule m ⟶ _) :=
  rfl

/-- The image of a chain of layers, transported to width `m`, is the product of the layer
operators. -/
theorem conj_mapChain {m : ℕ} (ls : List (Layer sig)) :
    ∀ {a b : Obj sig} (h : Chain a ls b) (ha : a.word.length = m) (hb : b.word.length = m),
      conj (congrArg polyModule ha.symm) (congrArg polyModule hb) (interp.mapChain a ls b h) =
        ModuleCat.ofHom (opList m ls) := by
  induction ls with
  | nil =>
    intro a b h ha hb
    cases h
    simp [conj, Interpretation.mapChain]
    rfl
  | cons L ls ih =>
    intro a b h ha hb
    have hL : L.dom.word.length = m := by rw [h.2.1]; exact ha
    have hL' : L.cod.word.length = m := by rw [layer_cod_length]; exact hL
    have ih' := ih h.2.2 hL' hb
    rw [opList_cons, ofHom_mul, ← ih', ← transport_layerOp hL]
    simp only [conj, Interpretation.mapChain, interp, Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc]

/-- The image of a diagram between objects of width `m`, transported to `polyModule m`. -/
theorem conj_map {m : ℕ} {a b : Obj sig} (f : a ⟶ b) (hA : polyModule m = interp.functor.obj a)
    (hB : interp.functor.obj b = polyModule m) (ha : a.word.length = m)
    (hb : b.word.length = m) :
    conj hA hB (interp.functor.map f) = ModuleCat.ofHom (opList m (Diagram.layers f)) :=
  conj_mapChain _ (Diagram.chain f) ha hb

/-- The image of a linear combination of diagrams between objects of width `m`, transported to
`polyModule m`. -/
theorem conj_freeLift_map {m : ℕ} {a b : Obj sig} (X : LinDiagram ℤ a b)
    (ha : a.word.length = m) (hb : b.word.length = m)
    (hA : polyModule m = (freeLift ℤ interp.functor).obj (Free.of ℤ a))
    (hB : (freeLift ℤ interp.functor).obj (Free.of ℤ b) = polyModule m) :
    conj hA hB ((freeLift ℤ interp.functor).map X) = ModuleCat.ofHom (linOp m X) := by
  induction X using Finsupp.induction_linear with
  | zero =>
    rw [CategoryTheory.Functor.map_zero, conj_zero, linOp_zero]
    rfl
  | add X Y hX hY =>
    rw [CategoryTheory.Functor.map_add, conj_add, hX, hY, linOp_add]
    rfl
  | single d r =>
    rw [freeLift_map_single, conj_smul, linOp_single]
    change r • conj (A := interp.functor.obj a) (B := interp.functor.obj b) hA hB
      (interp.functor.map d) = _
    rw [conj_map d hA hB ha hb]
    rfl

theorem freeLift_map_eq_zero {m : ℕ} {a b : Obj sig} (ha : a.word.length = m)
    (hb : b.word.length = m) (X : LinDiagram ℤ a b) (h : linOp m X = 0) :
    (freeLift ℤ interp.functor).map X = 0 := by
  rw [← conj_eq_zero_iff (congrArg polyModule ha.symm) (congrArg polyModule hb),
    conj_freeLift_map X ha hb, h]
  rfl

/-! ## Soundness -/

theorem respects_rel (r : Rel) (u : Obj sig) (v : List sig.Colour)
    (hw : (strands r.width).WhiskerOK u v) :
    (freeLift ℤ interp.functor).map (LinDiagram.whisker (relation ℤ r) u v hw) = 0 := by
  have hm : ((strands r.width).whisker u v).word.length = u.word.length + r.width + v.length := by
    simp; omega
  apply freeLift_map_eq_zero hm hm
  cases r <;>
    simp [relation, LinDiagram.whisker_add, LinDiagram.whisker_sub, dlay, lay, Layer.whisker,
      Rel.width, linOp, Finsupp.linearCombination_single]
  · exact op_square (by omega)
  · exact op_braid (by omega)
  · exact op_mixedRight (by omega)
  · exact op_mixedLeft (by omega)

theorem respects_interchange (d : InterchangeData sig) (hd : d.Valid) (u : Obj sig)
    (v : List sig.Colour) (hw : d.dom.WhiskerOK u v) :
    (freeLift ℤ interp.functor).map (LinDiagram.whisker (InterchangeData.rel ℤ hd) u v hw) =
      0 := by
  have hrel : InterchangeData.rel ℤ hd =
      LinDiagram.of (InterchangeData.ghDiagram hd) + LinDiagram.of (InterchangeData.hgDiagram hd) := by
    simp [InterchangeData.rel, InterchangeData.sign, sig]
  have hm : (d.dom.whisker u v).word.length =
      u.word.length + d.g.arity + d.mid.length + d.h.arity + v.length := by
    simp [InterchangeData.dom, sig]; omega
  have hm' : (d.cod.whisker u v).word.length =
      u.word.length + d.g.arity + d.mid.length + d.h.arity + v.length := by
    simp [InterchangeData.cod, sig]; omega
  apply freeLift_map_eq_zero hm hm'
  rw [hrel]
  simp [LinDiagram.whisker_add, linOp, Finsupp.linearCombination_single, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
    InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂,
    Layer.whisker]
  exact op_interchange d.g d.h (by omega) (by omega)

/-- The polynomial interpretation respects the defining relations and the super interchange
law. -/
theorem respects : (pres ℤ).Respects interp.functor where
  rel r u v hw := respects_rel r u v hw
  interchange d hd u v hw := respects_interchange d hd u v hw

/-- The polynomial representation of the presented odd nilHecke category. -/
def polyFunctor : ONH ℤ ⥤ ModuleCat.{0} ℤ := (pres ℤ).lift respects

instance : polyFunctor.Additive := Presentation.lift_additive _

theorem polyFunctor_map_diag {a b : Obj sig} (f : a ⟶ b) :
    polyFunctor.map ((pres ℤ).diag f) = interp.functor.map f :=
  Presentation.lift_diag _ _

/-! ## Endomorphisms of `m` strands -/

theorem polyModule_strands (m : ℕ) :
    polyModule m = polyFunctor.obj ((pres ℤ).obj (strands m)) :=
  congrArg polyModule (strands_word_length m).symm

/-- The action of endomorphisms of `m` strands on `SkewPolynomial m`. -/
def realize (m : ℕ) : End ((pres ℤ).obj (strands m)) →+* Module.End ℤ (SkewPolynomial m) where
  toFun f := (conj (polyModule_strands m) (polyModule_strands m).symm (polyFunctor.map f)).hom
  map_one' := by
    rw [End.one_def, CategoryTheory.Functor.map_id, conj_id]
    rfl
  map_mul' f g := by
    rw [End.mul_def, CategoryTheory.Functor.map_comp,
      conj_comp _ (polyModule_strands m).symm (polyModule_strands m)]
    rfl
  map_zero' := by simp only [CategoryTheory.Functor.map_zero, conj_zero]; rfl
  map_add' f g := by
    change (conj (polyModule_strands m) (polyModule_strands m).symm (polyFunctor.map (f + g))).hom =
      (conj (polyModule_strands m) (polyModule_strands m).symm (polyFunctor.map f)).hom +
        (conj (polyModule_strands m) (polyModule_strands m).symm (polyFunctor.map g)).hom
    rw [CategoryTheory.Functor.map_add, conj_add]
    rfl

theorem realize_diag (m : ℕ) (f : strands m ⟶ strands m) :
    realize m ((pres ℤ).diag f) = opList m (Diagram.layers f) := by
  change (conj (polyModule_strands m) (polyModule_strands m).symm
    (polyFunctor.map ((pres ℤ).diag f))).hom = _
  rw [polyFunctor_map_diag]
  exact congrArg ModuleCat.Hom.hom
    (conj_map f (polyModule_strands m) (polyModule_strands m).symm (strands_word_length m)
      (strands_word_length m))

theorem realize_x (n : ℕ) (j : Fin (n + 2)) :
    realize (n + 2) (x ℤ (n + 2) j) = dotOperator n j := by
  rw [x_def ℤ j.isLt, realize_diag, layers_dlay]
  simp [lay, layerOp_dot n j j.isLt]

theorem realize_ψ (n : ℕ) (i : Fin (n + 1)) :
    realize (n + 2) (ψ ℤ (n + 2) i) = AllRankDivided.divided i := by
  rw [ψ_def ℤ (by omega), realize_diag, layers_dlay]
  simp [lay, layerOp_cross n i i.isLt]

end OddMath.Diagrams.OddNilHecke

end
