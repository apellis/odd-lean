import OddMath.Diagrams.OddNilHecke.Basic

/-!
# The odd nilHecke relations at symbolic width

For every width `n` and every admissible position, the dots `x n i` and crossings `ψ n i`
of the presented odd nilHecke category satisfy the seven relation families of EKL,
arXiv:1111.1320v1, Proposition 2.1, (2.7)–(2.10) (indices shifted to start at `0`,
products are composition of operators, as in `OddMath.Frontier.NilHeckeAction.Relator`):

* `ψ_mul_ψ` (`square`): `ψ_i ψ_i = 0`;
* `ψ_braid` (`braid`): `ψ_i ψ_{i+1} ψ_i = ψ_{i+1} ψ_i ψ_{i+1}`;
* `x_mul_x_add_x_mul_x` (`dots`): `x_i x_j + x_j x_i = 0` for `i ≠ j`;
* `ψ_mul_ψ_add_ψ_mul_ψ` (`distant`): `ψ_i ψ_j + ψ_j ψ_i = 0` for `|i - j| > 1`;
* `x_mul_ψ_add_ψ_mul_x` (`mixedRight`): `x_i ψ_i + ψ_i x_{i+1} = 1`;
* `ψ_mul_x_add_x_mul_ψ` (`mixedLeft`): `ψ_i x_i + x_{i+1} ψ_i = 1`;
* `x_mul_ψ_add_ψ_mul_x_of_ne` (`spectator`): `x_j ψ_i + ψ_i x_j = 0` for `j ∉ {i, i+1}`.

The first two and the two mixed relations are whiskered defining relations. The three
anticommutation families are **not** defining relations: each is the super interchange law
for two odd generators (`interchange_at`), whose Koszul sign is `-1`.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams

variable (R : Type*) [CommRing R]

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

theorem whisker_strands {w i n : ℕ} (h : i + w ≤ n) :
    (strands w).whisker (shift i) (List.replicate (n - i - w) ()) = strands n :=
  obj_ext (by simp [strands, shift, Obj.whisker]; omega)

/-- A defining relation, transported to position `i` in width `n`. -/
theorem relation_at (r : Rel) {n i : ℕ} (h : i + r.width ≤ n) :
    (pres R).lin (LinDiagram.cast (LinDiagram.whisker (relation R r) (shift i)
      (List.replicate (n - i - r.width) ()) (Obj.whiskerOK_of_subsingleton _ _ _))
      (whisker_strands h) (whisker_strands h)) = 0 :=
  (pres R).lin_rel_cast r (shift i) _ _ _ _

/-- The super interchange law for the odd generators `g` (at position `i`) and `h` (at
position `j`, to the right of `g`) in width `n`: the Koszul sign is `-1`. -/
theorem interchange_at (g h : Gen) {n i j : ℕ} (hij : i + g.arity ≤ j) (hn : j + h.arity ≤ n) :
    (pres R).diag (dlay (n := n) (i := i) (g := g) (by omega)) ≫
        (pres R).diag (dlay (n := n) (i := j) (g := h) hn) =
      -((pres R).diag (dlay (n := n) (i := j) (g := h) hn) ≫
        (pres R).diag (dlay (n := n) (i := i) (g := g) (by omega))) := by
  let d : InterchangeData sig := ⟨(), g, List.replicate (j - i - g.arity) (), h⟩
  have hx : d.Valid := InterchangeData.valid_of_subsingleton d
  have hd : d.dom.whisker (shift i) (List.replicate (n - j - h.arity) ()) = strands n :=
    obj_ext (by simp [d, InterchangeData.dom, shift, strands, sig]; omega)
  have hc : d.cod.whisker (shift i) (List.replicate (n - j - h.arity) ()) = strands n :=
    obj_ext (by simp [d, InterchangeData.cod, shift, strands, sig]; omega)
  have key := (pres R).diag_interchange d hx (shift i) _
    (Obj.whiskerOK_of_subsingleton _ _ _) hd hc
  have hs : ((d.sign : ℤ) : R) = -1 := by simp [d, InterchangeData.sign, sig]
  rw [hs, neg_one_smul] at key
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  refine Eq.trans ?_ (key.trans ?_)
  · apply Presentation.diag_eq_of_layers_eq
    simp [d, dlay, lay, shift, Layer.whisker, InterchangeData.ghDiagram,
      InterchangeData.gh₁, InterchangeData.gh₂, sig]
    omega
  · congr 1
    apply Presentation.diag_eq_of_layers_eq
    simp [d, dlay, lay, shift, Layer.whisker, InterchangeData.hgDiagram,
      InterchangeData.hg₁, InterchangeData.hg₂, sig]
    omega

/-- The interchange law in the additive form `g h + h g = 0` of EKL (2.8)–(2.10). -/
theorem interchange_add (g h : Gen) {n i j : ℕ} (hij : i + g.arity ≤ j)
    (hn : j + h.arity ≤ n) :
    (pres R).diag (dlay (n := n) (i := i) (g := g) (by omega)) ≫
        (pres R).diag (dlay (n := n) (i := j) (g := h) hn) +
      (pres R).diag (dlay (n := n) (i := j) (g := h) hn) ≫
        (pres R).diag (dlay (n := n) (i := i) (g := g) (by omega)) = 0 := by
  rw [interchange_at R g h hij hn, neg_add_cancel]

/-! ## Defining relations -/

theorem ψ_mul_ψ (n i : ℕ) : ψ R n i * ψ R n i = 0 := by
  by_cases h : i + 1 < n
  · have key := relation_at R .square (n := n) (i := i) (by simp [Rel.width]; omega)
    rw [show relation R .square = LinDiagram.of _ from rfl, LinDiagram.whisker_of,
      LinDiagram.cast_of, Presentation.lin_of] at key
    rw [ψ_def R h, End.mul_def, ← Presentation.diag_comp, ← key]
    apply Presentation.diag_eq_of_layers_eq
    simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
  · rw [ψ_of_le R (by omega), mul_zero]

theorem ψ_braid (n i : ℕ) :
    ψ R n i * ψ R n (i + 1) * ψ R n i = ψ R n (i + 1) * ψ R n i * ψ R n (i + 1) := by
  by_cases h : i + 2 < n
  · have key := relation_at R .braid (n := n) (i := i) (by simp [Rel.width]; omega)
    rw [show relation R .braid = LinDiagram.of _ - LinDiagram.of _ from rfl,
      LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of, LinDiagram.cast_sub,
      LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of,
      Presentation.lin_of, sub_eq_zero] at key
    rw [ψ_def R (show i + 1 < n by omega), ψ_def R h]
    simp only [End.mul_def, ← Presentation.diag_comp]
    convert key using 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width] <;> omega
  · by_cases h' : i + 1 < n
    · rw [ψ_of_le R (n := n) (i := i + 1) (by omega)]; simp
    · rw [ψ_of_le R (n := n) (i := i) (by omega)]; simp

theorem x_mul_ψ_add_ψ_mul_x {n i : ℕ} (h : i + 1 < n) :
    x R n i * ψ R n i + ψ R n i * x R n (i + 1) = 1 := by
  have key := relation_at R .mixedRight (n := n) (i := i) (by simp [Rel.width]; omega)
  rw [show relation R .mixedRight = LinDiagram.of _ + LinDiagram.of _ - LinDiagram.of _ from rfl,
    LinDiagram.whisker_sub, LinDiagram.whisker_add, LinDiagram.whisker_of, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.cast_sub, LinDiagram.cast_add, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_add,
    Presentation.lin_of, Presentation.lin_of, Presentation.lin_of, sub_eq_zero] at key
  rw [x_def R (show i < n by omega), x_def R h, ψ_def R h]
  simp only [End.mul_def, ← Presentation.diag_comp, End.one_def]
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
    all_goals omega
  · refine Eq.trans ?_ ((pres R).diag_id _)
    apply Presentation.diag_eq_of_layers_eq
    simp

theorem ψ_mul_x_add_x_mul_ψ {n i : ℕ} (h : i + 1 < n) :
    ψ R n i * x R n i + x R n (i + 1) * ψ R n i = 1 := by
  have key := relation_at R .mixedLeft (n := n) (i := i) (by simp [Rel.width]; omega)
  rw [show relation R .mixedLeft = LinDiagram.of _ + LinDiagram.of _ - LinDiagram.of _ from rfl,
    LinDiagram.whisker_sub, LinDiagram.whisker_add, LinDiagram.whisker_of, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.cast_sub, LinDiagram.cast_add, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_add,
    Presentation.lin_of, Presentation.lin_of, Presentation.lin_of, sub_eq_zero] at key
  rw [x_def R (show i < n by omega), x_def R h, ψ_def R h]
  simp only [End.mul_def, ← Presentation.diag_comp, End.one_def]
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
    all_goals omega
  · refine Eq.trans ?_ ((pres R).diag_id _)
    apply Presentation.diag_eq_of_layers_eq
    simp

/-! ## Anticommutation, from the super interchange law -/

theorem x_mul_x_add_x_mul_x {n i j : ℕ} (hij : i ≠ j) :
    x R n i * x R n j + x R n j * x R n i = 0 := by
  wlog h : i < j generalizing i j
  · rw [add_comm]; exact this hij.symm (by omega)
  by_cases hj : j < n
  · rw [x_def R (show i < n by omega), x_def R hj, End.mul_def, End.mul_def, add_comm]
    exact interchange_add R .dot .dot (n := n) h hj
  · rw [x_of_le R (show n ≤ j by omega)]; simp

theorem ψ_mul_ψ_add_ψ_mul_ψ {n i j : ℕ} (hij : i + 1 < j ∨ j + 1 < i) :
    ψ R n i * ψ R n j + ψ R n j * ψ R n i = 0 := by
  wlog h : i + 1 < j generalizing i j
  · rw [add_comm]; exact this (by omega) (by omega)
  by_cases hj : j + 1 < n
  · rw [ψ_def R (show i + 1 < n by omega), ψ_def R hj, End.mul_def, End.mul_def, add_comm]
    exact interchange_add R .cross .cross (n := n) (show i + 2 ≤ j by omega) hj
  · rw [ψ_of_le R (show n ≤ j + 1 by omega)]; simp

theorem x_mul_ψ_add_ψ_mul_x_of_ne {n i j : ℕ} (hl : j ≠ i) (hr : j ≠ i + 1) :
    x R n j * ψ R n i + ψ R n i * x R n j = 0 := by
  rcases Nat.lt_or_ge j i with hji | hji
  · by_cases hi : i + 1 < n
    · rw [x_def R (show j < n by omega), ψ_def R hi, End.mul_def, End.mul_def, add_comm]
      exact interchange_add R .dot .cross (n := n) hji hi
    · rw [ψ_of_le R (show n ≤ i + 1 by omega)]; simp
  · by_cases hj : j < n
    · rw [x_def R hj, ψ_def R (show i + 1 < n by omega), End.mul_def, End.mul_def]
      exact interchange_add R .cross .dot (n := n) (show i + 2 ≤ j by omega) hj
    · rw [x_of_le R (show n ≤ j by omega)]; simp

end OddMath.Diagrams.OddNilHecke

end
