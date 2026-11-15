import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import Mathlib.Algebra.Polynomial.Module.AEval
import OddMath.QuiverHecke.CyclotomicAction.AppendMackey
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.FiniteHomMatrixRightModule
import Mathlib.LinearAlgebra.Quotient.Bilinear
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwiner
import Mathlib.Algebra.Polynomial.Monic
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Endpoint polynomials

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Descent of the full ELV old-generator map

Precomposition by the prescribed crossing word followed by the full ELV relation
maps the prepend-old relation span into the append-old relation span. This gives
P between the two old-only quotients. No injectivity, exactness, or polynomial
module linearity is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed morphism carries an inserted old ideal element into the append span. -/
theorem appendW_insert_ideal (i : I) {v t : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t) :
    appendW D Sc cutoff i v ≫ insert D Sc cutoff i v t r ∈
      appendRelations D Sc cutoff i v (i :: t) := by
  have he := appendError_mem_appendRelations D Sc cutoff i
    (twist k (appendQ D cutoff i v) r)
  rw [appendError_apply, twist_twist] at he
  have hi := appendRelations_mem D Sc cutoff i
    (twist_ideal D Sc cutoff (appendQ D cutoff i v) hr) (appendW D Sc cutoff i t)
  have h := Submodule.sub_mem (appendRelations D Sc cutoff i v (i :: t)) hi he
  simpa only [sub_sub_cancel] using h

/-- All old composites and ambient continuations are respected by the prescribed map. -/
theorem appendW_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    appendW D Sc cutoff i v ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    rw [← Category.assoc]
    exact appendRelations_comp D Sc cutoff i (appendW_insert_ideal D Sc cutoff i hr) a
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- P on old-only quotient coordinates, with the prescribed W and no balance hypothesis. -/
def pMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (appendW D Sc cutoff i v))
    (fun _ hh => appendW_relations D Sc cutoff i hh)

/-- The descended map is precomposition by W, not an unspecified quotient lift. -/
@[simp] theorem pMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    pMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w
        ((affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
          relation D Sc cutoff i v) ≫ h) := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Central moving-variable linearity of ELV P

`DeformedSquareResolution.md` §§1,3: the prescribed P intertwines the moving
dot for even colour and moving square for odd colour. Decorated deletion
slides are combined with even-power commutation with the full ELV relation.
Both actions preserve their old relation spaces, including zero cutoffs.
No unchanged odd-dot intertwining or centrality of the odd relation is used.

The polynomial map is over the ground polynomial ring k[s], with commuting
twisted old operators annihilating the old ideal. Assembly into a content-level
right B[s]-module, and projectivity, are separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_comp_movingPower (i : I) (v : List I) (d e : ℕ) :
    movingPower D Sc cutoff i v d ≫ movingPower D Sc cutoff i v e =
      movingPower D Sc cutoff i v (d + e) := by
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d) ≫
    affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ e) = _
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ e * dotE D Sc (i :: v) 0 ^ d) = _
  rw [← pow_add, Nat.add_comm]
  rfl

theorem movingPower_deformedCyclotomic (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    movingPower D Sc cutoff i v d ≫
        (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) =
      (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) ≫
        movingPower D Sc cutoff i v d := by
  rw [deformedCyclotomic_expansion, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Category.assoc, ← movingPower_insert D Sc cutoff i d hd, ← Category.assoc,
    ← Category.assoc, movingPower_comp_movingPower, movingPower_comp_movingPower,
    Nat.add_comm d j.val]

theorem movingPower_relation (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) :
    movingPower D Sc cutoff i v d ≫ relation D Sc cutoff i v =
      relation D Sc cutoff i v ≫ movingPower D Sc cutoff i v d := by
  unfold relation
  split_ifs <;> apply movingPower_deformedCyclotomic D Sc cutoff i v d hd

theorem appendDecoratedW_even (i : I) (v : List I) (d : ℕ)
    (hd : d • D.parity i = 0) :
    appendDecoratedW D Sc cutoff i v d =
      appendW D Sc cutoff i v ≫ movingPower D Sc cutoff i v d := by
  rw [appendDecoratedW, movingPower_relation D Sc cutoff i v d hd, ← Category.assoc]
  rfl

def appendMovingPower (i : I) (v : List I) (d : ℕ) :
    hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ d)

theorem appendMovingPower_relations (i : I) {v w : List I} (d : ℕ)
    {h : hom D Sc cutoff (v ++ [i]) w} (hh : h ∈ appendRelations D Sc cutoff i v w) :
    appendMovingPower D Sc cutoff i v d ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction d with
  | zero => simpa [appendMovingPower, affineUnit_id, End.one_def] using hh
  | succ d ih =>
    have he : appendMovingPower D Sc cutoff i v (d + 1) =
        affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length) ≫
          appendMovingPower D Sc cutoff i v d := by
      simp only [appendMovingPower, pow_succ, End.mul_def, affineUnit_comp]
    rw [he, Category.assoc]
    exact lastDot_comp_mem_appendRelations D Sc cutoff i ih

def appendMovingPowerTarget (i : I) (v w : List I) (d : ℕ) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (appendMovingPower D Sc cutoff i v d))
    (fun _ hh => appendMovingPower_relations D Sc cutoff i d hh)

@[simp] theorem appendMovingPowerTarget_projection (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    appendMovingPowerTarget D Sc cutoff i v w d (appendProjection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v d ≫ h) := rfl

theorem pMap_movingSquare (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w
        (movingPowerTarget D Sc cutoff i v w 2
          ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i)) z) =
      appendMovingPowerTarget D Sc cutoff i v w 2 (pMap D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫
      (movingPower D Sc cutoff i v 2 ≫ h)) =
    appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v 2 ≫
      (appendW D Sc cutoff i v ≫ h))
  have he := lastDotSquare_comp_appendDecoratedW_mem D Sc cutoff i v 0
  rw [appendDecoratedW_zero, zero_add, appendDecoratedW_even D Sc cutoff i v 2
    ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i))] at he
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v w _).mpr
    (appendRelations_comp D Sc cutoff i he h)
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  simpa only [Category.assoc, appendMovingPower] using hz.symm

theorem pMap_movingEvenDot (i : I) (hi : D.parity i = 0) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w (movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]) z) =
      appendMovingPowerTarget D Sc cutoff i v w 1 (pMap D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫
      (movingPower D Sc cutoff i v 1 ≫ h)) =
    appendProjection D Sc cutoff i v w (appendMovingPower D Sc cutoff i v 1 ≫
      (appendW D Sc cutoff i v ≫ h))
  have he := lastDot_comp_appendDecoratedW_mem D Sc cutoff i v 0
  rw [appendDecoratedW_zero, zero_add, appendDecoratedW_even D Sc cutoff i v 1 (by simp [hi])] at he
  simp only [hi, zero_mul, SKM.zsign, zero_ne_one, ite_false, one_smul] at he
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v w _).mpr
    (appendRelations_comp D Sc cutoff i he h)
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  simpa only [Category.assoc, appendMovingPower, pow_one] using hz.symm

def appendOldSourceTarget (i : I) (v w : List I) (c : hom D Sc cutoff v v) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (rightContext D Sc cutoff [i] v v c))
    (fun _ hh => comp_appendRelations D Sc cutoff i c hh)

/-- The prescribed central exponent is one at even colour, two at odd colour. -/
def centralDegree (i : I) : ℕ := if D.parity i = 0 then 1 else 2

theorem centralDegree_even (i : I) : centralDegree D i • D.parity i = 0 := by
  unfold centralDegree
  split_ifs with hi
  · simp [hi]
  · exact (by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i)

abbrev centralSource (i : I) (v w : List I) :=
  movingPowerTarget D Sc cutoff i v w (centralDegree D i) (centralDegree_even D i)

abbrev centralAppend (i : I) (v w : List I) :=
  appendMovingPowerTarget D Sc cutoff i v w (centralDegree D i)

theorem pMap_central (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w (centralSource D Sc cutoff i v w z) =
      centralAppend D Sc cutoff i v w (pMap D Sc cutoff i v w z) := by
  unfold centralSource centralAppend centralDegree
  split_ifs with hi
  · exact pMap_movingEvenDot D Sc cutoff i hi v w z
  · exact pMap_movingSquare D Sc cutoff i v w z

theorem appendMovingPower_whisker (i : I) (v : List I) (d : ℕ) :
    appendMovingPower D Sc cutoff i v d =
      affineUnit D Sc cutoff (v ++ [i]) (v ++ [i]) ((pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ d)) := by
  have he : (pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ d) =
      dotE D Sc (v ++ [i]) v.length ^ d := by
    induction d with
    | zero => exact MonoidalSupercategory.whiskerLeft_id (R := k) _ _
    | succ d ih =>
      simp only [pow_succ, End.mul_def]
      rw [MonoidalSupercategory.whiskerLeft_comp (R := k), ih, whiskerLeft_dotE D Sc v i rfl]
  rw [he]
  rfl

/-- The old-only source with the prescribed central polynomial action. -/
abbrev CentralTarget (i : I) (v w : List I) :=
  Module.AEval' (centralSource D Sc cutoff i v w)

/-- The append-old target with the prescribed central polynomial action. -/
abbrev CentralAppendTarget (i : I) (v w : List I) :=
  Module.AEval' (centralAppend D Sc cutoff i v w)

/-- P is polynomial-linear for the dot at even colour and square at odd colour.
The intertwining proof is `pMap_central`, not an input assumption. -/
def pCentralMap (i : I) (v w : List I) :
    CentralTarget D Sc cutoff i v w →ₗ[Polynomial k] CentralAppendTarget D Sc cutoff i v w :=
  LinearMap.ofAEval (centralSource D Sc cutoff i v w)
    ((Module.AEval'.of (centralAppend D Sc cutoff i v w)).toLinearMap.comp
      (pMap D Sc cutoff i v w)) (fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [Module.AEval'.X_smul_of]
        exact congrArg (Module.AEval'.of (centralAppend D Sc cutoff i v w))
          (pMap_central D Sc cutoff i v w z))

@[simp] theorem pCentralMap_of (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pCentralMap D Sc cutoff i v w (Module.AEval'.of (centralSource D Sc cutoff i v w) z) =
      Module.AEval'.of (centralAppend D Sc cutoff i v w) (pMap D Sc cutoff i v w z) := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordinary old ELV quotient category

The old cyclotomic Hom quotients form a linear category. Its finite content
Hom matrices give the ordinary coefficient ring in the square resolution.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Words in the old cyclotomic ELV category. -/
structure OldCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (cutoff : I → ℕ) where
  word : List I

/-- Quotient composition, in categorical order. -/
def oldComp (v t w : List I) :
    Old D Sc cutoff v t →ₗ[k]
      Old D Sc cutoff t w →ₗ[k] Old D Sc cutoff v w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (ideal D Sc cutoff v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
       hom D Sc cutoff v t →ₗ[k] hom D Sc cutoff t w →ₗ[k] Old D Sc cutoff v w)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (ideal_comp D Sc cutoff hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_ideal D Sc cutoff f hg))

@[simp] theorem oldComp_mk (v t w : List I)
    (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t w) :
    oldComp D Sc cutoff v t w
      ((ideal D Sc cutoff v t).mkQ f)
      ((ideal D Sc cutoff t w).mkQ g) =
      (ideal D Sc cutoff v w).mkQ (f ≫ g) := rfl

instance oldCategory : Category (OldCategory D Sc cutoff) where
  Hom v w := Old D Sc cutoff v.word w.word
  id v := (ideal D Sc cutoff v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := oldComp D Sc cutoff v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    exact congrArg (ideal D Sc cutoff v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    exact congrArg (ideal D Sc cutoff v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    obtain ⟨h, rfl⟩ := (ideal D Sc cutoff w.word z.word).mkQ_surjective h
    exact congrArg (ideal D Sc cutoff v.word z.word).mkQ (Category.assoc f g h)

instance oldPreadditive : Preadditive (OldCategory D Sc cutoff) where
  homGroup v w := inferInstanceAs (AddCommGroup (Old D Sc cutoff v.word w.word))
  add_comp := by
    intro v t w f g h
    exact LinearMap.map_add₂ (oldComp D Sc cutoff v.word t.word w.word) f g h
  comp_add := by
    intro v t w f g h
    exact (oldComp D Sc cutoff v.word t.word w.word f).map_add g h

instance oldLinear : Linear k (OldCategory D Sc cutoff) where
  homModule v w := inferInstanceAs (Module k (Old D Sc cutoff v.word w.word))
  smul_comp := by
    intro v t w r f g
    exact LinearMap.map_smul₂ (oldComp D Sc cutoff v.word t.word w.word) r f g
  comp_smul := by
    intro v t w f r g
    exact (oldComp D Sc cutoff v.word t.word w.word f).map_smul r g

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordinary endpoint actions of the old ELV category

The two old-only quotients are additive presheaves on the old cyclotomic
category. The prepend action retains an arbitrary total-parity twist, while
the append action is unchanged. All old word-to-word arrows act, not only
endomorphisms of a fixed word.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem insert_comp_relations (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) {h : hom D Sc cutoff (i :: v) w}
    (hh : h ∈ relations D Sc cutoff i v w) :
    insert D Sc cutoff i u v c ≫ h ∈ relations D Sc cutoff i u w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, ← insert_comp]
    exact Submodule.subset_span ⟨t, c ≫ r, comp_ideal D Sc cutoff c hr, f, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hb

/-- Twisted old precomposition, descended in both arguments. -/
def sourcePull (p : ZMod 2) (i : I) (u v w : List I) :
    Old D Sc cutoff u v →ₗ[k]
      Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i u w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun c =>
        (projection D Sc cutoff i u w).comp
          (Linear.leftComp k _ (insert D Sc cutoff i u v (twist k p c)))
       map_add' := by intros; ext h; simp [map_add, Preadditive.add_comp]
       map_smul' := by intros; ext h; simp [map_smul, Linear.smul_comp] } :
       hom D Sc cutoff u v →ₗ[k]
         hom D Sc cutoff (i :: v) w →ₗ[k] Target D Sc cutoff i u w)
    (by
      intro c hc
      ext h
      exact projection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff p hc) h)
    (by
      intro h hh
      ext c
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (insert_comp_relations D Sc cutoff i (twist k p c) hh))

@[simp] theorem sourcePull_mk (p : ZMod 2) (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) (h : hom D Sc cutoff (i :: v) w) :
    sourcePull D Sc cutoff p i u v w ((ideal D Sc cutoff u v).mkQ c)
      (projection D Sc cutoff i v w h) =
    projection D Sc cutoff i u w (insert D Sc cutoff i u v (twist k p c) ≫ h) := rfl

theorem sourcePull_comp (p : ZMod 2) (i : I) {a b c w : List I}
    (f : Old D Sc cutoff a b) (g : Old D Sc cutoff b c)
    (z : Target D Sc cutoff i c w) :
    sourcePull D Sc cutoff p i a c w (oldComp D Sc cutoff a b c f g) z =
      sourcePull D Sc cutoff p i a b w f (sourcePull D Sc cutoff p i b c w g z) := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff a b).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff b c).mkQ_surjective g
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i c w z
  change projection D Sc cutoff i a w (insert D Sc cutoff i a c (twist k p (f ≫ g)) ≫ h) =
    projection D Sc cutoff i a w (insert D Sc cutoff i a b (twist k p f) ≫ (insert D Sc cutoff i b c (twist k p g) ≫ h))
  rw [twist_comp, insert_comp, Category.assoc]

/-- The source quotient with its twisted ordinary old action. -/
def sourcePresheaf (p : ZMod 2) (i : I) (w : List I) :
    (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Target D Sc cutoff i v.unop.word w)
  map f := ModuleCat.ofHom (sourcePull D Sc cutoff p i _ _ w f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v.unop.word w z
    change projection D Sc cutoff i _ w (insert D Sc cutoff i _ _ (twist k p (𝟙 _)) ≫ h) = _
    simp
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact sourcePull_comp D Sc cutoff p i g.unop f.unop z

instance sourcePresheaf_additive (p : ZMod 2) (i : I) (w : List I) :
    (sourcePresheaf D Sc cutoff p i w).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (sourcePull D Sc cutoff p i _ _ w).map_add f.unop g.unop

/-- Untwisted append precomposition, descended in both arguments. -/
def appendPull (i : I) (u v w : List I) :
    Old D Sc cutoff u v →ₗ[k]
      AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i u w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun c =>
        (appendProjection D Sc cutoff i u w).comp
          (Linear.leftComp k _ (rightContext D Sc cutoff [i] u v c))
       map_add' := by intros; ext h; simp [map_add, Preadditive.add_comp]
       map_smul' := by intros; ext h; simp [map_smul, Linear.smul_comp] } :
       hom D Sc cutoff u v →ₗ[k]
         hom D Sc cutoff (v ++ [i]) w →ₗ[k] AppendTarget D Sc cutoff i u w)
    (by
      intro c hc
      ext h
      exact appendProjection_old_ideal D Sc cutoff i hc h)
    (by
      intro h hh
      ext c
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_appendRelations D Sc cutoff i c hh))

@[simp] theorem appendPull_mk (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) (h : hom D Sc cutoff (v ++ [i]) w) :
    appendPull D Sc cutoff i u v w ((ideal D Sc cutoff u v).mkQ c)
      (appendProjection D Sc cutoff i v w h) =
    appendProjection D Sc cutoff i u w (rightContext D Sc cutoff [i] u v c ≫ h) := rfl

private theorem appendContext_id (i : I) (v : List I) :
    rightContext D Sc cutoff [i] v v (𝟙 _) = 𝟙 _ := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    (𝟙 ((pres D Sc).obj (ob D v)) ▷ (pres D Sc).obj (ob D [i])) = _
  exact congrArg (fun f => (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (MonoidalSupercategory.id_whiskerRight (R := k)
      ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D [i])))

theorem appendPull_comp (i : I) {a b c w : List I}
    (f : Old D Sc cutoff a b) (g : Old D Sc cutoff b c)
    (z : AppendTarget D Sc cutoff i c w) :
    appendPull D Sc cutoff i a c w (oldComp D Sc cutoff a b c f g) z =
      appendPull D Sc cutoff i a b w f (appendPull D Sc cutoff i b c w g z) := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff a b).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff b c).mkQ_surjective g
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i c w z
  change appendProjection D Sc cutoff i a w (rightContext D Sc cutoff [i] a c (f ≫ g) ≫ h) =
    appendProjection D Sc cutoff i a w (rightContext D Sc cutoff [i] a b f ≫ (rightContext D Sc cutoff [i] b c g ≫ h))
  rw [rightContext_comp, Category.assoc]

/-- The append quotient with its unchanged ordinary old action. -/
def appendPresheaf (i : I) (w : List I) :
    (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (AppendTarget D Sc cutoff i v.unop.word w)
  map f := ModuleCat.ofHom (appendPull D Sc cutoff i _ _ w f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v.unop.word w z
    change appendProjection D Sc cutoff i _ w (rightContext D Sc cutoff [i] _ _ (𝟙 _) ≫ h) = _
    rw [appendContext_id, Category.id_comp]
    rfl
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact appendPull_comp D Sc cutoff i g.unop f.unop z

instance appendPresheaf_additive (i : I) (w : List I) :
    (appendPresheaf D Sc cutoff i w).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (appendPull D Sc cutoff i _ _ w).map_add f.unop g.unop

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Moving-chain descent and the signed QP operation

Q is precomposition by the moving chain on the append-old quotient. Its
relation preservation uses the full coefficient parity twist. The composite
with P is the existing signed QP polynomial, including repeated-even factors
−1. These are ground-ring linear maps, not polynomial-module equivalences.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Different word parities have zero full-coefficient Hom space. -/
theorem hom_zero_of_wordParity_ne {v t : List I}
    (hp : wordSumParity D t ≠ wordSumParity D v) (r : hom D Sc cutoff v t) : r = 0 := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [hr, hs, add_zero]
  | tmul a f =>
    have hf : f = 0 := by
      have hle : Submodule.span k {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t) |
          ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < v.length) ∧
            ∃ w : Equiv.Perm (Fin v.length),
              ∃ h, cl D Sc v t (l.map PG.dot ++ cw (Categorification.TypeA.canWord v.length w)) h = f} ≤
          (⊥ : Submodule k _) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨l, -, -, w, h, rfl⟩
        have ht := sChain_target (sChain_pl v
          (l.map PG.dot ++ cw (Categorification.TypeA.canWord v.length w))) h
        exact (hp (by rw [← ht, wordSumParity_tgt])).elim
      rw [span_normalForms D Sc v t] at hle
      exact hle Submodule.mem_top
    simp only [hf, TensorProduct.tmul_zero]

/-- Moving-chain naturality without a word-parity side condition. -/
theorem move_comp_rightContext (i : I) {v t : List I} (r : hom D Sc cutoff v t) :
    move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v t r =
      insert D Sc cutoff i v t (twist k (D.parity i * wordSumParity D v) r) ≫
        move D Sc cutoff i t := by
  by_cases hp : wordSumParity D t = wordSumParity D v
  · simpa only [twist_twist] using
      (insert_comp_move D Sc cutoff i hp (twist k (D.parity i * wordSumParity D v) r)).symm
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hp r]
    simp only [map_zero, Limits.comp_zero, Limits.zero_comp]

/-- Q carries every append-old relation to a prepend-old relation. -/
theorem move_appendRelations (i : I) {v w : List I}
    {h : hom D Sc cutoff (v ++ [i]) w} (hh : h ∈ appendRelations D Sc cutoff i v w) :
    move D Sc cutoff i v ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    rw [← Category.assoc, move_comp_rightContext, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- Q on the old-only quotients, with no assumed descent or balance. -/
def qMap (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (move D Sc cutoff i v))
    (fun _ hh => move_appendRelations D Sc cutoff i hh)

@[simp] theorem qMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    qMap D Sc cutoff i v w (appendProjection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w
        (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v) ≫ h) := rfl

/-- The literal quotient composite is the signed QP polynomial operation. -/
theorem qMap_pMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    qMap D Sc cutoff i v w (pMap D Sc cutoff i v w (projection D Sc cutoff i v w h)) =
      projection D Sc cutoff i v w
        ((affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h) := by
  have he := congrArg (act D Sc cutoff i h) (qp_projection_product D Sc cutoff i v)
  rw [affineUnit_comp D Sc cutoff (v := i :: v) (w := v ++ [i]) (z := i :: v)
    (moveHom D Sc i [] v) (lastToFirstHom D Sc i v)] at he
  simpa only [act_projection, pMap_projection, qMap_projection, Category.assoc] using he

/-- The signed polynomial followed by the full relation preserves the old span. -/
theorem qpProduct_relation_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h ∈
      relations D Sc cutoff i v w := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change projection D Sc cutoff i v w _ = 0
  rw [← qMap_pMap_projection]
  have hz : projection D Sc cutoff i v w h = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hh
  rw [hz, map_zero, map_zero]

/-- The existing signed polynomial and full relation, descended to old-only coordinates. -/
def signedQPMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v))
    (fun _ hh => qpProduct_relation_relations D Sc cutoff i hh)

@[simp] theorem signedQPMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    signedQPMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w
        ((affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h) := rfl

/-- Equality of maps on the actual quotients, not just an affine identity. -/
theorem qMap_comp_pMap (i : I) (v w : List I) :
    (qMap D Sc cutoff i v w).comp (pMap D Sc cutoff i v w) =
      signedQPMap D Sc cutoff i v w := by
  apply LinearMap.ext
  intro x
  obtain ⟨h, rfl⟩ := (relations D Sc cutoff i v w).mkQ_surjective x
  exact qMap_pMap_projection D Sc cutoff i v w h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Regularity of the signed QP product

The actual factors have invertible highest moving coefficients. Finite moving
support in the old-only quotient proves cancellation factor by factor, retaining
the total old-coefficient parity involution and the repeated-even minus signs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldSource_movingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (oldSourceTarget D Sc cutoff i v w c
        (signedMovingPowerTarget D Sc cutoff i v w d
          (prependOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift,
    oldSourceTarget_pair]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem affineUnit_dotPower (v : List I) (b d : ℕ) :
    affineUnit D Sc cutoff v v (dotE D Sc v b ^ d) =
      sourceDotPower D Sc cutoff v b d := rfl

theorem projection_moving_dotPower (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d) ≫ h) =
      signedMovingPowerTarget D Sc cutoff i v w d (projection D Sc cutoff i v w h) := rfl

theorem projection_old_dotPower (i : I) (v w : List I) (b d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1) ^ d) ≫ h) =
      oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b d)
        (projection D Sc cutoff i v w h) := by
  rw [oldSourceTarget_projection, insert_sourceDotPower, affineUnit_dotPower]

/-- The linear moving difference is regular even when its moving dot is odd. -/
theorem projection_dotDifference_regular (i : I) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (i :: v) (b + 1) - dotE D Sc (i :: v) 0) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  let z := projection D Sc cutoff i v w h
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hb : ∀ t ∈ f.support, t.1.1 < (q.representative.shift 1).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change t.1.1 < 1 + q.representative.1.1
    omega
  rw [map_sub, Preadditive.sub_comp, map_sub] at hh
  have hp : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1)) ≫ h) =
      oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1) z := by
    simpa only [pow_one] using projection_old_dotPower D Sc cutoff i v w b 1 h
  have hm : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0) ≫ h) =
      signedMovingPowerTarget D Sc cutoff i v w 1 z := by
    simpa only [pow_one] using projection_moving_dotPower D Sc cutoff i v w 1 h
  rw [hp, hm] at hh
  change oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1) z -
    signedMovingPowerTarget D Sc cutoff i v w 1 z = 0 at hh
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift 1)) hh
  rw [map_sub, map_zero, signedMovingPower_coordinate] at he
  have ho := oldSourceTarget_above D Sc cutoff 0 (q.representative.shift 1)
    (sourceDotPower D Sc cutoff v b 1) f hb
  rw [prependOldReconstruct_coordinateEquiv] at ho
  rw [ho, zero_sub, neg_eq_zero] at he
  have hh' := congrArg (oldTwist D Sc cutoff (1 • D.parity i) v q.representative.oldTarget) he
  rw [oldTwist_twice, map_zero] at hh'
  exact (DFinsupp.mem_support_iff.mp hq) hh'

/-- The prescribed distinct-colour factor has the unit `t i x` as highest moving coefficient. -/
theorem projection_qPoly_regular (i x : I) (hix : i ≠ x) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (qPoly D Sc (dotE D Sc (i :: v) 0) (dotE D Sc (i :: v) (b + 1)) i x) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  by_cases hd : D.d i x = 0
  · rw [qPoly, ite_eq_left hd, map_smul, End.one_def, affineUnit_id,
      Linear.smul_comp, Category.id_comp, map_smul] at hh
    exact (Sc.t i x).isUnit.smul_eq_zero.mp hh
  let z := projection D Sc cutoff i v w h
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hpos : 0 < D.dn i x := by
    have hc := D.dn_cast hix
    omega
  have hb (d : ℕ) (hlt : d < D.dn i x) :
      ∀ t ∈ f.support, d + t.1.1 < (q.representative.shift (D.dn i x)).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change d + t.1.1 < D.dn i x + q.representative.1.1
    omega
  have hlow (d e : ℕ) (hlt : d < D.dn i x) :
      prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
        (projection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (i :: v) 0 ^ d * dotE D Sc (i :: v) (b + 1) ^ e) ≫ h)) = 0 := by
    rw [End.mul_def, affineUnit_comp, Category.assoc, projection_old_dotPower,
      projection_moving_dotPower]
    simpa only [f, prependOldReconstruct_coordinateEquiv] using
      oldSource_movingPower_above D Sc cutoff 0 (q.representative.shift (D.dn i x))
        d (sourceDotPower D Sc cutoff v b e) f (hb d hlt)
  have hold : prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
      (projection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1) ^ D.dn x i) ≫ h)) = 0 := by
    simpa only [pow_zero, one_mul] using hlow 0 (D.dn x i) hpos
  rw [qPoly, ite_eq_right hd, map_add, map_add, Preadditive.add_comp,
    Preadditive.add_comp, map_add, map_add] at hh
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))) hh
  simp only [map_add, map_zero, map_sum, Preadditive.sum_comp, map_smul,
    Linear.smul_comp] at he
  have hl : (∑ d ∈ Finset.range (D.dn i x), ∑ e ∈ Finset.range (D.dn x i),
      Sc.s i x d e • prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
        (projection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (i :: v) 0 ^ d * dotE D Sc (i :: v) (b + 1) ^ e) ≫ h))) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd'
    apply Finset.sum_eq_zero
    intro e _
    rw [hlow d e (Finset.mem_range.mp hd'), smul_zero]
  rw [hl, hold, smul_zero, add_zero, zero_add, projection_moving_dotPower,
    signedMovingPower_coordinate] at he
  have ht := (Sc.t i x).isUnit.smul_eq_zero.mp he
  have ht' := congrArg (oldTwist D Sc cutoff (D.dn i x • D.parity i) v q.representative.oldTarget) ht
  rw [oldTwist_twice, map_zero] at ht'
  exact (DFinsupp.mem_support_iff.mp hq) ht'

/-- Every actual signed QP factor cancels in the old-only quotient. -/
theorem projection_qpFactor_regular (i : I) (v w : List I) (x : I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpFactor D Sc i v x b) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold qpFactor at hh
  split_ifs at hh with hx hi
  · rw [pow_two, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_dotDifference_regular D Sc cutoff i v w b h
      (projection_dotDifference_regular D Sc cutoff i v w b _ hh)
  · rw [map_neg, End.one_def, affineUnit_id, Preadditive.neg_comp,
      Category.id_comp, map_neg, neg_eq_zero] at hh
    exact hh
  · exact projection_qPoly_regular D Sc cutoff i x (Ne.symm hx) v w b h hh

/-- Cancellation for a list of the prescribed factors, in their actual multiplication order. -/
theorem projection_qpFactorList_regular (i : I) (v w : List I) (l : List ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        ((l.map fun b => qpFactor D Sc i v (v.getD b i) b).prod) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  induction l generalizing h with
  | nil => simpa only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id,
      Category.id_comp] using hh
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_qpFactor_regular D Sc cutoff i v w (v.getD b i) b h (ih _ hh)

/-- The signed all-word product is regular, without assuming any monicity or support bound. -/
theorem projection_qpProduct_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_qpFactorList_regular D Sc cutoff i v w (List.range v.length) h hh

/-- Actual full-ELV QP regularity in diagram composition order.
This is the raw-quotient injectivity input to the deformed square resolution;
it does not assume that the displayed operation descends to an endomorphism. -/
theorem projection_qp_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫
        relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_relation_regular D Sc cutoff i v w h
    (projection_qpProduct_regular D Sc cutoff i v w _ hh)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Injectivity of the full ELV P map

The actual quotient composite QP is regular in moving PBW coordinates.
Consequently the prescribed P map is injective, supplying the injectivity
step of the deformed square resolution. Polynomial-module linearity,
identification of the cokernel and projectivity are separate obligations.
-/

noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The descended signed QP operation is injective on the actual old-only quotient. -/
theorem signedQPMap_injective (i : I) (v w : List I) :
    Function.Injective (signedQPMap D Sc cutoff i v w) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  simp only [signedQPMap_projection, Category.assoc] at hz
  exact projection_qp_relation_regular D Sc cutoff i v w h hz

/-- The prescribed P map is injective for all words, cutoffs and full exterior coefficients. -/
theorem pMap_injective (i : I) (v w : List I) :
    Function.Injective (pMap D Sc cutoff i v w) := by
  intro x y hxy
  apply signedQPMap_injective D Sc cutoff i v w
  have h := congrArg (qMap D Sc cutoff i v w) hxy
  change ((qMap D Sc cutoff i v w).comp (pMap D Sc cutoff i v w)) x =
    ((qMap D Sc cutoff i v w).comp (pMap D Sc cutoff i v w)) y at h
  simpa only [qMap_comp_pMap] using h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Monic normalized endpoint norm polynomials

The independent moving-chain norm factors have the prescribed scalar unit leading
coefficients over any possibly noncommutative coefficient ring. Their ordered
normalized product is monic. `EndpointNormEvaluation` evaluates this polynomial
on actual affine dots; neither norm cancellation in a cyclotomic quotient nor
bounded cyclotomic support is inferred from monicity alone.
-/

noncomputable section
open scoped Classical
open Polynomial
namespace OddMath.QuiverHecke
open IntertwinerMeet
universe u v
variable {I k : Type u} {L : Type v} [AddCommGroup L]
  (D : SKM.Datum I L) [CommRing k] (Sc : SKM.Scalars D k)
variable {B : Type*} [Ring B] [Algebra k B]

theorem qLeft_polynomial_leadingCoeff (u : B) (d e : ℕ) (he : 0 < e)
    (t₁ : k) (t₂ : kˣ) (s : ℕ → ℕ → k) :
    (qLeft (C u) (X : Polynomial B) d e t₁ (t₂ : k) s).leadingCoeff =
      algebraMap k B (t₂ : k) := by
  nontriviality B
  have ht : algebraMap k B (t₂ : k) ≠ 0 := (t₂.isUnit.map (algebraMap k B)).ne_zero
  have hlow : (∑ p ∈ Finset.range d, ∑ q ∈ Finset.range e,
      s p q • ((C u : Polynomial B) ^ p * X ^ q)).degree < (e : WithBot ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp)).mpr
    intro p hp
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp)).mpr
    intro q hq
    apply lt_of_le_of_lt (degree_smul_le _ _)
    rw [← map_pow]
    exact (degree_C_mul_X_pow_le q (u ^ p)).trans_lt
      (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hq))
  have hconst : ((t₁ • (C u : Polynomial B) ^ d)).degree < (e : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_smul_le _ _)
    rw [← map_pow]
    exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr he)
  have htop : (t₂.val • (X : Polynomial B) ^ e) =
      C (algebraMap k B t₂.val) * X ^ e := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  unfold qLeft
  rw [← add_assoc, htop, leadingCoeff_add_of_degree_lt]
  · simp
  · rw [degree_C_mul_X_pow e ht]
    exact (degree_add_le _ _).trans_lt (max_lt hlow hconst)

/-- The literal leading scalar: diagonal minus sign, or the appropriate t unit. -/
def endpointNormLeadingUnit (j i : I) : kˣ :=
  if j = i then -1 else if D.d j i = 0 then Sc.t j i else Sc.t i j

theorem endpointNormFactor_polynomial_leadingCoeff (j i : I) (u : B) :
    (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).leadingCoeff =
      algebraMap k B (endpointNormLeadingUnit D Sc j i : k) := by
  unfold endpointNormFactor endpointNormLeadingUnit
  split_ifs with hji hp hd
  · have hm : (((X : Polynomial B) ^ 2 - C u ^ 2) ^ 2 *
        (C u ^ 2 + X ^ 2)).Monic := by
      apply Monic.mul
      · apply Monic.pow
        simpa only [← map_pow] using
          (monic_X_pow_sub_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
      · simpa only [← map_pow, add_comm] using
          (monic_X_pow_add_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
    simp [leadingCoeff_neg, hm.leadingCoeff]
  · have hm : (((X : Polynomial B) - C u) ^ 2).Monic :=
      (monic_X_sub_C u).pow 2
    simp [leadingCoeff_neg, hm.leadingCoeff]
  · simp only [Polynomial.algebraMap_apply, leadingCoeff_C]
  · have he : 0 < D.dn i j := by
      have hc := D.dn_cast (Ne.symm hji)
      have hz : D.d i j ≠ 0 := fun hz => hd ((D.d_eq_zero_iff j i).mpr hz)
      omega
    exact qLeft_polynomial_leadingCoeff u _ _ he _ _ _

/-- Left normalization by the explicit inverse sign/t unit. -/
def normalizedEndpointNormFactor (j i : I) (u : B) : Polynomial B :=
  C (algebraMap k B ((endpointNormLeadingUnit D Sc j i)⁻¹ : kˣ)) *
    endpointNormFactor D Sc j i (C u) X

theorem normalizedEndpointNormFactor_monic (j i : I) (u : B) :
    (normalizedEndpointNormFactor D Sc j i u).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [endpointNormFactor_polynomial_leadingCoeff, ← map_mul]
  simp

/-- Ordered normalized product; no commutativity of the coefficient ring is used. -/
def normalizedEndpointNormPolynomial (i : I) : List (I × B) → Polynomial B
  | [] => 1
  | (j, u) :: xs => normalizedEndpointNormFactor D Sc j i u *
      normalizedEndpointNormPolynomial i xs

theorem normalizedEndpointNormPolynomial_monic (i : I) (xs : List (I × B)) :
    (normalizedEndpointNormPolynomial D Sc i xs).Monic := by
  induction xs with
  | nil => exact monic_one
  | cons x xs ih =>
    exact (normalizedEndpointNormFactor_monic D Sc x.1 i x.2).mul ih

end OddMath.QuiverHecke
end

end

section

/-! # Evaluation of the ordered monic endpoint norm

Parity-supported old-dot powers commute with the moving dot even when the
individual dots do not. Evaluation therefore recovers the independent chain
norm times its explicit inverse leading unit, for arbitrary words.
-/
noncomputable section
namespace OddMath.QuiverHecke
open Polynomial IntertwinerMeet
universe u v
variable {I k : Type u} {L : Type v} [AddCommGroup L]
  (D : SKM.Datum I L) [CommRing k] (Sc : SKM.Scalars D k)
variable {B : Type*} [Ring B] [Algebra k B]

def NormCoeffCommute (x : B) (p : Polynomial B) : Prop :=
  ∀ n, Commute (p.coeff n) x

namespace NormCoeffCommute
variable {x : B} {p q : Polynomial B}
theorem const {a : B} (h : Commute a x) : NormCoeffCommute x (C a) := by
  intro n
  by_cases hn : n = 0 <;> simp [coeff_C, hn, h]
theorem X : NormCoeffCommute x (Polynomial.X : Polynomial B) := by
  intro n
  by_cases hn : 1 = n <;> simp [coeff_X, hn]
theorem add (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p + q) := by
  intro n
  simpa using (hp n).add_left (hq n)
theorem neg (hp : NormCoeffCommute x p) : NormCoeffCommute x (-p) := by
  intro n
  simpa using (hp n).neg_left
theorem sub (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p - q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg
theorem mul (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p * q) := by
  intro n
  rw [coeff_mul]
  apply Commute.sum_left
  intro a ha
  exact (hp a.1).mul_left (hq a.2)
theorem pow (hp : NormCoeffCommute x p) (n : ℕ) : NormCoeffCommute x (p ^ n) := by
  induction n with
  | zero => simpa using (const (Commute.one_left x))
  | succ n ih => simpa only [pow_succ] using ih.mul hp
theorem eval_mul (hq : NormCoeffCommute x q) :
    (p * q).eval₂ (RingHom.id B) x =
      p.eval₂ (RingHom.id B) x * q.eval₂ (RingHom.id B) x :=
  eval₂_mul_noncomm _ _ hq
theorem eval_pow (hp : NormCoeffCommute x p) (n : ℕ) :
    (p ^ n).eval₂ (RingHom.id B) x = (p.eval₂ (RingHom.id B) x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hp.eval_mul, ih, pow_succ]
end NormCoeffCommute

theorem eval₂_qLeft (u x : B) (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) :
    (qLeft (C u) (X : Polynomial B) d e t₁ t₂ s).eval₂ (RingHom.id B) x =
      qLeft u x d e t₁ t₂ s := by
  have hx : (X ^ e : Polynomial B).eval x = x ^ e := eval₂_X_pow _ _
  simp [qLeft, eval₂_finsetSum, ← map_pow, hx]

theorem eval₂_endpointNormFactor (j i : I) (u x : B)
    (hodd : Commute (u ^ 2) x) (heven : D.parity j ≠ 1 → Commute u x) :
    (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).eval₂ (RingHom.id B) x =
      endpointNormFactor D Sc j i u x := by
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hc : NormCoeffCommute x ((C u : Polynomial B) ^ 2) := by
      simpa only [← map_pow] using NormCoeffCommute.const hodd
    have hx := (NormCoeffCommute.X (x := x)).pow 2
    rw [eval₂_neg, (hc.add hx).eval_mul, (hx.sub hc).eval_pow]
    simp [← map_pow]
  · rw [eval₂_neg, ((NormCoeffCommute.X (x := x)).sub
      (NormCoeffCommute.const (heven hp))).eval_pow]
    simp
  · simp [Polynomial.algebraMap_apply]
  · exact eval₂_qLeft u x _ _ _ _ _

theorem eval₂_normalizedEndpointNormFactor (j i : I) (u x : B)
    (hodd : Commute (u ^ 2) x) (heven : D.parity j ≠ 1 → Commute u x) :
    (normalizedEndpointNormFactor D Sc j i u).eval₂ (RingHom.id B) x =
      algebraMap k B ((endpointNormLeadingUnit D Sc j i)⁻¹ : kˣ) *
        endpointNormFactor D Sc j i u x := by
  unfold normalizedEndpointNormFactor
  rw [← Polynomial.algebraMap_apply, ← Algebra.smul_def, eval₂_id, eval_smul, ← eval₂_id,
    eval₂_endpointNormFactor D Sc j i u x hodd heven, Algebra.smul_def]

theorem NormCoeffCommute.smul {x : B} {p : Polynomial B}
    (hp : NormCoeffCommute x p) (a : k) : NormCoeffCommute x (a • p) := by
  intro n
  change Commute (a • p.coeff n) x
  rw [Algebra.smul_def]
  exact (Algebra.commute_algebraMap_left a x).mul_left (hp n)

theorem NormCoeffCommute.sum {x : B} {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial B) (h : ∀ a ∈ s, NormCoeffCommute x (f a)) :
    NormCoeffCommute x (∑ a ∈ s, f a) := by
  intro n
  rw [finsetSum_coeff]
  apply Commute.sum_left
  intro a ha
  exact h a ha n

theorem endpointNormFactor_coeffCommute (j i : I) (u x : B)
    (hpow : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → Commute (u ^ n) x) :
    NormCoeffCommute x (endpointNormFactor D Sc j i (C u) (X : Polynomial B)) := by
  have hc (n : ℕ) (hn : (n : ZMod 2) * D.parity j = 0) :
      NormCoeffCommute x ((C u : Polynomial B) ^ n) := by
    simpa only [← map_pow] using NormCoeffCommute.const (hpow n hn)
  have hx := NormCoeffCommute.X (x := x)
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hc2 := hc 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul])
    exact (((hx.pow 2).sub hc2).pow 2 |>.mul (hc2.add (hx.pow 2))).neg
  · have hc1 : NormCoeffCommute x (C u) := by
      simpa using hc 1 (by rw [parity_eq_zero_of_ne_one hp, mul_zero])
    exact ((hx.sub hc1).pow 2).neg
  · rw [Polynomial.algebraMap_apply]
    exact NormCoeffCommute.const (Algebra.commutes _ _)
  · unfold qLeft
    apply NormCoeffCommute.add
    · apply NormCoeffCommute.sum
      intro p hp
      apply NormCoeffCommute.sum
      intro q hq
      by_cases hs : Sc.s j i p q = 0
      · simp only [hs, zero_smul]
        simpa using (NormCoeffCommute.const (Commute.zero_left x))
      · apply NormCoeffCommute.smul
        apply NormCoeffCommute.mul _ (hx.pow q)
        exact hc p (zmod_two_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero j i p q h))
    · exact ((hc _ (dn_mul_parity D j i)).smul _).add ((hx.pow _).smul _)

theorem normalizedEndpointNormFactor_coeffCommute (j i : I) (u x : B)
    (hpow : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → Commute (u ^ n) x) :
    NormCoeffCommute x (normalizedEndpointNormFactor D Sc j i u) := by
  exact (NormCoeffCommute.const (Algebra.commutes _ _)).mul
    (endpointNormFactor_coeffCommute D Sc j i u x hpow)

theorem norm_mul_pow_signed (a b : B) (e : k) (h : a * b = e • (b * a))
    (n : ℕ) : a * b ^ n = e ^ n • (b ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h,
      mul_smul_comm, ← mul_assoc, smul_smul, ← pow_succ, ← pow_succ]

open CategoryTheory in
theorem norm_oldDot_pow_commute (l m : List I) (j i : I) (n : ℕ)
    (hn : (n : ZMod 2) * D.parity j = 0) :
    Commute (dotE D Sc (l ++ [j] ++ m ++ [i]) l.length ^ n)
      (dotE D Sc (l ++ [j] ++ m ++ [i]) (l.length + 1 + m.length)) := by
  have hs := genE_interchange D Sc l m [] (.dot j) (.dot i) rfl rfl
    (w := l ++ [j] ++ m ++ [i]) (by simp [Shape.dom]) (p := l.length)
    (q := l.length + 1 + m.length) rfl (by simp only [Shape.dom, List.length_append, List.length_singleton])
  simp only [Shape.parity, PG.ofShape] at hs
  have h := norm_mul_pow_signed _ _ _ hs n
  rw [zsign_pow, ← mul_assoc, hn, zero_mul] at h
  simp [SKM.zsign] at h
  exact h.symm

theorem normalizedEndpointNormPolynomial_coeffCommute (i : I) (xs : List (I × B)) (x : B)
    (h : ∀ z ∈ xs, ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 → Commute (z.2 ^ n) x) :
    NormCoeffCommute x (normalizedEndpointNormPolynomial D Sc i xs) := by
  induction xs with
  | nil => exact NormCoeffCommute.const (Commute.one_left x)
  | cons z zs ih =>
    exact (normalizedEndpointNormFactor_coeffCommute D Sc z.1 i z.2 x
      (h z (by simp))).mul (ih fun a ha => h a (by simp [ha]))

theorem eval₂_normalizedEndpointNormPolynomial (i : I) (xs : List (I × B)) (x : B)
    (h : ∀ z ∈ xs, ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 → Commute (z.2 ^ n) x) :
    (normalizedEndpointNormPolynomial D Sc i xs).eval₂ (RingHom.id B) x =
      algebraMap k B (((xs.map fun z => (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
        (xs.map fun z => endpointNormFactor D Sc z.1 i z.2 x).prod := by
  induction xs with
  | nil => simp [normalizedEndpointNormPolynomial]
  | cons z zs ih =>
    have ht := fun a ha => h a (List.mem_cons_of_mem z ha)
    rw [normalizedEndpointNormPolynomial,
      (normalizedEndpointNormPolynomial_coeffCommute D Sc i zs x ht).eval_mul,
      eval₂_normalizedEndpointNormFactor D Sc z.1 i z.2 x
        (h z (by simp) 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]))
        (fun hp => by simpa using h z (by simp) 1 (by rw [parity_eq_zero_of_ne_one hp, mul_zero])),
      ih ht]
    simp only [List.map_cons, List.prod_cons, Units.val_mul, map_mul]
    rw [mul_assoc, ← mul_assoc (endpointNormFactor D Sc z.1 i z.2 x),
      ← Algebra.commutes, ← mul_assoc, ← mul_assoc]
    exact mul_assoc _ _ _

open CategoryTheory

def endpointOldDotEntries (w : List I) : ℕ → List I → List (I × End ((pres D Sc).obj (ob D w)))
  | _, [] => []
  | p, j :: ν => (j, dotE D Sc w p) :: endpointOldDotEntries w (p + 1) ν

theorem endpointOldDotEntries_pow_commute (i : I) (ν l : List I) :
    ∀ z ∈ endpointOldDotEntries D Sc (l ++ ν ++ [i]) l.length ν,
      ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 →
        Commute (z.2 ^ n) (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) := by
  induction ν generalizing l with
  | nil => simp [endpointOldDotEntries]
  | cons j ν ih =>
    intro z hz n hn
    simp only [endpointOldDotEntries, List.mem_cons] at hz
    rcases hz with rfl | hz
    · have hh := norm_oldDot_pow_commute D Sc l ν j i n hn
      have hw : l ++ [j] ++ ν ++ [i] = l ++ (j :: ν) ++ [i] := by simp
      rw [hw] at hh
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ν.length] using hh
    · have hh := ih (l ++ [j])
      have hw : (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] := by simp
      rw [hw] at hh
      simp only [List.length_append, List.length_singleton] at hh
      have hc := hh z hz n hn
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ν.length] using hc

theorem endpointOldDotEntries_eval_prod (i : I) (w : List I) (moving old : ℕ) (ν : List I) :
    ((endpointOldDotEntries D Sc w old ν).map fun z =>
      endpointNormFactor D Sc z.1 i z.2 (dotE D Sc w moving)).prod =
      endpointNormAux D Sc i w moving old ν := by
  induction ν generalizing old with
  | nil => rfl
  | cons j ν ih =>
    simp only [endpointOldDotEntries, List.map_cons, List.prod_cons, endpointNormAux, ih]

theorem eval₂_normalizedEndpointNormPolynomial_dotE (i : I) (l ν : List I) :
    let xs := endpointOldDotEntries D Sc (l ++ ν ++ [i]) l.length ν
    (normalizedEndpointNormPolynomial D Sc i xs).eval₂ (RingHom.id _)
        (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) =
      algebraMap k _ (((xs.map fun z => (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
        endpointNorm D Sc i l ν := by
  dsimp only
  rw [eval₂_normalizedEndpointNormPolynomial D Sc _ _ _
    (endpointOldDotEntries_pow_commute D Sc i ν l), endpointOldDotEntries_eval_prod]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # Full-coefficient monic moving-dot product

The literal ELV coefficient polynomial times the normalized full chain norm is
monic. Its evaluation is the ordered categorical norm followed by the endpoint
ELV relation. All coefficients lie in the original full super coefficient category.
`ELVMonicAnnihilator` applies this polynomial to the full cyclotomic ideal.
-/

noncomputable section
open CategoryTheory Polynomial
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def affineUnitEndHom (w : List I) :
    End ((pres D Sc).obj (ob D w)) →+* End (obj D Sc cutoff w) where
  toFun := affineUnit D Sc cutoff w w
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := affineUnit_id D Sc cutoff w
  map_mul' f g := affineUnit_comp D Sc cutoff g f

@[simp] theorem affineUnitEndHom_apply (w : List I)
    (f : End ((pres D Sc).obj (ob D w))) :
    affineUnitEndHom D Sc cutoff w f = affineUnit D Sc cutoff w w f := rfl

def movingELVPolynomial (i : I) (v : List I) : Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  ∑ r : Fin (cutoff i + 1),
    (C (R := End (obj D Sc cutoff (v ++ [i]))))
      (ELVPScalar.scalar D Sc cutoff (v ++ [i]) (singleCoefficient D cutoff i r)) * X ^ r.val

private theorem finiteMonic {B : Type*} [Ring B] (n : ℕ) (a : Fin (n + 1) → B)
    (ha : a (Fin.last n) = 1) : (∑ r, C (a r) * X ^ r.val).Monic := by
  apply monic_of_degree_le n
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro r hr
    exact (degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Nat.le_of_lt_succ r.isLt)
  · rw [finsetSum_coeff, Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, coeff_C_mul_X_pow, ite_true, ha]
    · intro r hr hn
      rw [coeff_C_mul_X_pow]
      split_ifs with h
      · exact (hn (Fin.ext h.symm)).elim
      · rfl
    · simp

theorem movingELVPolynomial_monic (i : I) (v : List I) :
    (movingELVPolynomial D Sc cutoff i v).Monic := by
  apply finiteMonic (cutoff i)
  rw [singleCoefficient_top]
  rfl

theorem movingELVPolynomial_eval (i : I) (v : List I) :
    (movingELVPolynomial D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      ∑ r : Fin (cutoff i + 1), singleCoefficient D cutoff i r ⊗ₜ[k]
        (dotE D Sc (v ++ [i]) v.length ^ r.val : End _) := by
  rw [movingELVPolynomial, eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial]
  simp only [RingHom.id_apply]
  rw [← map_pow, End.mul_def]
  exact affineUnit_comp_scalar D Sc cutoff _ _

def affineNormalizedEndpointNormPolynomial (i : I) (v : List I) :
    Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  (normalizedEndpointNormPolynomial D Sc i
    (endpointOldDotEntries D Sc (v ++ [i]) 0 v)).map (affineUnitEndHom D Sc cutoff _)

theorem affineNormalizedEndpointNormPolynomial_monic (i : I) (v : List I) :
    (affineNormalizedEndpointNormPolynomial D Sc cutoff i v).Monic :=
  (normalizedEndpointNormPolynomial_monic D Sc i _).map _

theorem affineNormalizedEndpointNormPolynomial_coeffCommute (i : I) (v : List I) :
    NormCoeffCommute
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length))
      (affineNormalizedEndpointNormPolynomial D Sc cutoff i v) := by
  have h := endpointOldDotEntries_pow_commute D Sc i v []
  simp only [List.nil_append, List.length_nil, zero_add] at h
  have hc := normalizedEndpointNormPolynomial_coeffCommute D Sc i _ _ h
  intro n
  simpa only [affineNormalizedEndpointNormPolynomial, coeff_map] using
    (hc n).map (affineUnitEndHom D Sc cutoff (v ++ [i]))

theorem affineNormalizedEndpointNormPolynomial_eval (i : I) (v : List I) :
    (affineNormalizedEndpointNormPolynomial D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      affineUnitEndHom D Sc cutoff (v ++ [i])
        (algebraMap k (End ((pres D Sc).obj (ob D ([] ++ v ++ [i]))))
          ((((endpointOldDotEntries D Sc (v ++ [i]) 0 v).map fun z =>
            (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
          endpointNorm D Sc i [] v) := by
  have h := eval₂_normalizedEndpointNormPolynomial_dotE D Sc i [] v
  simp only [List.nil_append, List.length_nil, zero_add] at h
  change Polynomial.eval₂ (RingHom.id _)
    (affineUnitEndHom D Sc cutoff _ (dotE D Sc (v ++ [i]) v.length))
    (Polynomial.map (affineUnitEndHom D Sc cutoff _)
      (normalizedEndpointNormPolynomial D Sc i _)) = _
  rw [eval₂_map, RingHom.id_comp, eval₂_at_apply]
  exact congrArg (affineUnitEndHom D Sc cutoff _) h

def monicELVEndpointProduct (i : I) (v : List I) :
    Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  movingELVPolynomial D Sc cutoff i v * affineNormalizedEndpointNormPolynomial D Sc cutoff i v

theorem monicELVEndpointProduct_monic (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).Monic :=
  (movingELVPolynomial_monic D Sc cutoff i v).mul
    (affineNormalizedEndpointNormPolynomial_monic D Sc cutoff i v)

theorem monicELVEndpointProduct_eval (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      (∑ r : Fin (cutoff i + 1), singleCoefficient D cutoff i r ⊗ₜ[k]
        (dotE D Sc (v ++ [i]) v.length ^ r.val : End _) : End (obj D Sc cutoff (v ++ [i]))) *
      affineUnitEndHom D Sc cutoff (v ++ [i])
        (algebraMap k (End ((pres D Sc).obj (ob D ([] ++ v ++ [i]))))
          ((((endpointOldDotEntries D Sc (v ++ [i]) 0 v).map fun z =>
            (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
          endpointNorm D Sc i [] v) := by
  refine (affineNormalizedEndpointNormPolynomial_coeffCommute D Sc cutoff i v).eval_mul.trans ?_
  exact congrArg₂ (fun a b : End (obj D Sc cutoff (v ++ [i])) => a * b)
    (movingELVPolynomial_eval D Sc cutoff i v)
    (affineNormalizedEndpointNormPolynomial_eval D Sc cutoff i v)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Full ELV polynomial at the append endpoint

`relation_comp_move` transports the finite all-colour cyclotomic polynomial
through G with its total coefficient parity sign. This provides the ordered
coefficient comparison in `DeformedBoundaryDivision.md` §3. It imposes no
cyclotomic relation on the moving endpoint.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def endpointCoefficient (i : I) (j : Fin (cutoff i + 1)) : SKM.SYM D k :=
  if h : D.parity i = 1 then
    SKM.SYM.elvMonicCoefficient D k ⟨i, h⟩ (cutoff i) j
  else SKM.SYM.evenMonicCoefficient D k i (cutoff i) j

private theorem endpointCoefficient_parity (i : I) (j : Fin (cutoff i + 1)) :
    SKM.SYM.polynomialExteriorEquiv D k (endpointCoefficient D cutoff i j) ∈
      SKM.SYM.polynomialExteriorParity D k
        (cutoff i • D.parity i - j.val • D.parity i) := by
  unfold endpointCoefficient
  split_ifs with hi
  · simpa only [hi, nsmul_eq_mul, mul_one] using
      (SKM.SYM.elvMonicCoefficient_mem_parity (k := k) D ⟨i, hi⟩ (cutoff i) j)
  · have he : D.parity i = 0 := (parity_eq_zero_or_one (D.parity i)).resolve_right hi
    simp only [he, nsmul_zero, sub_self, SKM.SYM.evenMonicCoefficient, map_smul]
    apply Submodule.smul_mem
    cases cutoff i - j.val with
    | zero =>
        simpa only [SKM.SYM.evenCyclotomicCoefficient, map_one] using
          (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior D k) ∈
            SKM.SYM.polynomialExteriorParity D k 0)
    | succ n => exact SKM.SYM.polynomialExterior_e_mem_even D k i n

private theorem relation_as_polynomial (i : I) (v : List I) :
    relation D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (coefficientDotPolynomial D Sc (i :: v) 0 (cutoff i)
          (endpointCoefficient D cutoff i)) := by
  unfold relation endpointCoefficient
  dsimp only [elvQuotientFunctor]
  split_ifs with hi
  · apply congrArg (elvQuotientMap D Sc cutoff _ _)
    exact (elvDotPolynomial_first D Sc ⟨i, hi⟩ v (cutoff i)).symm
  · apply congrArg (elvQuotientMap D Sc cutoff _ _)
    unfold evenCyclotomic deformedCyclotomic coefficientDotPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [dotE_pow, firstDotPower, List.map_replicate]

/-- The full finite ELV polynomial at the last strand, with coefficients on the left. -/
def endpointELV (i : I) (v : List I) : hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  ∑ j : Fin (cutoff i + 1), singleCoefficient D cutoff i j ⊗ₜ[k]
    (dotE D Sc (v ++ [i]) v.length ^ j.val : End _)

private theorem endpointELV_as_polynomial (i : I) (v : List I) :
    endpointELV D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (coefficientDotPolynomial D Sc (v ++ [i]) v.length (cutoff i)
          (endpointCoefficient D cutoff i)) := by
  change _ = elvQuotientMap D Sc cutoff _ _ _
  unfold endpointELV coefficientDotPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (elvQuotientMap_source D Sc cutoff (endpointCoefficient D cutoff i j)
    (dotE D Sc (v ++ [i]) v.length ^ j.val)).symm

private theorem move_as_map (i : I) (v : List I) :
    move D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] v)) := by
  change _ = elvQuotientMap D Sc cutoff _ _ _
  rw [elvQuotientMap_source, map_one]
  rfl

/-- Full-coefficient moving-polynomial transport, at every colour and cutoff. -/
theorem relation_comp_move (i : I) (v : List I) :
    relation D Sc cutoff i v ≫ move D Sc cutoff i v =
      sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
        (move D Sc cutoff i v ≫ endpointELV D Sc cutoff i v) := by
  have h := coefficientDotPolynomial_comp_moveHom D Sc i [] v (cutoff i)
    (endpointCoefficient D cutoff i) (cutoff i • D.parity i)
    (endpointCoefficient_parity D cutoff i)
  have hq := congrArg (fun f => (elvQuotientFunctor D Sc cutoff).map f) h
  rw [relation_as_polynomial, endpointELV_as_polynomial, move_as_map]
  simp only [List.nil_append, List.length_nil, zero_add,
    Functor.map_comp, Functor.map_smul] at hq
  dsimp only [elvQuotientFunctor] at hq ⊢
  exact hq
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Actual full-cyclotomic moving-dot annihilator

The concrete monic polynomial evaluates into the full cyclotomic ideal, by
sandwiching the first-position relation between the reverse and moving chains.
Only the scalar parity sign is removed; no chain norm is cancelled. Together
with `ELVMonicOldCoefficients`, this supplies the old-coefficient recurrence
needed for bounded moving-exponent reduction at arbitrary content.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Polynomial
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem endpointNorm_endpointELV_mem_ideal (i : I) (v : List I) :
    affineUnit D Sc cutoff _ _ (endpointNorm D Sc i [] v) ≫ endpointELV D Sc cutoff i v ∈
      ideal D Sc cutoff (v ++ [i]) (v ++ [i]) := by
  have h := comp_ideal D Sc cutoff
    (affineUnit D Sc cutoff _ _ (reverseMoveHom D Sc i [] v))
    (ideal_comp D Sc cutoff (relation_mem D Sc cutoff i v) (move D Sc cutoff i v))
  rw [relation_comp_move, Linear.comp_smul, ← Category.assoc] at h
  change sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
    ((affineUnit D Sc cutoff _ _ (reverseMoveHom D Sc i [] v) ≫
      affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v)) ≫ endpointELV D Sc cutoff i v) ∈ _ at h
  rw [← affineUnit_comp, reverseMoveHom_comp_moveHom_eq_endpointNorm] at h
  have hh := (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).smul_mem
    (sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v))) h
  simpa only [sign_smul_sign_smul] using hh

theorem affineUnitEndHom_smul (w : List I) (c : k)
    (f : End ((pres D Sc).obj (ob D w))) :
    affineUnitEndHom D Sc cutoff w (c • f) = c • affineUnitEndHom D Sc cutoff w f :=
  (affineUnit D Sc cutoff w w).map_smul c f

theorem monicELVEndpointProduct_eval_mem_ideal (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).eval₂ (RingHom.id (End (obj D Sc cutoff (v ++ [i]))))
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) ∈
        ideal D Sc cutoff (v ++ [i]) (v ++ [i]) := by
  let f : End (obj D Sc cutoff (v ++ [i])) := endpointELV D Sc cutoff i v
  let n : End ((pres D Sc).obj (ob D (v ++ [i]))) := endpointNorm D Sc i [] v
  let c : k := ((((endpointOldDotEntries D Sc (v ++ [i]) 0 v).map fun z =>
    (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k)
  have he : (monicELVEndpointProduct D Sc cutoff i v).eval₂
      (RingHom.id (End (obj D Sc cutoff (v ++ [i]))))
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      f * affineUnitEndHom D Sc cutoff (v ++ [i]) (c • n) := by
    simpa only [f, n, c, endpointELV, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul] using monicELVEndpointProduct_eval D Sc cutoff i v
  rw [he, affineUnitEndHom_smul, End.mul_def, Linear.smul_comp]
  exact Submodule.smul_mem _ c (endpointNorm_endpointELV_mem_ideal D Sc cutoff i v)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Old coefficients of the actual monic endpoint product

Every coefficient of the enlarged monic moving-dot polynomial is explicitly
inserted from the old full-coefficient endomorphism ring. This is the coefficient
closure input for bounded moving-exponent reduction from `ELVMonicAnnihilator`;
no centrality of arbitrary full ELV coefficients is assumed.
-/

noncomputable section
open CategoryTheory Polynomial
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def rightContextEndHom (i : I) (v : List I) :
    End (obj D Sc cutoff v) →+* End (obj D Sc cutoff (v ++ [i])) where
  toFun := rightContext D Sc cutoff [i] v v
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := rightContext_id D Sc cutoff [i] v
  map_mul' f g := rightContext_comp D Sc cutoff [i] g f

@[simp] theorem rightContextEndHom_apply (i : I) (v : List I)
    (f : End (obj D Sc cutoff v)) :
    rightContextEndHom D Sc cutoff i v f = rightContext D Sc cutoff [i] v v f := rfl

private theorem normalizedFactor_map {B C' : Type*} [Ring B] [Ring C']
    [Algebra k B] [Algebra k C'] (f : B →ₐ[k] C') (j i : I) (x : B) :
    (normalizedEndpointNormFactor D Sc j i x).map f.toRingHom =
      normalizedEndpointNormFactor D Sc j i (f x) := by
  simp only [normalizedEndpointNormFactor, Polynomial.map_mul, Polynomial.map_C]
  congr 1
  · exact congrArg C (f.commutes _)
  · unfold endpointNormFactor
    split_ifs <;>
      simp [IntertwinerMeet.qLeft, Algebra.smul_def, Polynomial.algebraMap_apply,
        Polynomial.map_sum]

private theorem normalizedEntries_map (i : I) (w σ ν : List I) (p : ℕ)
    (h : p + ν.length ≤ w.length) :
    (normalizedEndpointNormPolynomial D Sc i (endpointOldDotEntries D Sc w p ν)).map
        (whiskerListAlgHom D Sc w σ).toRingHom =
      normalizedEndpointNormPolynomial D Sc i (endpointOldDotEntries D Sc (w ++ σ) p ν) := by
  induction ν generalizing p with
  | nil => simp [endpointOldDotEntries, normalizedEndpointNormPolynomial]
  | cons j ν ih =>
    simp only [endpointOldDotEntries, normalizedEndpointNormPolynomial, Polynomial.map_mul]
    rw [normalizedFactor_map]
    have hd : whiskerListAlgHom D Sc w σ (dotE D Sc w p) = dotE D Sc (w ++ σ) p :=
      dotE_whiskerRight D Sc w σ p (by simp only [List.length_cons] at h; omega)
    rw [hd, ih (p + 1) (by simp only [List.length_cons] at h; omega)]

/-- An explicit old-endomorphism polynomial whose image is the concrete endpoint product. -/
def oldMonicELVEndpointProduct (i : I) (v : List I) : Polynomial (End (obj D Sc cutoff v)) :=
  (∑ r : Fin (cutoff i + 1),
    C (R := End (obj D Sc cutoff v))
      (ELVPScalar.scalar D Sc cutoff v (singleCoefficient D cutoff i r)) * X ^ r.val) *
  (normalizedEndpointNormPolynomial D Sc i (endpointOldDotEntries D Sc v 0 v)).map
    (affineUnitEndHom D Sc cutoff v)

theorem oldMonicELVEndpointProduct_map (i : I) (v : List I) :
    (oldMonicELVEndpointProduct D Sc cutoff i v).map (rightContextEndHom D Sc cutoff i v) =
      monicELVEndpointProduct D Sc cutoff i v := by
  rw [oldMonicELVEndpointProduct, Polynomial.map_mul, monicELVEndpointProduct]
  congr 1
  · simp only [movingELVPolynomial, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      rightContextEndHom_apply, ELVPScalar.rightContext_scalar]
  · rw [Polynomial.map_map]
    have hc : (rightContextEndHom D Sc cutoff i v).comp (affineUnitEndHom D Sc cutoff v) =
        (affineUnitEndHom D Sc cutoff (v ++ [i])).comp
          (whiskerListAlgHom D Sc v [i]).toRingHom := by
      ext f
      rfl
    rw [hc, ← Polynomial.map_map, normalizedEntries_map D Sc i v [i] v 0 (by omega)]
    rfl

/-- Every coefficient, including coefficients outside the support, is an inserted old endomorphism. -/
theorem monicELVEndpointProduct_coeff_mem_range (i : I) (v : List I) (n : ℕ) :
    (monicELVEndpointProduct D Sc cutoff i v).coeff n ∈
      (rightContextEndHom D Sc cutoff i v).range := by
  refine ⟨(oldMonicELVEndpointProduct D Sc cutoff i v).coeff n, ?_⟩
  rw [← Polynomial.coeff_map, oldMonicELVEndpointProduct_map]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Bounded moving powers in the full ELV cyclotomic quotient

The actual monic annihilator and its explicitly old coefficients give a bounded
last-dot spanning result at every old word. The recurrence multiplies on the
right and never commutes arbitrary old coefficients across an odd dot. This
is the moving-exponent input for content induction; the all-content integer
support bound still requires finite-shuffle spanning and homogeneous projection.
-/

noncomputable section
open CategoryTheory Polynomial

namespace OddMath.QuiverHecke.ELVOld

private theorem powers_mem_ideal_sup_span
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (J : Submodule R A) (B : Subring A) (x : A) (p : Polynomial A)
    (hm : p.Monic) (hc : ∀ r, p.coeff r ∈ B)
    (he : p.eval₂ (RingHom.id A) x ∈ J)
    (hl : ∀ a b, b ∈ J → a * b ∈ J)
    (hr : ∀ a b, a ∈ J → a * b ∈ J) (n : ℕ) :
    x ^ n ∈ J ⊔ Submodule.span R {z | ∃ a ∈ B, ∃ j < p.natDegree, z = a * x ^ j} := by
  let S := Submodule.span R {z | ∃ a ∈ B, ∃ j < p.natDegree, z = a * x ^ j}
  have hleft (a : A) (ha : a ∈ B) (z : A) (hz : z ∈ S) : a * z ∈ S := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, j, hj, rfl⟩ := hz
      exact Submodule.subset_span ⟨a * b, B.mul_mem ha hb, j, hj, (mul_assoc _ _ _).symm⟩
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using S.add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using S.smul_mem r hb
  have hleft' (a : A) (ha : a ∈ B) (z : A) (hz : z ∈ J ⊔ S) : a * z ∈ J ⊔ S := by
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hl a b hb))
      (Submodule.mem_sup_right (hleft a ha c hc))
  change x ^ n ∈ J ⊔ S
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < p.natDegree
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨1, B.one_mem, n, hn, by simp⟩)
    · have hN : p.natDegree ≤ n := Nat.le_of_not_gt hn
      have hrec : p.eval₂ (RingHom.id A) x =
          (∑ r ∈ Finset.range p.natDegree, p.coeff r * x ^ r) + x ^ p.natDegree := by
        rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
        simp only [RingHom.id_apply, hm.coeff_natDegree, one_mul]
      have heq : x ^ n = p.eval₂ (RingHom.id A) x * x ^ (n - p.natDegree) -
          ∑ r ∈ Finset.range p.natDegree, p.coeff r * x ^ (r + (n - p.natDegree)) := by
        rw [hrec, add_mul, Finset.sum_mul]
        simp only [mul_assoc, ← pow_add, Nat.add_sub_of_le hN, add_sub_cancel_left]
      rw [heq]
      apply Submodule.sub_mem
      · exact Submodule.mem_sup_left (hr _ _ he)
      · apply Submodule.sum_mem
        intro r hr
        exact hleft' _ (hc r) _ (ih (r + (n - p.natDegree))
          (by have := Finset.mem_range.mp hr; omega))

universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Every power of the moving dot reduces, in the full cyclotomic quotient,
 to powers strictly below the concrete monic endpoint degree with old coefficients
 on the left. No commutation between those coefficients and the moving dot is used. -/
theorem movingDot_pow_mem_bounded_old_span (i : I) (v : List I) (n : ℕ) :
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      ((affineUnitEndHom D Sc cutoff (v ++ [i])
        (dotE D Sc (v ++ [i]) v.length)) ^ n) ∈
    Submodule.span k {z | ∃ a : End (obj D Sc cutoff v),
      ∃ j < (monicELVEndpointProduct D Sc cutoff i v).natDegree,
        z = (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
          (rightContextEndHom D Sc cutoff i v a *
            (affineUnitEndHom D Sc cutoff (v ++ [i])
              (dotE D Sc (v ++ [i]) v.length)) ^ j)} := by
  let J := ideal D Sc cutoff (v ++ [i]) (v ++ [i])
  let x := affineUnitEndHom D Sc cutoff (v ++ [i])
    (dotE D Sc (v ++ [i]) v.length)
  let p := monicELVEndpointProduct D Sc cutoff i v
  let B := (rightContextEndHom D Sc cutoff i v).range
  have h := powers_mem_ideal_sup_span J B x p
    (monicELVEndpointProduct_monic D Sc cutoff i v)
    (monicELVEndpointProduct_coeff_mem_range D Sc cutoff i v)
    (monicELVEndpointProduct_eval_mem_ideal D Sc cutoff i v)
    (fun a b hb => ideal_comp D Sc cutoff hb a)
    (fun a b ha => comp_ideal D Sc cutoff b ha) n
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
  have hqa : (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ a = 0 :=
    (Submodule.Quotient.mk_eq_zero J).mpr ha
  rw [← hab, map_add, hqa, zero_add]
  clear hab
  induction hb using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, j, hj, rfl⟩ := hz
    obtain ⟨d, rfl⟩ := hc
    exact Submodule.subset_span ⟨d, j, hj, rfl⟩
  | zero => simp
  | add b c _ _ hb hc => simpa only [map_add] using Submodule.add_mem _ hb hc
  | smul r b _ hb => simpa only [map_smul] using Submodule.smul_mem _ r hb

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Reverse moving-chain descent over ELV coefficients

Reverse old-ideal descent for the moving chains of Kang–Kashiwara–Oh.
The parity twist acts on the full coefficient-plus-diagram parity. The map
from the prepend-old quotient to the append-old quotient is ground-ring linear;
no inverse, regularity, or injectivity assertion is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The reverse moving chain has the same total parity as the forward chain. -/
theorem reverseMoveHom_parity (i : I) (l ν : List I) :
    reverseMoveHom D Sc i l ν ∈ parity (R := k) _ _ (D.parity i * wordSumParity D ν) := by
  have he {A B : (pres D Sc).Presented} (h : A = B) :
      eqToHom h ∈ parity (R := k) A B 0 := by
    subst h
    exact Supercategory.id_mem _
  induction ν generalizing l with
  | nil => simpa only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero] using he _
  | cons j ν ih =>
    simpa only [reverseMoveHom, wordSumParity, List.map_cons, List.sum_cons, mul_add,
      zero_add, add_zero, mul_comm, add_comm] using Supercategory.comp_mem (he _)
        (Supercategory.comp_mem (ih (l ++ [j]))
          (Supercategory.comp_mem (he _) (Supercategory.comp_mem
            (intertwinerHom_parity D Sc l ν j i) (he _))))

namespace ELVOld
variable (cutoff : I → ℕ)

/-- The reverse affine moving chain with unit ELV coefficient. -/
def reverseMove (i : I) (v : List I) : hom D Sc cutoff (v ++ [i]) (i :: v) :=
  affineUnit D Sc cutoff _ _ (reverseMoveHom D Sc i [] v)

/-- Reverse transport retains the coefficient parity as well as the diagram parity. -/
theorem reverseMove_comp_insert (i : I) {v t : List I} (r : hom D Sc cutoff v t) :
    reverseMove D Sc cutoff i v ≫
        insert D Sc cutoff i v t (twist k (D.parity i * wordSumParity D v) r) =
      rightContext D Sc cutoff [i] v t r ≫ reverseMove D Sc cutoff i t := by
  by_cases hp : wordSumParity D t = wordSumParity D v
  · have hz := reverseMoveHom_parity D Sc i [] t
    rw [hp] at hz
    have h := lift_twisted_square D Sc cutoff
      (affineRightContext D Sc [i] v t) (affineInsert D Sc i v t)
      (reverseMoveHom D Sc i [] v) (reverseMoveHom D Sc i [] t) hz
      (fun hf => MonoidalSupercategory.whiskerLeft_mem (R := k)
        ((pres D Sc).obj (ob D [i])) hf)
      (fun f => by
        simpa only [twist_twist, affineInsert, affineRightContext, LinearMap.coe_mk,
          AddHom.coe_mk, List.nil_append] using
          (hom_comp_reverseMoveHom D Sc i (twist k (D.parity i * wordSumParity D v) f)).symm)
      (twist k (D.parity i * wordSumParity D v) r)
    rw [twist_twist] at h
    change affineUnit D Sc cutoff (v ++ [i]) (i :: v) (reverseMoveHom D Sc i [] v) ≫
        TensorProduct.map LinearMap.id (affineInsert D Sc i v t)
          (twist k (D.parity i * wordSumParity D v) r) =
      TensorProduct.map LinearMap.id (affineRightContext D Sc [i] v t) r ≫
        affineUnit D Sc cutoff (t ++ [i]) (i :: t) (reverseMoveHom D Sc i [] t)
    exact h
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hp r]
    simp only [map_zero, Limits.comp_zero, Limits.zero_comp]

/-- Precomposition with the reverse chain preserves the old relation spans. -/
theorem reverseMove_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    reverseMove D Sc cutoff i v ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    have he := reverseMove_comp_insert D Sc cutoff i
      (twist k (D.parity i * wordSumParity D v) r)
    rw [twist_twist] at he
    rw [← Category.assoc, he, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- Reverse moving-chain map on the old-only quotients. -/
def rMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (reverseMove D Sc cutoff i v))
    (fun _ hh => reverseMove_relations D Sc cutoff i hh)

@[simp] theorem rMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    rMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff (v ++ [i]) (i :: v) (reverseMoveHom D Sc i [] v) ≫ h) := rfl

/-- The reverse-after-forward quotient composite is the append-end norm operation. -/
theorem rMap_qMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    rMap D Sc cutoff i v w (qMap D Sc cutoff i v w (appendProjection D Sc cutoff i v w h)) =
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff (v ++ [i]) (v ++ [i])
          (reverseMoveHom D Sc i [] v ≫ moveHom D Sc i [] v) ≫ h) := by
  simp only [qMap_projection, rMap_projection, affineUnit_comp, Category.assoc, List.nil_append]

end ELVOld
end OddMath.QuiverHecke
end

end
