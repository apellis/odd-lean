import StringDiagrams.Super.Functor
import StringDiagrams.Super.SCat
import StringDiagrams.Super.TwoSCat
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.SKM.FiniteColourRestriction
import OddMath.SKM.RouquierData
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.SKM.ScalarChangePresentation

/-!
# Super adjunction

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Three-strand braid identities in cyclotomic colour corners

Ports the algebraic braid input of
`Categorification/KLR/CyclotomicAction/Braid.lean`. Words read left to right,
diagrams compose bottom to top, and matrix multiplication reverses diagram
composition. The braid with distinct outside colours has no additional sign,
even when all three colours are odd. The assertion is in the concrete affine
and cyclotomic algebras, before transport through the induction associator.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- Attach three specified colours, retaining the old-word index. -/
def tripleWord (i j c : I) {n : ℕ} (w : Word I n) : Word I (n + 3) :=
  ⟨w.1 ++ [i,j,c] ++ [], by simp [w.2]⟩

/-- Crossing the first two added strands. -/
def tripleCrossLeft (i j c : I) {n : ℕ} (w : Word I n) :
    wordObj D Sc (tripleWord i j c w) ⟶ wordObj D Sc (tripleWord j i c w) :=
  cl D Sc _ _ [.cross w.1.length] (by
    simp [tripleWord, pl, PG.ld, Shape.dom, Shape.cod])

/-- Crossing the last two added strands. -/
def tripleCrossRight (i j c : I) {n : ℕ} (w : Word I n) :
    wordObj D Sc (tripleWord i j c w) ⟶ wordObj D Sc (tripleWord i c j w) :=
  cl D Sc _ _ [.cross (w.1.length + 1)] (by
    have hle : w.1.length ≤ n + 1 := by omega
    simp [tripleWord, pl, PG.ld, Shape.dom, Shape.cod, List.take_append,
      List.drop_append, List.append_assoc, List.take_of_length_le hle,
      List.drop_eq_nil_of_le hle])

/-- The diagram-level braid on each old-word corner. -/
theorem tripleCross_braid (i j c : I) (hb : ¬ (i = c ∧ i ≠ j)) {n : ℕ} (w : Word I n) :
    tripleCrossLeft D Sc i j c w ≫ tripleCrossRight D Sc j i c w ≫
        tripleCrossLeft D Sc j c i w =
      tripleCrossRight D Sc i j c w ≫ tripleCrossLeft D Sc i c j w ≫
        tripleCrossRight D Sc c i j w := by
  dsimp only [tripleCrossLeft, tripleCrossRight]
  rw [cl_comp, cl_comp, cl_comp, cl_comp]
  exact braid_ne D Sc w.1 [] i j c hb _ _

variable [Fintype I]

/-- A family of morphisms on three-strand corners as a finite matrix. -/
def tripleMatrix (i j c i' j' c' : I) {n : ℕ}
    (f : ∀ w : Word I n, wordObj D Sc (tripleWord i j c w) ⟶
      wordObj D Sc (tripleWord i' j' c' w)) : Hn D Sc (n + 3) :=
  ∑ w, FiniteHomMatrix.single (tripleWord i' j' c' w) (tripleWord i j c w) (f w)

/-- First-pair affine crossing with the third added colour fixed. -/
def affineTripleLeft (i j c : I) (n : ℕ) : Hn D Sc (n + 3) :=
  tripleMatrix D Sc i j c j i c (tripleCrossLeft D Sc i j c)

/-- Last-pair affine crossing with the first added colour fixed. -/
def affineTripleRight (i j c : I) (n : ℕ) : Hn D Sc (n + 3) :=
  tripleMatrix D Sc i j c i c j (tripleCrossRight D Sc i j c)

end OddMath.QuiverHecke
end

end

section

/-!
# The square-zero relation on cyclotomic composition corners

Ports the same-colour quadratic input of
`Categorification/KLR/CyclotomicAction/Square.lean` to the concrete super
cyclotomic quotient. The signed right multiplier, rather than ordinary right
multiplication, is used on the composition superbimodule. Thus the conclusion
also holds for an odd colour. Mixed-colour polynomial transport is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- Positioned-word coordinates for the concrete last-pair crossing. -/
theorem inductionLastCrossing_eq_cl (i j : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i j w =
      cl D Sc _ _ [.cross w.1.length] (by
        simp [appendWord, pl, PG.ld, Shape.dom, Shape.cod, List.append_assoc]) := by
  unfold inductionLastCrossing inductionStrandCrossing cl
  simp only [Presentation.associator_eq, eqToIso]
  dsimp only [wordObj]
  erw [Presentation.diag_whiskerLeft]
  rw [← (pres D Sc).diag_cast _ (Obj.tensor_assoc (ob D w.1) (ob D [i]) (ob D [j])).symm
    (Obj.tensor_assoc (ob D w.1) (ob D [j]) (ob D [i])).symm]
  apply Presentation.diag_eq_of_layers_eq
  simp [appendWord, pl, PG.ld, layList, lay, ob, List.append_assoc, Layer.wl]

variable [Fintype I]

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

end OddMath.QuiverHecke
end

end

section

/-!
# Mixed quadratic comparison on cyclotomic composition corners

Ports the algebraic comparison input of
`Categorification/KLR/CyclotomicAction/MixedComparison.lean` and the quadratic
calculation of `Categorification/KLR/CyclotomicAction/Square.lean`.
The quotient element on the right is the explicit polynomial in the two
positioned dots, not a freely specified square. Signed right multiplication
introduces the super-opposite sign. This is an upward quadratic comparison;
it does not assert the mixed induction–restriction Mackey isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial evaluated in a word endomorphism ring. -/
def wordQuadratic (i j : I) (t : List I) (r : ℕ) : End ((pres D Sc).obj (ob D t)) :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
      Sc.s i j p q • (dotE D Sc t r ^ p * dotE D Sc t (r + 1) ^ q) +
      ((Sc.t i j : k) • dotE D Sc t r ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc t (r + 1) ^ D.dn j i)

variable [Fintype I]

/-- Sum the displayed quadratic polynomial over the old-word corners. -/
def affinePairQuadratic (i j : I) (n : ℕ) : Hn D Sc (n + 1 + 1) :=
  ∑ w : Word I n, FiniteHomMatrix.single (appendWord j (appendWord i w))
    (appendWord j (appendWord i w))
    (wordQuadratic D Sc i j (appendWord j (appendWord i w)).1 w.1.length)

end OddMath.QuiverHecke
end

end

section

/-!
# An involutive transport of the even scalar parameters

Ports the parameter-comparison obligation behind
`Categorification/KLR/CyclotomicAction/MixedComparison.lean` to super scalars.
On the permitted even powers of an odd dot, signed right multiplication changes
`x^(2m)` by `(-1)^m`; two crossing multipliers contribute `(-1)^(|i||j|)`.
The coefficient family below records these signs and is again valid scalar
data. It is involutive and preserves homogeneous support. These coefficient
facts alone do not assert compatibility with the categorical braid or Mackey
map; those are separate relation-transport obligations.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The parity sign as a unit of the even coefficient ring. -/
def parameterSignUnit (p : ZMod 2) : kˣ := if p = 1 then -1 else 1

/-- The coefficient sign for a permitted two-dot monomial. -/
def parameterSignExponent (i j : I) (p q : ℕ) : ZMod 2 :=
  D.parity i * D.parity j + D.parity i * (p / 2 : ℕ) + D.parity j * (q / 2 : ℕ)

theorem parameterSignExponent_swap (i j : I) (p q : ℕ) :
    parameterSignExponent D i j p q = parameterSignExponent D j i q p := by
  unfold parameterSignExponent
  ring

/-- Transport the even coefficients while retaining their support conditions. -/
def parameterTwist : SKM.Scalars D k where
  t i j := if i = j then Sc.t i j else
    parameterSignUnit (k := k) (parameterSignExponent D i j (D.dn i j) 0) * Sc.t i j
  t_self i := by simp [Sc.t_self]
  t_symm_of_d_eq_zero i j hd := by
    by_cases hij : i = j
    · subst j; rfl
    have hd' := (D.d_eq_zero_iff i j).mp hd
    simp [hij, Ne.symm hij, parameterSignExponent, SKM.Datum.dn, hd, hd',
      Sc.t_symm_of_d_eq_zero i j hd, mul_comm]
  s i j p q := SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q
  s_symm i j p q := by rw [parameterSignExponent_swap, Sc.s_symm]
  s_eq_zero i j p q hp := by rw [Sc.s_eq_zero i j p q hp, mul_zero]
  two_isUnit := Sc.two_isUnit

/-- Signs do not enlarge the coefficient support, so homogeneity is preserved. -/
theorem parameterTwist_homogeneous (hSc : Sc.Homogeneous) : (parameterTwist D Sc).Homogeneous := by
  intro i j p q hij hp' hq' hs
  apply hSc i j p q hij hp' hq'
  intro hz
  exact hs (by simp [parameterTwist, hz])

private theorem scalars_ext {S T : SKM.Scalars D k} (ht : S.t = T.t) (hs : S.s = T.s) : S = T := by
  cases S
  cases T
  cases ht
  cases hs
  rfl

/-- The unit signs square to one. -/
theorem parameterSignUnit_square (p : ZMod 2) :
    parameterSignUnit (k := k) p * parameterSignUnit p = 1 := by
  unfold parameterSignUnit
  split_ifs <;> simp

/-- The coefficient transport is its own inverse, also over a non-field base ring. -/
theorem parameterTwist_involutive : parameterTwist D (parameterTwist D Sc) = Sc := by
  apply scalars_ext D
  · funext i j
    by_cases hij : i = j
    · simp [parameterTwist, hij]
    · simp [parameterTwist, hij, ← mul_assoc, parameterSignUnit_square]
  · funext i j p q
    change SKM.zsign k (parameterSignExponent D i j p q) *
      (SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q) = Sc.s i j p q
    rw [← mul_assoc, zsign_mul_self, one_mul]

end OddMath.QuiverHecke
end

end

section

/-!
# The homogeneous dot on cyclotomic superinduction

Ports the dot construction of `Categorification/KLR/CyclotomicAction/Induction.lean`
using the last-dot relation from `CyclotomicAction/SuperQuotient.lean`.
For the signed-left, ordinary-right superbimodule convention the corner map is
`x ↦ (-1)^{|i||x|} x c`, not unsigned right multiplication by the last dot `c`.
No square, braid or KKO relation is asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams
open Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => inductionCorner D Sc i a ha n
local notation "GB" => cyclotomicParity D Sc a ha (n + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "c" => cyclotomicLastDot D Sc i a n
local notation "d" => D.parity i

private theorem dot_mul_mem (x : CyclotomicAlgebra D Sc a (n + 1))
    (_hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    x * c ∈ inductionCornerSubmodule D Sc i a n := by
  change (x * c) * cyclotomicAppend D Sc i a n 1 = x * c
  rw [mul_assoc, (cyclotomicLastDot_corner D Sc i a n).2]

private theorem sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

end OddMath.QuiverHecke
end

end

section

/-!
# The cyclotomic super adjunction

Ports the induction-restriction adjunction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` to the actual
cyclotomic supermodule categories. The unit and counit are even and their
naturality includes odd morphisms.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

end OddMath.QuiverHecke
end

end

section

/-!
# Cyclotomic induction and restriction in the supercategory of supercategories

Ports the adjunction packaging of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` to `SKM.SuperAdjunction`.
The objects are the cyclotomic supermodule categories, and the 1-morphisms are
balanced-tensor induction and restriction. The unit and counit have only an even
component; the dot has the parity of its colour. The ambient bundled `TwoSCat`
is the existing `SCat` 2-supercategory, retaining supernatural transformations
and super-interchange. No local inversion, crossing, or vacuum extension is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The ambient 2-supercategory for the cyclotomic supermodule action. -/
abbrev cyclotomicActionTarget : TwoSCat k := TwoSCat.of k (SCat.{u, u, u + 1} k)

variable (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The cyclotomic supermodule category, as an object of the action target. -/
abbrev cyclotomicActionObject : cyclotomicActionTarget (k := k) :=
  SCat.of k (CyclotomicSupermodules D Sc a ha n)

variable (i : I)

/-- Balanced-tensor induction as a 1-morphism. -/
def cyclotomicActionInduction :
    cyclotomicActionObject D Sc a ha n ⟶ cyclotomicActionObject D Sc a ha (n + 1) :=
  ⟨cyclotomicSuperInduction D Sc i a ha n⟩

/-- Balanced-tensor restriction as a 1-morphism. -/
def cyclotomicActionRestriction :
    cyclotomicActionObject D Sc a ha (n + 1) ⟶ cyclotomicActionObject D Sc a ha n :=
  ⟨cyclotomicSuperRestriction D Sc i a ha n⟩


end OddMath.QuiverHecke
end

end

section

/-!
# The repeated-outside-colour cyclotomic braid correction

Ports the algebraic `braidQ` input of
`Categorification/KLR/CyclotomicAction/Square.lean`. The super divided-difference
polynomial retains its coefficient `(-1)^(|i|(|j|+s))`, including odd outside
colours. The equality is in the actual cyclotomic algebra; it does not yet
transport the three crossings through triple-superinduction associators.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit super divided-difference correction on an old-word corner. -/
def tripleBraidCorrection (i j : I) {n : ℕ} (w : Word I n) :
    End (wordObj D Sc (tripleWord i j i w)) :=
  ∑ s ∈ Finset.range (D.dn i j),
    (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
      (dotE D Sc (tripleWord i j i w).1 w.1.length ^ (D.dn i j - 1 - s) *
        dotE D Sc (tripleWord i j i w).1 (w.1.length + 2) ^ s) +
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
      ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (dotE D Sc (tripleWord i j i w).1 w.1.length ^ (p - 1 - s) *
            dotE D Sc (tripleWord i j i w).1 (w.1.length + 1) ^ q *
            dotE D Sc (tripleWord i j i w).1 (w.1.length + 2) ^ s)

/-- The full signed repeated-colour relation on each three-strand corner. -/
theorem tripleCross_braid_correction (i j : I) (hij : i ≠ j) {n : ℕ} (w : Word I n) :
    (tripleCrossLeft D Sc i j i w ≫ tripleCrossRight D Sc j i i w ≫
        tripleCrossLeft D Sc j i i w) -
      (tripleCrossRight D Sc i j i w ≫ tripleCrossLeft D Sc i i j w ≫
        tripleCrossRight D Sc i i j w) = tripleBraidCorrection D Sc i j w := by
  dsimp only [tripleCrossLeft, tripleCrossRight]
  rw [cl_comp, cl_comp, cl_comp, cl_comp]
  exact braid_iji D Sc w.1 [] hij _ _

variable [Fintype I]

/-- The correction as a diagonal family in the actual finite-matrix algebra. -/
def affineTripleBraidCorrection (i j : I) (n : ℕ) : Hn D Sc (n + 3) :=
  tripleMatrix D Sc i j i i j i (tripleBraidCorrection D Sc i j)

end OddMath.QuiverHecke
end

end

section

/-!
# Signed right operators for the three-strand braid

Ports the signed-operator input corresponding to
`Categorification/KLR/CyclotomicAction/Braid.lean`. The three crossing matrices
have their actual homogeneous degrees. On a graded regular module, reversing
three homogeneous right multipliers introduces a sign symmetric in their
three degrees. Thus the uncorrected braid remains valid as an equality of
signed operators. Identification with triple-superinduction remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- First-pair crossing parity on the actual triple-word corner. -/
theorem tripleCrossLeft_parity (i j c : I) {n : ℕ} (w : Word I n) :
    tripleCrossLeft D Sc i j c w ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  unfold tripleCrossLeft cl
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, tripleWord, pl, PG.ld, Shape.parity]

/-- Last-pair crossing parity on the actual triple-word corner. -/
theorem tripleCrossRight_parity (i j c : I) {n : ℕ} (w : Word I n) :
    tripleCrossRight D Sc i j c w ∈ parity (R := k) _ _ (D.parity j * D.parity c) := by
  unfold tripleCrossRight cl
  apply Presentation.diag_mem_homDeg'
  have hle : w.1.length ≤ n + 1 := by omega
  simp [degree_parity_mkD, tripleWord, pl, PG.ld, Shape.parity, List.take_append,
    List.drop_append, List.take_of_length_le hle, List.drop_eq_nil_of_le hle]

variable [Fintype I]

section Regular
variable {A : Type u} [Ring A] [Algebra k A]
  (G : ZMod 2 → Submodule k A) [GradedAlgebra G]

end Regular

end OddMath.QuiverHecke
end

end
