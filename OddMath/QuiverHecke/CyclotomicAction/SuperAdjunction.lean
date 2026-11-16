import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import StringDiagrams.Super.Functor
import OddMath.SKM.Grading
import OddMath.QuiverHecke.CyclotomicAction.SignedIntertwiner
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.SKM.RouquierData
import StringDiagrams.Super.SCat
import StringDiagrams.Super.TwoSCat

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
# The homogeneous crossing between composition corners

Ports the crossing construction of
`Categorification/KLR/CyclotomicAction/Induction.lean`, the intertwiner method of
`Categorification/KLR/CyclotomicAction/Slides.lean` and the corner comparison of
`Categorification/KLR/CyclotomicAction/Comparison.lean`.
The map from `compositionCorner i j` to `compositionCorner j i` is
`x ↦ (-1)^{|i||j||x|} x τᵢⱼ`. Here `τᵢⱼ` is the diagram from the word
ending in `[i,j]` to the word ending in `[j,i]`; right multiplication reverses
this direction on the left ideals. The sign gives signed left linearity and
ordinary right linearity in the superbimodule convention. No inverse is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "GC" => cyclotomicParity D Sc a ha (n + 1 + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "c" => cyclotomicLastCrossing D Sc i j a n
local notation "d" => D.parity i * D.parity j

private theorem crossing_mul_mem (x : CyclotomicAlgebra D Sc a (n + 1 + 1))
    (_hx : x ∈ compositionCornerSubmodule D Sc i j a n) :
    x * c ∈ compositionCornerSubmodule D Sc j i a n := by
  change (x * c) * cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n 1) = x * c
  rw [mul_assoc, (cyclotomicLastCrossing_corner D Sc i j a n).2]

/-- Parity sign followed by right multiplication by the concrete crossing. -/
def compositionCrossingLinear : (P).toSVec ⟶ (Q).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract c) (crossing_mul_mem D Sc i j a n)

/-- The crossing map has parity `|i||j|`. -/
theorem compositionCrossingLinear_parity :
    compositionCrossingLinear D Sc i j a ha n ∈ SVec.parityHom (P).toSVec (Q).toSVec d := by
  change compositionCrossingLinear D Sc i j a ha n ∈ parity (R := k) (P).toSVec (Q).toSVec d
  unfold compositionCrossingLinear
  have hd := SVec.restrictHom_mem (hU := compositionCorner_odd_mem D Sc i j a ha n)
    (hU' := compositionCorner_odd_mem D Sc j i a ha n)
    ((SuperBimodule.regular GC).ract_mem d c
      (cyclotomicLastCrossing_parity D Sc i j a ha n)) (crossing_mul_mem D Sc i j a n)
  simpa only [compositionCorner, compositionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem crossing_sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- The two action laws follow from the proved signed crossing intertwiner. -/
theorem compositionCrossingLinear_isHom :
    SuperBimodule.IsHom P Q (compositionCrossingLinear D Sc i j a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (compositionCrossingLinear_parity D Sc i j a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := crossing_sgn_action D Sc i j a ha n ((P).lact_mem p b hb) x
    apply Subtype.ext
    change ((P).toSVec.sgn d ((P).lact b x)).val * c =
      sign k (p * d) • (b * (((P).toSVec.sgn d x).val * c))
    rw [h]
    change (sign k (p * d) • (b * ((P).toSVec.sgn d x).val)) * c = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := crossing_sgn_action D Sc i j a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) *
          cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n r)
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc j a n r))) * c = _
      rw [smul_mul_assoc, mul_assoc, cyclotomicLastCrossing_intertwines D Sc i j a ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous superbimodule map between the two composition corners. -/
def compositionSuperCrossing : P ⟶ Q :=
  ⟨compositionCrossingLinear D Sc i j a ha n, compositionCrossingLinear_isHom D Sc i j a ha n⟩

theorem compositionSuperCrossing_parity :
    compositionSuperCrossing D Sc i j a ha n ∈ parity (R := k) P Q d :=
  SuperBimodule.mem_parity_iff.2 (compositionCrossingLinear_parity D Sc i j a ha n)

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
local notation "P" => compositionCorner D Sc i i a ha n
local notation "f" => compositionSuperCrossing D Sc i i a ha n

end OddMath.QuiverHecke
end

end

section

/-!
# The crossing on composed cyclotomic superinduction

Ports the crossing of `Categorification/KLR/CyclotomicAction/Induction.lean`
through the even comparison of `CyclotomicAction/Comparison.lean`.
The transformation below is obtained from `compositionSuperCrossing`, not from
an assumed crossing operator. Only its parity and supernatural naturality are
asserted; no square, braid, inversion or KKO relations are asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "F" => cyclotomicSuperInduction D Sc j a ha n ⋙
  cyclotomicSuperInduction D Sc i a ha (n + 1)
local notation "G" => cyclotomicSuperInduction D Sc i a ha n ⋙
  cyclotomicSuperInduction D Sc j a ha (n + 1)
local notation "d" => D.parity i * D.parity j
local notation "e" => inductionFunctorComparison D Sc i j a ha n
local notation "e'" => inductionFunctorComparison D Sc j i a ha n

/-- Transport the corner crossing along the two even comparison isomorphisms. -/
def inductionCrossingApp (M : CyclotomicSupermodules D Sc a ha n) : (F).obj M ⟶ (G).obj M :=
  (e).hom.app M ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫ (e').inv.app M

/-- The transported crossing has parity `|i||j|`. -/
theorem inductionCrossingApp_mem (M : CyclotomicSupermodules D Sc a ha n) :
    inductionCrossingApp D Sc i j a ha n M ∈ parity (R := k) _ _ d := by
  change ((inductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
    whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
      (inductionFunctorComparisonApp D Sc j i a ha n M).inv) ∈
        parity (R := k) ((F).obj M) ((G).obj M) d
  simpa only [zero_add, add_zero] using comp_mem
    (inductionFunctorComparisonApp_hom_mem D Sc i j a ha n M)
    (comp_mem (whiskerRight_mem P (compositionSuperCrossing_parity D Sc i j a ha n) M)
      (inductionFunctorComparisonApp_inv_mem D Sc j i a ha n M))

/-- The comparison introduces no additional naturality sign. -/
theorem inductionCrossingApp_naturality
    {M N : CyclotomicSupermodules D Sc a ha n} {q : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N q) :
    (F).map f ≫ inductionCrossingApp D Sc i j a ha n N =
      koszulSign d q • (inductionCrossingApp D Sc i j a ha n M ≫ (G).map f) := by
  have hcross : whiskerLeft P f ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) N =
      koszulSign d q • (whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
        whiskerLeft Q f) := by
    rw [super_interchange P f (compositionSuperCrossing_parity D Sc i j a ha n) hf,
      koszulSign_smul_smul]
  have he := (e).hom.naturality f
  have he' := (e').inv.naturality f
  change (F).map f ≫ (e).hom.app N = (e).hom.app M ≫ whiskerLeft P f at he
  change whiskerLeft Q f ≫ (e').inv.app N = (e').inv.app M ≫ (G).map f at he'
  unfold inductionCrossingApp
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (whiskerLeft P f),
    hcross, Linear.smul_comp, Linear.comp_smul, Category.assoc, he']
  simp only [Category.assoc]

/-- The homogeneous supernatural crossing between the composed induction superfunctors. -/
def cyclotomicSuperInductionCrossing : SuperNatTrans k F G where
  app p M := if p = d then inductionCrossingApp D Sc i j a ha n M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact inductionCrossingApp_mem D Sc i j a ha n M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    split_ifs with h
    · subst p
      exact inductionCrossingApp_naturality D Sc i j a ha n f hf
    · simp

/-- The component of parity `|i||j|` is precisely the transported corner crossing. -/
@[simp] theorem cyclotomicSuperInductionCrossing_app
    (M : CyclotomicSupermodules D Sc a ha n) :
    (cyclotomicSuperInductionCrossing D Sc i j a ha n).app d M =
      (e).hom.app M ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
        (e').inv.app M := by
  simp [cyclotomicSuperInductionCrossing, inductionCrossingApp]

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
# The unit of cyclotomic super induction and restriction

Ports the unit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` using genuine balanced
super tensor products. Both inserted colour idempotents are even.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
local notation "ep" => inductionCornerIdempotent D Sc i a ha n
local notation "eq" => restrictionCornerOf D Sc i a ha n 1

/-- The two even colour idempotents give the linear unit. -/
def superUnitLinear (M : CyclotomicSupermodules D Sc a ha n) :
    M.toSVec →ₗ[k] (tensor Q (tensor P M)).toSVec where
  toFun m := btmul Q (tensor P M) eq (btmul P M ep m)
  map_add' x y := by rw [btmul_add_right, btmul_add_right]
  map_smul' c x := by rw [btmul_smul_right, btmul_smul_right]; rfl

@[simp] theorem superUnitLinear_apply (M : CyclotomicSupermodules D Sc a ha n) (m : M.toSVec) :
    superUnitLinear D Sc i a ha n M m = btmul Q (tensor P M) eq (btmul P M ep m) := rfl

theorem restrictionCornerOf_one_mem : eq ∈ (Q).toSVec.part 0 :=
  (restrictionCorner_mem_part_iff D Sc i a ha n).mpr
    (cyclotomicAppend_parity D Sc i a ha n (SetLike.one_mem_graded _))

theorem superUnitLinear_mem (M : CyclotomicSupermodules D Sc a ha n) :
    SVec.ofHom (superUnitLinear D Sc i a ha n M) ∈
      SVec.parityHom M.toSVec (tensor Q (tensor P M)).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p m hm
  change btmul Q (tensor P M) eq (btmul P M ep m) ∈
    (tensor Q (tensor P M)).toSVec.part (p + 0)
  simpa only [zero_add, add_zero] using
    btmul_mem_part Q (tensor P M) (restrictionCornerOf_one_mem D Sc i a ha n)
      (btmul_mem_part P M (inductionCornerIdempotent_mem D Sc i a ha n) hm)

theorem superUnitLinear_lact (M : CyclotomicSupermodules D Sc a ha n) (r : A) (m : M.toSVec) :
    superUnitLinear D Sc i a ha n M (M.lact r m) =
      (tensor Q (tensor P M)).lact r (superUnitLinear D Sc i a ha n M m) := by
  rw [superUnitLinear_apply, superUnitLinear_apply, lact_btmul, ← btmul_ract_lact]
  have he : (P).ract r ep = (P).lact (φ r) ep := by
    apply Subtype.ext
    change φ 1 * φ r = φ r * φ 1
    rw [← map_mul, ← map_mul, one_mul, mul_one]
  rw [he, ← lact_btmul, ← btmul_ract_lact]
  congr 1
  apply Subtype.ext
  change φ 1 * φ r = φ r * φ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

/-- The even component of the induction-restriction unit. -/
def superUnitComponent (M : CyclotomicSupermodules D Sc a ha n) : M ⟶ tensor Q (tensor P M) :=
  ⟨SVec.ofHom (superUnitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (superUnitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p r _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro m
      exact superUnitLinear_lact D Sc i a ha n M r m
    · intro c
      apply SVec.hom_ext
      intro m
      rfl⟩

/-- Naturality includes homogeneous odd module maps. -/
theorem superUnitComponent_naturality_of_mem
    {M N : CyclotomicSupermodules D Sc a ha n} {p : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N p) :
    f ≫ superUnitComponent D Sc i a ha n N =
      superUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f) := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro m
  change superUnitLinear D Sc i a ha n N (f.1 m) =
    (whiskerLeft Q (whiskerLeft P f)).1 (superUnitLinear D Sc i a ha n M m)
  rw [superUnitLinear_apply, superUnitLinear_apply,
    whiskerLeft_btmul Q _ (whiskerLeft_mem P f hf) (restrictionCornerOf_one_mem D Sc i a ha n),
    whiskerLeft_btmul P f hf (inductionCornerIdempotent_mem D Sc i a ha n)]
  simp only [zero_mul, Supercategory.sign_zero, one_smul]

/-- The actual even unit as a natural transformation between superfunctors. -/
def cyclotomicSuperUnit : 𝟭 (CyclotomicSupermodules D Sc a ha n) ⟶
    cyclotomicSuperInduction D Sc i a ha n ⋙ cyclotomicSuperRestriction D Sc i a ha n where
  app M := superUnitComponent D Sc i a ha n M
  naturality {M N} f := by
    change f ≫ superUnitComponent D Sc i a ha n N =
      superUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f)
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact superUnitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end OddMath.QuiverHecke
end

end

section

/-!
# The counit of cyclotomic super induction and restriction

Ports the counit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean`. Evaluation is the
actual action `(x ⊗ (y ⊗ m)) ↦ (xy)m` on the balanced super tensor products.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
variable (M : CyclotomicSupermodules D Sc a ha (n + 1))

/-- The inner bilinear action of a fixed induction element. -/
def superCounitInnerBi (x : (P).toSVec) :
    (Q).toSVec →ₗ[k] M.toSVec →ₗ[k] M.toSVec :=
  M.lact.comp (cornerPairingBi D Sc i a ha n x)

theorem superCounitInner_balance (x : (P).toSVec) (y : (Q).toSVec) (b : B) (m : M.toSVec) :
    superCounitInnerBi D Sc i a ha n M x ((Q).ract b y) m =
      superCounitInnerBi D Sc i a ha n M x y (M.lact b m) := by
  change M.lact (x.1 * (y.1 * b)) m = M.lact (x.1 * y.1) (M.lact b m)
  rw [← mul_assoc, M.lact_mul]
  rfl

/-- Balanced evaluation in the inner tensor factor. -/
def superCounitInner (x : (P).toSVec) : (tensor Q M).toSVec →ₗ[k] M.toSVec :=
  tensorLift (superCounitInnerBi D Sc i a ha n M x) (superCounitInner_balance D Sc i a ha n M x)

@[simp] theorem superCounitInner_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    superCounitInner D Sc i a ha n M x (btmul Q M y m) = M.lact (x.1 * y.1) m :=
  tensorLift_btmul _ _ y m

/-- The bilinear outer evaluation. -/
def superCounitBi : (P).toSVec →ₗ[k] (tensor Q M).toSVec →ₗ[k] M.toSVec where
  toFun := superCounitInner D Sc i a ha n M
  map_add' x y := by
    apply tensor_hom_ext Q M
    intro z m
    change M.lact ((x.1 + y.1) * z.1) m = M.lact (x.1 * z.1) m + M.lact (y.1 * z.1) m
    rw [add_mul, map_add]
    rfl
  map_smul' c x := by
    apply tensor_hom_ext Q M
    intro y m
    change M.lact ((c • x.1) * y.1) m = c • M.lact (x.1 * y.1) m
    rw [smul_mul_assoc, map_smul]
    rfl

theorem superCounit_balance (x : (P).toSVec) (r : A) (z : (tensor Q M).toSVec) :
    superCounitBi D Sc i a ha n M ((P).ract r x) z =
      superCounitBi D Sc i a ha n M x ((tensor Q M).lact r z) := by
  refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
    superCounitBi D Sc i a ha n M ((P).ract r x) z =
      superCounitBi D Sc i a ha n M x ((tensor Q M).lact r z)) z ?_ ?_ ?_
  · simp only [map_zero]
  · intro y m
    change superCounitInner D Sc i a ha n M ((P).ract r x) (btmul Q M y m) =
      superCounitInner D Sc i a ha n M x ((tensor Q M).lact r (btmul Q M y m))
    rw [lact_btmul, superCounitInner_btmul, superCounitInner_btmul]
    change M.lact ((x.1 * φ r) * y.1) m = M.lact (x.1 * (φ r * y.1)) m
    rw [mul_assoc]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The actual linear counit on the doubly balanced tensor. -/
def superCounitLinear : (tensor P (tensor Q M)).toSVec →ₗ[k] M.toSVec :=
  tensorLift (superCounitBi D Sc i a ha n M) (superCounit_balance D Sc i a ha n M)

@[simp] theorem superCounitLinear_btmul (x : (P).toSVec) (z : (tensor Q M).toSVec) :
    superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z) =
      superCounitInner D Sc i a ha n M x z := tensorLift_btmul _ _ x z

@[simp] theorem superCounitLinear_btmul_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x (btmul Q M y m)) =
      M.lact (x.1 * y.1) m := by rw [superCounitLinear_btmul, superCounitInner_btmul]

theorem superCounitInner_mem {p : ZMod 2} {x : (P).toSVec} (hx : x ∈ (P).toSVec.part p) :
    SVec.ofHom (superCounitInner D Sc i a ha n M x) ∈
      SVec.parityHom (tensor Q M).toSVec M.toSVec p := by
  apply tensor_mem_parity_of_btmul
  intro q r y m hy hm
  change M.lact (x.1 * y.1) m ∈ M.toSVec.part (q + r + p)
  have hxy := SetLike.GradedMul.mul_mem
    ((inductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    ((restrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  simpa only [add_comm, add_left_comm, add_assoc] using
    SVec.apply_mem_part (M.lact_mem (p + q) (x.1 * y.1) hxy) hm

theorem superCounitLinear_mem :
    SVec.ofHom (superCounitLinear D Sc i a ha n M) ∈
      SVec.parityHom (tensor P (tensor Q M)).toSVec M.toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x z hx hz
  change (SVec.ofHom (superCounitInner D Sc i a ha n M x)) z ∈ M.toSVec.part (p + q + 0)
  simpa only [add_zero, add_comm] using
    SVec.apply_mem_part (superCounitInner_mem D Sc i a ha n M hx) hz

theorem superCounitLinear_lact (b : B) (t : (tensor P (tensor Q M)).toSVec) :
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (superCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (superCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b (btmul P (tensor Q M) x z)) =
        M.lact b (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [lact_btmul, superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
      change M.lact ((b * x.1) * y.1) m = M.lact b (M.lact (x.1 * y.1) m)
      rw [mul_assoc, M.lact_mul]
      rfl
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

theorem superCounitLinear_ract (c : k) (t : (tensor P (tensor Q M)).toSVec) :
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (superCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (superCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c (btmul P (tensor Q M) x z)) =
        M.ract c (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [ract_btmul, ract_btmul, superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
      exact (congrArg (fun f : M.toSVec ⟶ M.toSVec => f m) (M.lact_ract (x.1 * y.1) c)).symm
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The even component of the restriction-induction counit. -/
def superCounitComponent : tensor P (tensor Q M) ⟶ M :=
  ⟨SVec.ofHom (superCounitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (superCounitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p b _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro t
      exact superCounitLinear_lact D Sc i a ha n M b t
    · intro c
      apply SVec.hom_ext
      intro t
      exact superCounitLinear_ract D Sc i a ha n M c t⟩

/-- Signed naturality of evaluation for a homogeneous module map. -/
theorem superCounitComponent_naturality_of_mem
    {M N : CyclotomicSupermodules D Sc a ha (n + 1)} {s : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N s) :
    whiskerLeft P (whiskerLeft Q f) ≫ superCounitComponent D Sc i a ha n N =
      superCounitComponent D Sc i a ha n M ≫ f := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext_homogeneous P (tensor Q M)
  intro p _ x z hx _
  change superCounitLinear D Sc i a ha n N
    ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
      f.1 (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))
  refine tensor_induction_on_homogeneous (M := Q) (N := M) («P» := fun z =>
    superCounitLinear D Sc i a ha n N
      ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
        f.1 (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
  · simp only [btmul_zero_right, map_zero]
  · intro q r y m hy _
    rw [whiskerLeft_btmul P _ (whiskerLeft_mem Q f hf) hx,
      whiskerLeft_btmul Q f hf hy, btmul_smul_right, map_smul, map_smul,
      superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
    have hxy := SetLike.GradedMul.mul_mem
      ((inductionCorner_mem_part_iff D Sc i a ha n).mp hx)
      ((restrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
    have h := congrArg (fun g : M.toSVec ⟶ N.toSVec => g m)
      (((isHom_iff_of_mem (mem_parity_iff.mp hf)).mp f.2).1 (p + q) (x.1 * y.1) hxy)
    change f.1 (M.lact (x.1 * y.1) m) =
      Supercategory.sign k ((p + q) * s) • N.lact (x.1 * y.1) (f.1 m) at h
    rw [h, smul_smul, ← Supercategory.sign_add, ← add_mul]
  · intro z w hz hw
    simp only [btmul_add_right, map_add, hz, hw]

/-- The actual even counit as a natural transformation between superfunctors. -/
def cyclotomicSuperCounit :
    cyclotomicSuperRestriction D Sc i a ha n ⋙ cyclotomicSuperInduction D Sc i a ha n ⟶
      𝟭 (CyclotomicSupermodules D Sc a ha (n + 1)) where
  app M := superCounitComponent D Sc i a ha n M
  naturality {M N} f := by
    change whiskerLeft P (whiskerLeft Q f) ≫ superCounitComponent D Sc i a ha n N =
      superCounitComponent D Sc i a ha n M ≫ f
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact superCounitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

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
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
local notation "F" => cyclotomicSuperInduction D Sc i a ha n
local notation "E" => cyclotomicSuperRestriction D Sc i a ha n

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

local notation "F" => cyclotomicActionInduction D Sc a ha n i
local notation "E" => cyclotomicActionRestriction D Sc a ha n i

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
