import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals
import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules.ProbeDotPropagation
import OddMath.SKM.BWWPureNilpotent

/-!
# Probe mixed

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Literal crossings of distinct probe words

These are the actual affine morphisms between the two word objects, together
with their signed dot slides and quadratic formula. They precede the source
and target corner comparison; no invertibility assumption is used here.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

def probeMixedWord (pre post : List I) (i j : I) :
    Word I ((pre.length+post.length+1)+1) :=
  ⟨pre ++ [i,j] ++ post, by simp; omega⟩

theorem probeMixedChain (pre post : List I) (i j : I) :
    SChain (pre ++ [i,j] ++ post)
      (pl (pre ++ [i,j] ++ post) [.cross pre.length]) (pre ++ [j,i] ++ post) :=
  sChain_ofShape' pre post (.cross i j) rfl rfl rfl

def probeMixedCross (pre post : List I) (i j : I) :
    (pres D Sc).obj (ob D (pre ++ [i,j] ++ post)) ⟶
      (pres D Sc).obj (ob D (pre ++ [j,i] ++ post)) :=
  cl D Sc _ _ [.cross pre.length] (probeMixedChain pre post i j)

theorem probeMixedCross_slide (pre post : List I) (i j : I) (hij : i ≠ j) :
    probeMixedCross D Sc pre post i j ≫
      dotE D Sc (pre ++ [j,i] ++ post) pre.length =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ≫
          probeMixedCross D Sc pre post i j) := by
  change cl D Sc _ _ [.cross pre.length] _ ≫ dotE D Sc _ _ = _
  rw [dotE_eq, dotE_eq]
  simp only [probeMixedCross, cl_comp']
  exact slide_right_ne D Sc pre post i j hij _ _

/-- The reverse crossing supplies the second slide required by the direct
rectangular unit proof, with exactly the same sign. -/
theorem probeMixedCross_slide_reverse (pre post : List I) (i j : I) (hij : i ≠ j) :
    dotE D Sc (pre ++ [j,i] ++ post) pre.length ≫
      probeMixedCross D Sc pre post j i =
      SKM.zsign k (D.parity i * D.parity j) •
        (probeMixedCross D Sc pre post j i ≫
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) := by
  change dotE D Sc _ _ ≫ cl D Sc _ _ [.cross pre.length] _ = _
  rw [dotE_eq, dotE_eq]
  simp only [probeMixedCross, cl_comp']
  simpa only [List.cons_append, List.nil_append, mul_comm] using slide_left_ne D Sc pre post j i hij.symm
    (sChain_comp (sChain_pl _ [.dot pre.length]) (probeMixedChain pre post j i))
    (sChain_comp (probeMixedChain pre post j i)
      (sChain_pl _ [.dot (pre.length+1)]))

theorem probeMixedCross_quadratic_zero (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j = 0) :
    probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i =
      (Sc.t i j : k) • 𝟙 _ := by
  simp only [probeMixedCross, cl_comp']
  exact cross_cross_ne_zero D Sc pre post hij hd _

theorem probeMixedCross_quadratic (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i =
      (∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ p *
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ^ q)) +
      ((Sc.t i j : k) • dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ^ D.dn j i) := by
  simp only [probeMixedCross, cl_comp']
  exact cross_cross_ne D Sc pre post hij hd _

/-- The two literal dots obey the prescribed supercommutation sign. -/
theorem probeMixedDots_slide (pre post : List I) (i j : I) :
    dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) *
      dotE D Sc (pre ++ [i,j] ++ post) pre.length =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc (pre ++ [i,j] ++ post) pre.length *
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) := by
  have h := genE_interchange D Sc pre [] post (.dot i) (.dot j) rfl rfl
    (w := pre ++ [i,j] ++ post) (by simp [Shape.dom, List.append_assoc])
    (p := pre.length) (q := pre.length+1) rfl (by simp [Shape.dom])
  simpa only [Shape.parity, PG.ofShape] using h

end OddMath.QuiverHecke
end

end

section

/-! # Actual old append and dot under scalar probe specialization
These formulas compare the existing canonical old append and appended dot
with their literal ordinary probe images. The dot image is a unit in its
actual word corner at every height, including append from the vacuum.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

omit [Fintype I] in
/-- Unit-coefficient affine arrows specialize to themselves. -/
theorem elvProbeScalarHom_affineUnit {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    elvProbeScalarHom D m Sc v w (ELV.affineUnit D Sc cut v w f) = f := by
  change (elvAffineScalarSpecialization D Sc cut (probeScalarValues D m)
      (probeScalarValues_vanish D m)).map
    (BoxProd.tmulHom (X := ELV.obj D Sc cut v) (Y := ELV.obj D Sc cut w)
      (SuperalgebraCat.ofElem 1) f) = f
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem, map_one, one_smul]

end OddMath.QuiverHecke
end

end
