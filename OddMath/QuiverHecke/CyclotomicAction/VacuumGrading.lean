import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.SKM.BubbleELVGrading
import OddMath.SKM.BubbleELVPolynomialGrading
import OddMath.QuiverHecke.Grading
import OddMath.QuiverHecke.CyclotomicAction.CoefficientTransport
import StringDiagrams.Super.BoxProductGraded
import OddMath.QuiverHecke.CyclotomicAbsentColour

/-!
# Vacuum grading

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Vacuum strand inclusion

The height-zero boundary of cyclotomic induction uses `Hn D Sc 0` as its
source and the height-one cyclotomic quotient as its target. It is the
composite of affine strand inclusion and the quotient map, with no new
quotient presentation. The image of one is the single-colour idempotent.
-/

noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The empty boundary word. -/
def vacuumWord : Word I 0 := ⟨[], rfl⟩

/-- Add the first strand, then impose the first-dot cyclotomic relation. -/
def vacuumAppend (i : I) (a : I → _root_.Polynomial k) :
    Hn D Sc 0 →ₙₐ[k] CyclotomicAlgebra D Sc a 0 where
  toFun x := cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 x)
  map_zero' := by simp
  map_add' := by intros; simp
  map_smul' := by intros; simp
  map_mul' := by intros; simp

@[simp] theorem vacuumAppend_apply (i : I) (a : I → _root_.Polynomial k)
    (x : Hn D Sc 0) :
    vacuumAppend D Sc i a x = cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 x) := rfl

/-- The first-strand colour cut in the cyclotomic quotient. -/
def vacuumColourCut (i : I) (a : I → _root_.Polynomial k) :
    CyclotomicAlgebra D Sc a 0 :=
  cyclotomicMk D Sc a 0 (Hn.wordIdempotent (appendWord i (vacuumWord (I := I))))

private theorem vacuum_one : (1 : Hn D Sc 0) =
    Hn.wordIdempotent (vacuumWord (I := I)) := by
  have h : (Finset.univ : Finset (Word I 0)) = {vacuumWord} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp w.2
  change FiniteHomMatrix.localUnit Finset.univ = _
  rw [h]
  simp [FiniteHomMatrix.localUnit, Hn.wordIdempotent]

@[simp] theorem vacuumAppend_one (i : I) (a : I → _root_.Polynomial k) :
    vacuumAppend D Sc i a 1 = vacuumColourCut D Sc i a := by
  rw [vacuumAppend_apply, vacuum_one]
  congr 1
  change appendLinear D Sc i 0 (FiniteHomMatrix.single _ _ (𝟙 _)) = _
  rw [appendLinear_single]
  congr 1
  exact MonoidalSupercategory.id_whiskerRight (R := k)
    (wordObj D Sc (vacuumWord (I := I))) ((pres D Sc).obj (ob D [i]))

/-- Scalars act on the chosen colour cut, not necessarily on the whole unit. -/
@[simp] theorem vacuumAppend_scalar (i : I) (a : I → _root_.Polynomial k) (c : k) :
    vacuumAppend D Sc i a (algebraMap k (Hn D Sc 0) c) =
      c • vacuumColourCut D Sc i a := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, vacuumAppend_one]

@[simp] theorem vacuumColourCut_sq (i : I) (a : I → _root_.Polynomial k) :
    vacuumColourCut D Sc i a * vacuumColourCut D Sc i a = vacuumColourCut D Sc i a := by
  rw [← vacuumAppend_one, ← map_mul, one_mul]

@[simp] theorem vacuumColourCut_mul_append (i : I) (a : I → _root_.Polynomial k)
    (x : Hn D Sc 0) :
    vacuumColourCut D Sc i a * vacuumAppend D Sc i a x = vacuumAppend D Sc i a x := by
  rw [← vacuumAppend_one, ← map_mul, one_mul]

@[simp] theorem vacuumAppend_mul_colourCut (i : I) (a : I → _root_.Polynomial k)
    (x : Hn D Sc 0) :
    vacuumAppend D Sc i a x * vacuumColourCut D Sc i a = vacuumAppend D Sc i a x := by
  rw [← vacuumAppend_one, ← map_mul, mul_one]

/-- Vacuum strand inclusion is even for homogeneous cyclotomic parameters. -/
theorem vacuumAppend_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) {p : ZMod 2} {x : Hn D Sc 0}
    (hx : x ∈ affineParity D Sc 0 p) :
    vacuumAppend D Sc i a x ∈ cyclotomicParity D Sc a ha 0 p :=
  cyclotomicMk_parity D Sc a ha 0 (appendAlgebra_parity D Sc i 0 hx)

end OddMath.QuiverHecke
end

end

section

/-! # Integer grading of the ELV coefficient diagram category

The full coefficient quotient retains exterior parity independently of integer
 degree. The affine relations use `Sc.Homogeneous`. The first-position
cyclotomic relations have their prescribed symmetrizer degree. This supplies
Hom gradings for the coefficient action in `DeformedGradedAction.md`; it does
not assert bounded support at positive strand content.
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous) (cutoff : I → ℕ)

/-- Integer grading on the coefficient one-object category, with its existing parity. -/
@[instance_reducible]
def elvCoefficientCategoryGrading : GradedSupercategory k
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff)) :=
  SuperalgebraCat.instGradedSupercategory (SKM.SYM.elvCoefficientGSuperAlg D sy cutoff).gsa

/-- The full coefficient diagram category has the tensor-sum integer grading. -/
@[instance_reducible]
def elvHomGrading : GradedSupercategory k (ELVCoefficientCategory D Sc cutoff) := by
  letI := elvCoefficientCategoryGrading (k := k) D sy cutoff
  letI := gradedSupercategory D sy Sc hc
  exact BoxProd.instGradedSupercategory

/-- The integer homogeneous parts of the existing coefficient quotient Homs. -/
abbrev elvHomDegree (v w : List I) (n : ℤ) : Submodule k (ELV.hom D Sc cutoff v w) :=
  letI := elvHomGrading D sy Sc hc cutoff
  GradedSupercategory.degree (R := k) (ELV.obj D Sc cutoff v) (ELV.obj D Sc cutoff w) n

/-- These parts form a direct sum, not merely a filtration. -/
theorem elvHomDegree_internal (v w : List I) :
    DirectSum.IsInternal (elvHomDegree D sy Sc hc cutoff v w) :=
by
  let _ := elvHomGrading D sy Sc hc cutoff
  exact GradedSupercategory.isInternal_degree _ _

/-- A coefficient and an affine diagram contribute additively to integer degree. -/
theorem elvQuotientMap_source_mem_degree {v w : List I} {a : SKM.SYM D k}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)} {r s : ℤ}
    (ha : a ∈ SKM.SYM.coefficientDegreePart D k sy r)
    (hf : f ∈ homDegree D sy Sc v w s) :
    elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc a f) ∈
      elvHomDegree D sy Sc hc cutoff v w (r + s) := by
  rw [elvQuotientMap_source]
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  exact BoxProd.tmulHom_mem_degree (X := ELV.obj D Sc cutoff v)
    (Y := ELV.obj D Sc cutoff w) (Submodule.mem_map_of_mem ha) hf

/-- Dot powers on a nonempty word have their affine symmetrizer degree. -/
theorem firstDotPower_mem_gdeg (j : I) (v : List I) (n : ℕ) :
    firstDotPower D Sc (j :: v) n ∈ homDegree D sy Sc (j :: v) (j :: v)
      (2 * sy.d j * n) := by
  apply Presentation.diag_mem_homDeg'
  rw [degree_gdeg_mkD]
  simp only [List.map_replicate]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, pl_cons, PG.ld, PG.act, List.drop_zero,
      List.take_zero, List.singleton_append, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [gdeg, Nat.cast_add, Nat.cast_one]
    ring

/-- A coefficient polynomial with complementary coefficient degrees is homogeneous. -/
theorem deformedCyclotomic_mem_elvHomDegree (j : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k)
    (hcoeff : ∀ a, c a ∈ SKM.SYM.coefficientDegreePart D k sy
      (2 * sy.d j * ((N : ℤ) - a.val))) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (j :: v) N c) ∈
      elvHomDegree D sy Sc hc cutoff (j :: v) (j :: v) (2 * sy.d j * N) := by
  change elvQuotientMap D Sc cutoff _ _ _ ∈ _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Submodule.sum_mem
  intro a _
  have h := elvQuotientMap_source_mem_degree D sy Sc hc cutoff (hcoeff a)
    (firstDotPower_mem_gdeg D sy Sc j v a.val)
  have he : 2 * sy.d j * ((N : ℤ) - a.val) + 2 * sy.d j * a.val =
      2 * sy.d j * N := by ring
  rw [he] at h
  exact h

/-- Both parity cases of the first-position cyclotomic relation have degree
`2 d_j cutoff_j`, with the original exterior coefficients. -/
theorem ELV.relation_mem_degree (j : I) (v : List I) :
    ELV.relation D Sc cutoff j v ∈
      elvHomDegree D sy Sc hc cutoff (j :: v) (j :: v) (2 * sy.d j * cutoff j) := by
  unfold ELV.relation
  split_ifs with hj
  · exact deformedCyclotomic_mem_elvHomDegree D sy Sc hc cutoff j v (cutoff j) _
      (SKM.SYM.elvMonicCoefficient_mem_coefficientDegreePart D k sy ⟨j, hj⟩ (cutoff j))
  · have he : D.parity j = 0 := (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    exact deformedCyclotomic_mem_elvHomDegree D sy Sc hc cutoff j v (cutoff j) _
      (SKM.SYM.evenMonicCoefficient_mem_coefficientDegreePart D k sy j he (cutoff j))

end OddMath.QuiverHecke
end

end

section

/-! # Integer and super gradings of the old ELV quotient

Integer projections preserve the two-sided old cyclotomic ideal: decompose
both surrounding coefficient-category morphisms into homogeneous summands,
then use the homogeneity of the first-position relation. The quotient is
`ELV.Old` with its full exterior coefficients, not a replacement quotient.

The degree images form an internal direct sum under `Sc.Homogeneous`.
Total super parity descends independently and commutes with integer projection;
no invertibility of two is used. The existing signed `oldCompose` adds integer
degrees. No positive-content support bound or enlarged target action is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous) (cutoff : I → ℕ)

/-- Integer projection on the coefficient-category Homs. -/
abbrev homDproj {v w : List I} (n : ℤ) : hom D Sc cutoff v w →ₗ[k] hom D Sc cutoff v w :=
  letI := elvHomGrading D sy Sc hc cutoff
  dproj k n

/-- Integer projection preserves the two-sided old cyclotomic ideal. -/
theorem ideal_dproj_mem {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ ideal D Sc cutoff v w) (n : ℤ) :
    homDproj D sy Sc hc cutoff n f ∈ ideal D Sc cutoff v w := by
  let _ := elvHomGrading D sy Sc hc cutoff
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    change dproj k n (a ≫ relation D Sc cutoff j t ≫ b) ∈ _
    refine induction_on_degree (R := k) a (by simp) (fun r a ha => ?_)
      (fun a a' ha ha' => ?_)
    · refine induction_on_degree (R := k) b (by simp) (fun s b hb => ?_)
        (fun b b' hb hb' => ?_)
      · have hg := comp_mem_degree ha
          (comp_mem_degree (relation_mem_degree D sy Sc hc cutoff j t) hb)
        by_cases h : r + (2 * sy.d j * cutoff j + s) = n
        · rw [← h, dproj_of_mem hg]
          exact Submodule.subset_span ⟨j, t, a, b, rfl⟩
        · rw [dproj_of_mem_ne hg h]
          exact Submodule.zero_mem _
      · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
    · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'
  | zero => simpa only [map_zero] using (ideal D Sc cutoff v w).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The degree parts in the old quotient are images of the original Hom parts. -/
def oldDegree (v w : List I) (n : ℤ) : Submodule k (Old D Sc cutoff v w) :=
  (elvHomDegree D sy Sc hc cutoff v w n).map (ideal D Sc cutoff v w).mkQ

/-- Integer component projection on the old cyclotomic quotient. -/
def oldDproj (v w : List I) (n : ℤ) :
    Old D Sc cutoff v w →ₗ[k] Old D Sc cutoff v w :=
  (ideal D Sc cutoff v w).mapQ (ideal D Sc cutoff v w) (homDproj D sy Sc hc cutoff n)
    (fun _ hf => ideal_dproj_mem D sy Sc hc cutoff hf n)

@[simp] theorem oldDproj_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    oldDproj D sy Sc hc cutoff v w n ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ (homDproj D sy Sc hc cutoff n f) := rfl

theorem oldDproj_of_mem {v w : List I} {m : ℤ} {f : Old D Sc cutoff v w}
    (hf : f ∈ oldDegree D sy Sc hc cutoff v w m) (n : ℤ) :
    oldDproj D sy Sc hc cutoff v w n f = if m = n then f else 0 := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldDproj_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The original old quotient has an internal integer grading. -/
theorem oldDegree_internal (v w : List I) :
    DirectSum.IsInternal (oldDegree D sy Sc hc cutoff v w) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (oldDproj D sy Sc hc cutoff v w n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, oldDproj D sy Sc hc cutoff v w n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => oldDproj_of_mem D sy Sc hc cutoff (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · change (⨆ n, (elvHomDegree D sy Sc hc cutoff v w n).map
      (ideal D Sc cutoff v w).mkQ) = ⊤
    rw [← Submodule.map_iSup, (elvHomDegree_internal D sy Sc hc cutoff v w).submodule_iSup_eq_top]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- Super parity projections also preserve the ideal, without dividing by two. -/
theorem ideal_proj_mem {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ ideal D Sc cutoff v w) (p : ZMod 2) :
    Supercategory.proj k p f ∈ ideal D Sc cutoff v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    refine Supercategory.induction_on (R := k) a (by simp) (fun r a ha => ?_)
      (fun a a' ha ha' => ?_)
    · refine Supercategory.induction_on (R := k) b (by simp) (fun s b hb => ?_)
        (fun b b' hb hb' => ?_)
      · have hg := Supercategory.comp_mem ha
          (Supercategory.comp_mem (relation_mem_parity D Sc cutoff j t) hb)
        by_cases h : r + ((cutoff j : ZMod 2) * D.parity j + s) = p
        · rw [← h, Supercategory.proj_of_mem hg]
          exact Submodule.subset_span ⟨j, t, a, b, rfl⟩
        · rw [Supercategory.proj_of_mem_ne hg h]
          exact Submodule.zero_mem _
      · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
    · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'
  | zero => simpa only [map_zero] using (ideal D Sc cutoff v w).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- Super parity on the old quotient, distinct from integer degree modulo two. -/
def oldParity (v w : List I) (p : ZMod 2) : Submodule k (Old D Sc cutoff v w) :=
  (Supercategory.parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p).map
    (ideal D Sc cutoff v w).mkQ

/-- The descended total parity projection. -/
def oldProj (v w : List I) (p : ZMod 2) :
    Old D Sc cutoff v w →ₗ[k] Old D Sc cutoff v w :=
  (ideal D Sc cutoff v w).mapQ (ideal D Sc cutoff v w) (Supercategory.proj k p)
    (fun _ hf => ideal_proj_mem D Sc cutoff hf p)

@[simp] theorem oldProj_mk (v w : List I) (p : ZMod 2) (f : hom D Sc cutoff v w) :
    oldProj D Sc cutoff v w p ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ (Supercategory.proj k p f) := rfl

theorem oldProj_of_mem {v w : List I} {q : ZMod 2} {f : Old D Sc cutoff v w}
    (hf : f ∈ oldParity D Sc cutoff v w q) (p : ZMod 2) :
    oldProj D Sc cutoff v w p f = if q = p then f else 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldProj_mk]
  split_ifs with h
  · subst p
    rw [Supercategory.proj_of_mem ha]
  · rw [Supercategory.proj_of_mem_ne ha h, map_zero]

/-- The parity images form an internal direct sum over the same ground ring. -/
theorem oldParity_internal (v w : List I) :
    DirectSum.IsInternal (oldParity D Sc cutoff v w) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (oldProj D Sc cutoff v w n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, oldProj D Sc cutoff v w n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => oldProj_of_mem D Sc cutoff (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · change (⨆ p, (Supercategory.parity (R := k) (obj D Sc cutoff v)
      (obj D Sc cutoff w) p).map (ideal D Sc cutoff v w).mkQ) = ⊤
    let _ := Supercategory.decomposition k (obj D Sc cutoff v) (obj D Sc cutoff w)
    rw [← Submodule.map_iSup,
      (DirectSum.Decomposition.isInternal (Supercategory.parity (R := k)
        (obj D Sc cutoff v) (obj D Sc cutoff w))).submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- Parity projection preserves each integer component in the old quotient. -/
theorem oldProj_mem_oldDegree (p : ZMod 2) {v w : List I} {n : ℤ}
    {f : Old D Sc cutoff v w} (hf : f ∈ oldDegree D sy Sc hc cutoff v w n) :
    oldProj D Sc cutoff v w p f ∈ oldDegree D sy Sc hc cutoff v w n := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  exact Submodule.mem_map_of_mem (proj_mem_degree p ha)

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Full-coefficient one-strand old ELV spanning

The one-strand affine dot basis and the actual monic old relation give spanning
by dot powers strictly below the cutoff, with coefficients in the full ELV
coefficient algebra. This is not an upper-support assertion for that algebra.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Coefficients of the actual old relation, with its normalized left order. -/
def singleCoefficient (i : I) (j : Fin (cutoff i + 1)) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff
    (if h : D.parity i = 1 then SKM.SYM.elvMonicCoefficient D k ⟨i, h⟩ (cutoff i) j
     else SKM.SYM.evenMonicCoefficient D k i (cutoff i) j)

@[simp] theorem singleCoefficient_top (i : I) :
    singleCoefficient (k := k) D cutoff i (Fin.last (cutoff i)) = 1 := by
  unfold singleCoefficient
  split_ifs <;> simp [Fin.last]

def singleTerm (i : I) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (n : ℕ) : hom D Sc cutoff [i] [i] := a ⊗ₜ[k] (dotE D Sc [i] 0 ^ n : End _)

/-- Actual coefficient times dot-power classes in the old quotient. -/
def singleClass (i : I) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (n : ℕ) : Old D Sc cutoff [i] [i] :=
  (ideal D Sc cutoff [i] [i]).mkQ (a ⊗ₜ[k] (dotE D Sc [i] 0 ^ n : End _))

theorem single_relation (i : I) :
    relation D Sc cutoff i [] = ∑ j : Fin (cutoff i + 1),
      singleTerm D Sc cutoff i (singleCoefficient D cutoff i j) j.val := by
  unfold relation singleCoefficient singleTerm
  dsimp only [elvQuotientFunctor]
  split_ifs with h
  · rw [← elvDotPolynomial_first]
    simp only [elvDotPolynomial, coefficientDotPolynomial, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact elvQuotientMap_source D Sc cutoff _ _
  · unfold evenCyclotomic deformedCyclotomic
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show firstDotPower D Sc [i] j.val = dotE D Sc [i] 0 ^ j.val by
      simp only [dotE_pow, firstDotPower, List.map_replicate]]
    exact elvQuotientMap_source D Sc cutoff _ _

private theorem single_precomp (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m n : ℕ) :
    singleTerm D Sc cutoff i 1 m ≫ singleTerm D Sc cutoff i a n =
      singleTerm D Sc cutoff i a (n + m) := by
  change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
    (𝟙 _) (dotE D Sc [i] 0 ^ m) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
      a (dotE D Sc [i] 0 ^ n) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [proj_id, ↓reduceIte, one_ne_zero, Category.id_comp, Limits.zero_comp,
    BoxProd.tmulHom_def, TensorProduct.zero_tmul]
  change a ⊗ₜ[k] ((dotE D Sc [i] 0 ^ n) * (dotE D Sc [i] 0 ^ m)) = _
  rw [← pow_add]
  rfl

private theorem single_postcomp (i : I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    singleTerm D Sc cutoff i b n ≫ singleTerm D Sc cutoff i a 0 =
      singleTerm D Sc cutoff i (a * b) n := by
  change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
    b (dotE D Sc [i] 0 ^ n) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i]) a (𝟙 _) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [twist_id, Category.comp_id, ← BoxProd.tmulHom_add_left,
    ← Preadditive.add_comp, proj_add_proj]
  rfl

/-- Multiplying the genuine relation on the two specified sides keeps all
coefficients, in their original order; no parity specialization is used. -/
theorem single_recurrence (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1), singleClass D Sc cutoff i
      (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 := by
  have h := comp_ideal D Sc cutoff (singleTerm D Sc cutoff i 1 m)
    (relation_mem D Sc cutoff i [])
  have h' := ideal_comp D Sc cutoff h (singleTerm D Sc cutoff i a 0)
  rw [single_relation, Preadditive.comp_sum, Preadditive.sum_comp] at h'
  simp only [single_precomp, single_postcomp] at h'
  have hz : (ideal D Sc cutoff [i] [i]).mkQ
      (∑ j : Fin (cutoff i + 1), singleTerm D Sc cutoff i
        (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (ideal D Sc cutoff [i] [i])).mpr h'
  rw [map_sum] at hz
  exact hz

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coefficient truncation of the old ELV quotient

The homogeneous reservoir truncation of `DeformedGradedAction.md` is imposed
inside the coefficient diagram category, by the two-sided ideal generated by
the coefficient weight ideal. The cyclotomic relations and exterior
coefficients are unchanged. Bounds below concern only one-strand corners.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- A coefficient at a word identity, with the original exterior algebra. -/
def coefficientIdentity (t : List I) (a : SKM.SYM D k) : hom D Sc cutoff t t :=
  SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k] (𝟙 _)

/-- Two-sided Hom ideal generated by coefficient monomials of weight at least `N`. -/
def coefficientHomIdeal (N : ℕ) (v w : List I) : Submodule k (hom D Sc cutoff v w) :=
  Submodule.span k {f | ∃ t a, N ≤ SKM.SYM.coefficientWeight D a ∧
    ∃ l : hom D Sc cutoff v t, ∃ r : hom D Sc cutoff t w,
      l ≫ coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D k a) ≫ r = f}

/-- Both the old relations and the coefficient truncation are imposed. -/
def truncatedIdeal (N : ℕ) (v w : List I) : Submodule k (hom D Sc cutoff v w) :=
  ideal D Sc cutoff v w ⊔ coefficientHomIdeal D Sc cutoff N v w

abbrev TruncatedOld (N : ℕ) (v w : List I) :=
  hom D Sc cutoff v w ⧸ truncatedIdeal D Sc cutoff N v w

/-- The further quotient map from the old quotient. -/
def truncateOld (N : ℕ) (v w : List I) :
    Old D Sc cutoff v w →ₗ[k] TruncatedOld D Sc cutoff N v w :=
  Submodule.mapQ _ _ LinearMap.id (by intro x hx; exact Submodule.mem_sup_left hx)

@[simp] theorem truncateOld_mk (N : ℕ) (v w : List I) (f : hom D Sc cutoff v w) :
    truncateOld D Sc cutoff N v w ((ideal D Sc cutoff v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N v w).mkQ f := rfl

theorem truncateOld_surjective (N : ℕ) (v w : List I) :
    Function.Surjective (truncateOld D Sc cutoff N v w) := by
  intro z
  obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v w).mkQ_surjective z
  exact ⟨(ideal D Sc cutoff v w).mkQ f, rfl⟩

theorem coefficientHomIdeal_comp (N : ℕ) {v t w : List I} {f : hom D Sc cutoff v t}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v t) (b : hom D Sc cutoff t w) :
    f ≫ b ∈ coefficientHomIdeal D Sc cutoff N v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, a, ha, l, r, rfl⟩ := hf
    exact Submodule.subset_span ⟨s, a, ha, l, r ≫ b, by simp only [Category.assoc]⟩
  | zero => simp
  | add f g _ _ hf hg => simpa only [Preadditive.add_comp] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [Linear.smul_comp] using Submodule.smul_mem _ c hf

theorem comp_coefficientHomIdeal (N : ℕ) {v t w : List I} (b : hom D Sc cutoff v t)
    {f : hom D Sc cutoff t w} (hf : f ∈ coefficientHomIdeal D Sc cutoff N t w) :
    b ≫ f ∈ coefficientHomIdeal D Sc cutoff N v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, a, ha, l, r, rfl⟩ := hf
    exact Submodule.subset_span ⟨s, a, ha, b ≫ l, r, by simp only [Category.assoc]⟩
  | zero => simp
  | add f g _ _ hf hg => simpa only [Preadditive.comp_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [Linear.comp_smul] using Submodule.smul_mem _ c hf

theorem truncatedIdeal_comp (N : ℕ) {v t w : List I} {f : hom D Sc cutoff v t}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v t) (b : hom D Sc cutoff t w) :
    f ≫ b ∈ truncatedIdeal D Sc cutoff N v w := by
  obtain ⟨f, hf₁, g, hg, rfl⟩ := Submodule.mem_sup.mp hf
  rw [Preadditive.add_comp]
  exact Submodule.mem_sup.mpr ⟨_, ideal_comp D Sc cutoff hf₁ b,
    _, coefficientHomIdeal_comp D Sc cutoff N hg b, rfl⟩

theorem comp_truncatedIdeal (N : ℕ) {v t w : List I} (b : hom D Sc cutoff v t)
    {f : hom D Sc cutoff t w} (hf : f ∈ truncatedIdeal D Sc cutoff N t w) :
    b ≫ f ∈ truncatedIdeal D Sc cutoff N v w := by
  obtain ⟨f, hf₁, g, hg, rfl⟩ := Submodule.mem_sup.mp hf
  rw [Preadditive.comp_add]
  exact Submodule.mem_sup.mpr ⟨_, comp_ideal D Sc cutoff b hf₁,
    _, comp_coefficientHomIdeal D Sc cutoff N b hg, rfl⟩

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem coefficientIdentity_basis_degree (t : List I) (a : SKM.SYM.CoefficientIndex D) :
    coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D k a) ∈
      elvHomDegree D sy Sc hc cutoff t t (SKM.SYM.coefficientDegree D sy a) := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  have ha : SKM.SYM.coefficientBasis D k a ∈
      SKM.SYM.coefficientDegreePart D k sy (SKM.SYM.coefficientDegree D sy a) :=
    Submodule.subset_span ⟨a, rfl, rfl⟩
  have hi : (𝟙 ((pres D Sc).obj (ob D t))) ∈ homDegree D sy Sc t t 0 :=
    GradedSupercategory.id_mem_degree _
  have h := elvQuotientMap_source_mem_degree D sy Sc hc cutoff ha hi
  rw [elvQuotientMap_source, add_zero] at h
  exact h

theorem coefficientHomIdeal_dproj_mem (N : ℕ) {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) (n : ℤ) :
    homDproj D sy Sc hc cutoff n f ∈ coefficientHomIdeal D Sc cutoff N v w := by
  let _ := elvHomGrading D sy Sc hc cutoff
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, c, hcw, a, b, rfl⟩ := hf
    change dproj k n (a ≫ coefficientIdentity D Sc cutoff t
      (SKM.SYM.coefficientBasis D k c) ≫ b) ∈ _
    refine induction_on_degree (R := k) a (by simp) (fun r a ha => ?_)
      (fun a a' ha ha' => ?_)
    · refine induction_on_degree (R := k) b (by simp) (fun s b hb => ?_)
        (fun b b' hb hb' => ?_)
      · have hg := comp_mem_degree ha
          (comp_mem_degree (coefficientIdentity_basis_degree D Sc cutoff sy hc t c) hb)
        by_cases h : r + (SKM.SYM.coefficientDegree D sy c + s) = n
        · rw [← h, dproj_of_mem hg]
          exact Submodule.subset_span ⟨t, c, hcw, a, b, rfl⟩
        · rw [dproj_of_mem_ne hg h]
          exact Submodule.zero_mem _
      · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
    · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'
  | zero => simpa only [map_zero] using (coefficientHomIdeal D Sc cutoff N v w).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

theorem truncatedIdeal_dproj_mem (N : ℕ) {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) (n : ℤ) :
    homDproj D sy Sc hc cutoff n f ∈ truncatedIdeal D Sc cutoff N v w := by
  obtain ⟨f, hf₁, g, hg, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_dproj_mem D sy Sc hc cutoff hf₁ n,
    _, coefficientHomIdeal_dproj_mem D Sc cutoff sy hc N hg n, rfl⟩

theorem coefficientIdentity_basis_parity (t : List I) (a : SKM.SYM.CoefficientIndex D) :
    coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D k a) ∈
      Supercategory.parity (R := k) (obj D Sc cutoff t) (obj D Sc cutoff t)
        (a.2.card : ZMod 2) := by
  have ha := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.coefficientBasis_mem_parity D k a)
  simp only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] at ha
  have h := BoxProd.tmul_mem_parity (X := obj D Sc cutoff t) (Y := obj D Sc cutoff t)
    ha (Supercategory.id_mem (R := k) ((pres D Sc).obj (ob D t)))
  dsimp only [coefficientIdentity, hom, obj, elvQuotientObj, coefficientObj] at h ⊢
  simpa only [add_zero] using h

theorem coefficientHomIdeal_proj_mem (N : ℕ) {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) (n : ZMod 2) :
    Supercategory.proj k n f ∈ coefficientHomIdeal D Sc cutoff N v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, c, hcw, a, b, rfl⟩ := hf
    refine Supercategory.induction_on (R := k) a (by simp) (fun r a ha => ?_)
      (fun a a' ha ha' => ?_)
    · refine Supercategory.induction_on (R := k) b (by simp) (fun s b hb => ?_)
        (fun b b' hb hb' => ?_)
      · have hg := Supercategory.comp_mem ha
          (Supercategory.comp_mem (coefficientIdentity_basis_parity D Sc cutoff t c) hb)
        by_cases h : r + ((c.2.card : ZMod 2) + s) = n
        · rw [← h, Supercategory.proj_of_mem hg]
          exact Submodule.subset_span ⟨t, c, hcw, a, b, rfl⟩
        · rw [Supercategory.proj_of_mem_ne hg h]
          exact Submodule.zero_mem _
      · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
    · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'
  | zero => simpa only [map_zero] using (coefficientHomIdeal D Sc cutoff N v w).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

theorem truncatedIdeal_proj_mem (N : ℕ) {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) (n : ZMod 2) :
    Supercategory.proj k n f ∈ truncatedIdeal D Sc cutoff N v w := by
  obtain ⟨f, hf₁, g, hg, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_proj_mem D Sc cutoff hf₁ n,
    _, coefficientHomIdeal_proj_mem D Sc cutoff N hg n, rfl⟩

variable (N : ℕ)

/-- Super parity on the old quotient, distinct from integer degree modulo two. -/
def truncatedParity (v w : List I) (p : ZMod 2) : Submodule k (TruncatedOld D Sc cutoff N v w) :=
  (Supercategory.parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p).map
    (truncatedIdeal D Sc cutoff N v w).mkQ

/-- The descended total parity projection. -/
def truncatedProj (v w : List I) (p : ZMod 2) :
    TruncatedOld D Sc cutoff N v w →ₗ[k] TruncatedOld D Sc cutoff N v w :=
  (truncatedIdeal D Sc cutoff N v w).mapQ (truncatedIdeal D Sc cutoff N v w) (Supercategory.proj k p)
    (fun _ hf => truncatedIdeal_proj_mem D Sc cutoff N hf p)

@[simp] theorem truncatedProj_mk (v w : List I) (p : ZMod 2) (f : hom D Sc cutoff v w) :
    truncatedProj D Sc cutoff N v w p ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N v w).mkQ (Supercategory.proj k p f) := rfl

theorem truncatedProj_of_mem {v w : List I} {q : ZMod 2} {f : TruncatedOld D Sc cutoff N v w}
    (hf : f ∈ truncatedParity D Sc cutoff N v w q) (p : ZMod 2) :
    truncatedProj D Sc cutoff N v w p f = if q = p then f else 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [truncatedProj_mk]
  split_ifs with h
  · subst p
    rw [Supercategory.proj_of_mem ha]
  · rw [Supercategory.proj_of_mem_ne ha h, map_zero]

/-- The parity images form an internal direct sum over the same ground ring. -/
theorem truncatedParity_internal (v w : List I) :
    DirectSum.IsInternal (truncatedParity D Sc cutoff N v w) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (truncatedProj D Sc cutoff N v w n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, truncatedProj D Sc cutoff N v w n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => truncatedProj_of_mem D Sc cutoff N (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · change (⨆ p, (Supercategory.parity (R := k) (obj D Sc cutoff v)
      (obj D Sc cutoff w) p).map (truncatedIdeal D Sc cutoff N v w).mkQ) = ⊤
    let _ := Supercategory.decomposition k (obj D Sc cutoff v) (obj D Sc cutoff w)
    rw [← Submodule.map_iSup,
      (DirectSum.Decomposition.isInternal (Supercategory.parity (R := k)
        (obj D Sc cutoff v) (obj D Sc cutoff w))).submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- Degree parts in the further quotient are images of the original Hom parts. -/
def truncatedDegree (v w : List I) (n : ℤ) : Submodule k (TruncatedOld D Sc cutoff N v w) :=
  (elvHomDegree D sy Sc hc cutoff v w n).map (truncatedIdeal D Sc cutoff N v w).mkQ

/-- Integer component projection on the old cyclotomic quotient. -/
def truncatedDproj (v w : List I) (n : ℤ) :
    TruncatedOld D Sc cutoff N v w →ₗ[k] TruncatedOld D Sc cutoff N v w :=
  (truncatedIdeal D Sc cutoff N v w).mapQ (truncatedIdeal D Sc cutoff N v w) (homDproj D sy Sc hc cutoff n)
    (fun _ hf => truncatedIdeal_dproj_mem D Sc cutoff sy hc N hf n)

@[simp] theorem truncatedDproj_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    truncatedDproj D Sc cutoff sy hc N v w n ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N v w).mkQ (homDproj D sy Sc hc cutoff n f) := rfl

theorem truncatedDproj_of_mem {v w : List I} {m : ℤ} {f : TruncatedOld D Sc cutoff N v w}
    (hf : f ∈ truncatedDegree D Sc cutoff sy hc N v w m) (n : ℤ) :
    truncatedDproj D Sc cutoff sy hc N v w n f = if m = n then f else 0 := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [truncatedDproj_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The coefficient-truncated old quotient has an internal integer grading. -/
theorem truncatedDegree_internal (v w : List I) :
    DirectSum.IsInternal (truncatedDegree D Sc cutoff sy hc N v w) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (truncatedDproj D Sc cutoff sy hc N v w n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, truncatedDproj D Sc cutoff sy hc N v w n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => truncatedDproj_of_mem D Sc cutoff sy hc N (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · change (⨆ n, (elvHomDegree D sy Sc hc cutoff v w n).map
      (truncatedIdeal D Sc cutoff N v w).mkQ) = ⊤
    rw [← Submodule.map_iSup, (elvHomDegree_internal D sy Sc hc cutoff v w).submodule_iSup_eq_top]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- The quotient projection is homogeneous of degree zero. -/
theorem mkQ_mem_truncatedDegree {v w : List I} {n : ℤ} {f : hom D Sc cutoff v w}
    (hf : f ∈ elvHomDegree D sy Sc hc cutoff v w n) :
    (truncatedIdeal D Sc cutoff N v w).mkQ f ∈ truncatedDegree D Sc cutoff sy hc N v w n :=
  Submodule.mem_map_of_mem hf

/-- The quotient map preserves the inherited integer degree. -/
theorem truncateOld_mem_degree {v w : List I} {n : ℤ} {f : Old D Sc cutoff v w}
    (hf : f ∈ oldDegree D sy Sc hc cutoff v w n) :
    truncateOld D Sc cutoff N v w f ∈ truncatedDegree D Sc cutoff sy hc N v w n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact Submodule.mem_map_of_mem ha

end OddMath.QuiverHecke.ELV
end

end

section

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem vacuum_index_target {w : List I} (j : NFIdx [] w) : w = [] := by
  apply List.eq_nil_of_length_eq_zero
  have h := congrArg List.length j.tgt_cw
  simpa only [length_tgt, List.length_nil] using h.symm

theorem vacuum_nf (j : NFIdx ([] : List I) []) :
    j.nf (D := D) (Sc := Sc) = 𝟙 _ := by
  have hd : j.val.1 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have := j.property.2.1 x hx
    simp at this
  have hp : j.val.2 = 1 := by
    ext x
    exact Fin.elim0 x
  have hc : Categorification.TypeA.canWord 0 j.val.2 = [] := by
    rw [hp]
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  simp only [NFIdx.nf, hd, List.map_nil, List.nil_append, List.length_nil, hc, cw]
  exact cl_nil D Sc [] _

theorem vacuum_hom_span (f : hom D Sc cutoff [] []) :
    f ∈ Submodule.span k (Set.range (coefficientIdentity D Sc cutoff [])) := by
  change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D [])) at f
  change f ∈ Submodule.span k (Set.range fun a : SKM.SYM D k =>
    SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D []))))
  induction f using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a f =>
    obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
      (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon a
    have hf : f ∈ Submodule.span k (Set.range (fun j : NFIdx [] [] => j.nf (D := D) (Sc := Sc))) := by
      rw [span_nf]; trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      simp only [vacuum_nf D Sc]
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => simp only [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [TensorProduct.tmul_smul] using Submodule.smul_mem _ c hx

theorem vacuum_hom_eq_zero {w : List I} (hw : w ≠ []) (f : hom D Sc cutoff [] w) : f = 0 := by
  change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D w)) at f
  change f = (0 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D w)))
  induction f using TensorProduct.inductionOn with
  | add x y hx hy => rw [hx, hy, add_zero]
  | tmul a f =>
    have hf : f ∈ Submodule.span k (Set.range (fun j : NFIdx [] w => j.nf (D := D) (Sc := Sc))) := by
      rw [span_nf]; trivial
    have hf0 : f = 0 := by
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨j, rfl⟩ := hf
        exact (hw (vacuum_index_target j)).elim
      | zero => rfl
      | add x y _ _ hx hy => rw [hx, hy, add_zero]
      | smul c x _ hx => rw [hx, smul_zero]
    rw [hf0, TensorProduct.tmul_zero]

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

def vacuumClassLinear : SKM.SYM D k →ₗ[k] TruncatedOld D Sc cutoff N [] [] :=
  (truncatedIdeal D Sc cutoff N [] []).mkQ.comp
    (((TensorProduct.mk k _ _).flip (𝟙 ((pres D Sc).obj (ob D [])))).comp
      (SKM.SYM.elvCoefficientQuotient D cutoff).toLinearMap)

theorem vacuumClass_basis_zero (a : SKM.SYM.CoefficientIndex D)
    (ha : N ≤ SKM.SYM.coefficientWeight D a) :
    vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D k a) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.mem_sup_right
  apply Submodule.subset_span
  exact ⟨[], a, ha, 𝟙 _, 𝟙 _, by simp only [Category.id_comp, Category.comp_id]; rfl⟩

theorem vacuumClass_basis_degree (a : SKM.SYM.CoefficientIndex D) :
    vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D k a) ∈
      truncatedDegree D Sc cutoff sy hc N [] [] (SKM.SYM.coefficientDegree D sy a) := by
  apply mkQ_mem_truncatedDegree
  have ha : SKM.SYM.coefficientBasis D k a ∈
      SKM.SYM.coefficientDegreePart D k sy (SKM.SYM.coefficientDegree D sy a) :=
    Submodule.subset_span ⟨a, rfl, rfl⟩
  have hf : (𝟙 ((pres D Sc).obj (ob D []))) ∈ homDegree D sy Sc [] [] 0 :=
    (pres D Sc).id_mem_homDeg (gdeg D sy) _
  have h := elvQuotientMap_source_mem_degree D sy Sc hc cutoff ha hf
  rw [elvQuotientMap_source, add_zero] at h
  exact h

/-- Actual vacuum support from a bound on coefficient degree versus total weight. -/
theorem truncatedVacuum_support_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (w : List I) :
    (⊤ : Submodule k (TruncatedOld D Sc cutoff N [] w)) =
      ⨆ n ∈ Set.Icc (0 : ℤ) (M * N), truncatedDegree D Sc cutoff sy hc N [] w n := by
  apply le_antisymm _ le_top
  intro z hz
  clear hz
  obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N [] w).mkQ_surjective z
  by_cases hw : w = []
  · subst w
    have hf := vacuum_hom_span D Sc cutoff f
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      change vacuumClassLinear D Sc cutoff N a ∈ _
      have ha : a ∈ Submodule.span k (Set.range (SKM.SYM.coefficientBasis D k)) := by
        rw [Module.Basis.span_eq]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨b, rfl⟩ := ha
        by_cases hb : N ≤ SKM.SYM.coefficientWeight D b
        · rw [vacuumClass_basis_zero D Sc cutoff N b hb]
          exact Submodule.zero_mem _
        · have hw : (SKM.SYM.coefficientWeight D b : ℤ) ≤ N := by
            exact_mod_cast (by omega : SKM.SYM.coefficientWeight D b ≤ N)
          have hn : SKM.SYM.coefficientDegree D sy b ∈ Set.Icc (0 : ℤ) (M * N) :=
            ⟨SKM.SYM.coefficientDegree_nonneg D sy b,
              (hbound b).trans (mul_le_mul_of_nonneg_left hw hM)⟩
          exact Submodule.mem_iSup_of_mem (SKM.SYM.coefficientDegree D sy b)
            (Submodule.mem_iSup_of_mem hn (vacuumClass_basis_degree D Sc cutoff sy hc N b))
      | zero => simpa only [map_zero] using Submodule.zero_mem (⨆ n ∈ Set.Icc (0 : ℤ) (M * N),
          truncatedDegree D Sc cutoff sy hc N [] [] n)
      | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
    | zero => simpa only [map_zero] using Submodule.zero_mem (⨆ n ∈ Set.Icc (0 : ℤ) (M * N),
        truncatedDegree D Sc cutoff sy hc N [] [] n)
    | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
  · rw [vacuum_hom_eq_zero D Sc cutoff hw f, map_zero]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELV
end

end
