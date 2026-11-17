import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import OddMath.QuiverHecke.CyclotomicAction.ContentModules.CentralPolynomialModule
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop.CyclotomicCrossingTensor

/-!
# Content modules

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Untruncated old ELV categories of a fixed content
This restricts the existing old category, with its entire coefficient ring,
to a finite permutation class of words. Append is the existing canonical old
append functor. No coefficient truncation occurs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full old category on the finite permutation class of a word. -/
structure OldContentCategory (ν : List I) where
  obj : OldCategory D Sc cutoff
  wordPerm : obj.word.Perm ν

instance oldContentCategory (ν : List I) : Category (OldContentCategory D Sc cutoff ν) where
  Hom v w := v.obj ⟶ w.obj
  id v := 𝟙 v.obj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance oldContentPreadditive (ν : List I) : Preadditive (OldContentCategory D Sc cutoff ν) where
  homGroup v w := inferInstanceAs (AddCommGroup (v.obj ⟶ w.obj))
  add_comp := by intro v w z f g h; exact Preadditive.add_comp v.obj w.obj z.obj f g h
  comp_add := by intro v w z f g h; exact Preadditive.comp_add v.obj w.obj z.obj f g h

instance oldContentLinear (ν : List I) : Linear k (OldContentCategory D Sc cutoff ν) where
  homModule v w := inferInstanceAs (Module k (v.obj ⟶ w.obj))
  smul_comp := by intro v w z r f g; exact Linear.smul_comp v.obj w.obj z.obj r f g
  comp_smul := by intro v w z f r g; exact Linear.comp_smul v.obj w.obj z.obj f r g

instance oldContentSupercategory (ν : List I) :
    Supercategory k (OldContentCategory D Sc cutoff ν) where
  parity v w := parity (R := k) v.obj w.obj
  isInternal v w := Supercategory.isInternal v.obj w.obj
  id_mem v := id_mem v.obj
  comp_mem := Supercategory.comp_mem

/-- The inclusion preserves every quotient Hom, including exterior coefficients. -/
def oldContentInclusion (ν : List I) :
    OldContentCategory D Sc cutoff ν ⥤ OldCategory D Sc cutoff where
  obj v := v.obj
  map f := f

instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Full where
  map_surjective f := ⟨f,rfl⟩
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Faithful where
  map_injective h := h
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Additive where
  map_add := rfl
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Linear k where
  map_smul _ _ := rfl
instance (ν : List I) : IsSuperfunctor k (oldContentInclusion D Sc cutoff ν) where
  map_mem h := h

/-- Extract the same finite content coordinate from an actual content object. -/
def oldContentWord (ν : List I) (v : OldContentCategory D Sc cutoff ν) : ContentWords ν :=
  ⟨v.obj.word,v.wordPerm⟩

/-- Append uses the existing canonical untruncated old functor. -/
def oldContentAppend (ν : List I) (i : I) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff (i :: ν) where
  obj v := ⟨(CyclotomicCrossingTensor.append D Sc cutoff i).obj v.obj,
    (v.wordPerm.append (List.Perm.refl [i])).trans
      (List.perm_append_comm : (ν ++ [i]).Perm ([i] ++ ν))⟩
  map f := (CyclotomicCrossingTensor.append D Sc cutoff i).map f
  map_id v := (CyclotomicCrossingTensor.append D Sc cutoff i).map_id v.obj
  map_comp f g := (CyclotomicCrossingTensor.append D Sc cutoff i).map_comp f g

instance (ν : List I) (i : I) : (oldContentAppend D Sc cutoff ν i).Additive where
  map_add := (CyclotomicCrossingTensor.append D Sc cutoff i).map_add
instance (ν : List I) (i : I) : (oldContentAppend D Sc cutoff ν i).Linear k where
  map_smul f r := (CyclotomicCrossingTensor.append D Sc cutoff i).map_smul r f
instance (ν : List I) (i : I) : IsSuperfunctor k (oldContentAppend D Sc cutoff ν i) where
  map_mem := Supercategory.map_mem (CyclotomicCrossingTensor.append D Sc cutoff i)

/-- Appending then including is literally the established old append functor. -/
theorem oldContentAppend_inclusion (ν : List I) (i : I) :
    oldContentAppend D Sc cutoff ν i ⋙ oldContentInclusion D Sc cutoff (i :: ν) =
      oldContentInclusion D Sc cutoff ν ⋙ CyclotomicCrossingTensor.append D Sc cutoff i := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! Degree shifts of the finite append spanning maps. -/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem affineUnit_mem_degree {v w : List I} {d : ℤ}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ homDegree D sy Sc v w d) :
    affineUnit D Sc cutoff v w f ∈ elvHomDegree D sy Sc hc cutoff v w d := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  have h := BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w)
    (GradedSupercategory.id_mem_degree (R := k) (obj D Sc cutoff v).fst) hf
  rw [zero_add] at h
  exact h

theorem appendSourcePower_mem_degree (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n ∈
      elvHomDegree D sy Sc hc cutoff (v ++ [i]) (v ++ [i]) (2 * sy.d i * n) := by
  rw [appendSourcePower_whisker]
  apply affineUnit_mem_degree D Sc cutoff sy hc
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  have h : (dotE D Sc [i] 0 ^ n : End _) ∈ homDegree D sy Sc [i] [i]
      (2 * sy.d i * n) := by
    simpa only [firstDotPower, dotE_pow, List.map_replicate] using
      firstDotPower_mem_gdeg D sy Sc i [] n
  exact GradedMonoidalSupercategory.whiskerLeft_mem_degree ((pres D Sc).obj (ob D v)) h

/-- Sum of the generator degrees of the concrete tail diagram. -/
def appendTailDegree {i : I} {v w : List I} (x : AppendIdx i v w) : ℤ :=
  gsum D sy (pl (x.oldTarget ++ [i])
    (((List.replicate x.1.1 v.length).map PG.dot) ++
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)))

theorem appendTail_mem_degree {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ homDegree D sy Sc (x.oldTarget ++ [i]) w
      (appendTailDegree D sy x) :=
  Presentation.diag_mem_homDeg' (degree_gdeg_mkD D sy _ _)

/-- The source moving dots, old homogeneous term, and tail contribute additively. -/
theorem appendBoundedOldMap_mem_degree (N : ℕ) (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {a b : ℤ}
    (hh : h ∈ elvHomDegree D sy Sc hc cutoff (t ++ [i]) w b)
    {r : TruncatedOld D Sc cutoff N v t}
    (hr : r ∈ truncatedDegree D Sc cutoff sy hc N v t a) :
    appendBoundedOldMap D Sc cutoff N i v t w j h r ∈
      truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w (2 * sy.d i * j + (a + b)) := by
  obtain ⟨r, hr, rfl⟩ := hr
  rw [appendBoundedOldMap_mk]
  apply Submodule.mem_map_of_mem
  let _ := elvHomGrading D sy Sc hc cutoff
  exact GradedSupercategory.comp_mem_degree
    (appendSourcePower_mem_degree D Sc cutoff sy hc i v j)
    (GradedSupercategory.comp_mem_degree
      (rightContext_mem_degree D Sc cutoff sy hc [i] hr) hh)

/-- A supported smaller quotient gives supported range, with the concrete shift. -/
theorem appendBoundedOldMap_range_le (N : ℕ) (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {b : ℤ}
    (hh : h ∈ elvHomDegree D sy Sc hc cutoff (t ++ [i]) w b)
    (S : Set ℤ)
    (hS : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v t)) =
      ⨆ a ∈ S, truncatedDegree D Sc cutoff sy hc N v t a) :
    LinearMap.range (appendBoundedOldMap D Sc cutoff N i v t w j h) ≤
      ⨆ a ∈ S, truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
        (2 * sy.d i * j + (a + b)) := by
  rw [← Submodule.map_top, hS, Submodule.map_iSup]
  apply iSup_le
  intro a
  rw [Submodule.map_iSup]
  apply iSup_le
  intro ha
  apply le_trans _ (le_iSup_of_le a (le_iSup_of_le ha le_rfl))
  rintro z ⟨r, hr, rfl⟩
  exact appendBoundedOldMap_mem_degree D Sc cutoff sy hc N i v t w j hh hr

/-- All-content support propagation from smaller truncated Hom support. The
indices are finite when each `S q` is finite; no finite-colour assumption occurs. -/
theorem appendFiniteRange_degree_support (N : ℕ) (i : I) (v w : List I)
    (S : AppendCrossingSkeleton i v w → Set ℤ)
    (hS : ∀ q, (⊤ : Submodule k (TruncatedOld D Sc cutoff N v q.index.oldTarget)) =
      ⨆ a ∈ S q, truncatedDegree D Sc cutoff sy hc N v q.index.oldTarget a) :
    (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) =
      ⨆ (q : AppendCrossingSkeleton i v w)
        (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree)
        (a : ℤ) (_ : a ∈ S q),
        truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
          (2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) := by
  apply le_antisymm _ le_top
  rw [← appendFiniteRangeSpan_eq_top D Sc cutoff N i v w]
  unfold appendFiniteRangeSpan
  apply iSup_le
  intro q
  apply iSup_le
  intro j
  exact le_trans (appendBoundedOldMap_range_le D Sc cutoff sy hc N i v
    q.index.oldTarget w j.val
    (affineUnit_mem_degree D Sc cutoff sy hc (appendTail_mem_degree D Sc sy q.index))
    (S q) (hS q)) (le_iSup_of_le q (le_iSup_of_le j le_rfl))

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Finite integer support at arbitrary strand content

The coefficient-weight-truncated vacuum and the finite homogeneous append
spanning family give finite degree support by induction on the source word.
No rank, freeness, or bound on the number of words of a weight is used.
-/
noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

/-- Finite smaller degree supports propagate through the concrete finite append family. -/
theorem truncatedAppend_finite_support (i : I) (v w : List I)
    (ih : ∀ t : List I, ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v t)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v t n) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w n := by
  classical
  choose S hfin hs using ih
  let T : Set ℤ := ⋃ (q : AppendCrossingSkeleton i v w),
    ⋃ (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
      (fun a => 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) '' S q.index.oldTarget
  have ht : T.Finite := Set.finite_iUnion fun q => Set.finite_iUnion fun j =>
    (hfin q.index.oldTarget).image _
  refine ⟨T, ht, le_antisymm ?_ le_top⟩
  rw [appendFiniteRange_degree_support D Sc cutoff sy hc N i v w
    (fun q => S q.index.oldTarget) (fun q => hs q.index.oldTarget)]
  refine iSup_le fun q => iSup_le fun j => iSup_le fun a => iSup_le fun ha => ?_
  exact le_iSup_of_le _ (le_iSup_of_le
    (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨j, ⟨a, ha, rfl⟩⟩⟩ :
      2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ∈ T) le_rfl)

/-- Arbitrary content has finite support whenever the coefficient degrees have a
uniform degree/weight bound. This bound is obtained from finite colours below. -/
theorem truncatedContent_finite_support_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨Set.Icc 0 (M * N), Set.finite_Icc _ _,
      truncatedVacuum_support_of_bound D Sc cutoff sy hc N M hM hbound w⟩
  | append_singleton v i ih =>
      exact truncatedAppend_finite_support D Sc cutoff sy hc N i v w ih

/-- Finite colours give bounded integer support for every pair of words, including
arbitrarily repeated even, odd, and mixed colours. -/
theorem truncatedContent_finite_support [Finite I] (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_finite_support_of_bound D Sc cutoff sy hc N M hM hb v w

/-- A finite homogeneous spanning support kills all other homogeneous parts. -/
theorem truncatedDegree_eq_bot_of_support (v w : List I) (S : Set ℤ)
    (hS : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
      ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n)
    (n : ℤ) (hn : n ∉ S) :
    truncatedDegree D Sc cutoff sy hc N v w n = ⊥ := by
  have hp : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) ≤
      LinearMap.ker (truncatedDproj D Sc cutoff sy hc N v w n) := by
    rw [hS]
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro z hz
    exact (truncatedDproj_of_mem D Sc cutoff sy hc N hz n).trans
      (ite_eq_right (by intro he; exact hn (he ▸ ha)))
  apply bot_unique
  intro z hz
  have he := truncatedDproj_of_mem D Sc cutoff sy hc N hz n
  rw [ite_eq_left rfl, hp (Submodule.mem_top : z ∈ (⊤ : Submodule k _))] at he
  exact he.symm

/-- An explicit loose symmetric interval extracted from a finite support. -/
theorem truncatedContent_bounded_of_finite_support (v w : List I)
    (h : ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ := by
  classical
  obtain ⟨S, hf, hs⟩ := h
  refine ⟨hf.toFinset.sup Int.natAbs, fun n hn =>
    truncatedDegree_eq_bot_of_support D Sc cutoff sy hc N v w S hs n ?_⟩
  intro hmem
  have hnat : n.natAbs ≤ hf.toFinset.sup Int.natAbs :=
    Finset.le_sup (f := Int.natAbs) (hf.mem_toFinset.mpr hmem)
  have habs : |n| ≤ ((hf.toFinset.sup Int.natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have := abs_le.mp habs
  omega

/-- Actual bounded integer support at arbitrary content, from the coefficient
bound and the concrete cyclotomic recurrence, not from a support premise. -/
theorem truncatedContent_bounded_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_finite_support D Sc cutoff sy hc N v w
    (truncatedContent_finite_support_of_bound D Sc cutoff sy hc N M hM hbound v w)

/-- Every coefficient-weight-truncated cyclotomic Hom has bounded integer
support for finite colours, without any restriction on strand content. -/
theorem truncatedContent_bounded [Finite I] (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_finite_support D Sc cutoff sy hc N v w
    (truncatedContent_finite_support D Sc cutoff sy hc N v w)

end OddMath.QuiverHecke.ELV
end

end
