import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import OddMath.QuiverHecke.HnBasis

/-! # Scalar coordinates of the regular probe vacuum

The height-zero regular probe in `SwappedActionAssembly.md`, F2, has a
canonical ground-ring coordinate. We derive it from the empty-word PBW
basis (BE2, (11.1)), retaining the prescribed empty idempotent vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem zeroWord_eq (s : Word I 0) : s = vacuumWord := by
  apply Subtype.ext
  exact List.length_eq_zero_iff.mp s.property

private def zeroNF : NFIdx ([] : List I) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private theorem zeroNF_eq (j : NFIdx ([] : List I) []) : j = zeroNF := by
  apply Subtype.ext
  apply Prod.ext
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    exact Nat.not_lt_zero x (j.property.2.1 x hx)
  · ext a
    exact Fin.elim0 a

private def zeroIndex : HnIdx I 0 := ⟨(vacuumWord, vacuumWord), zeroNF⟩

private theorem zeroIndex_eq (j : HnIdx I 0) : j = zeroIndex := by
  rcases j with ⟨⟨a,b⟩, j⟩
  obtain rfl := zeroWord_eq a
  obtain rfl := zeroWord_eq b
  exact congrArg (fun h => (⟨(vacuumWord, vacuumWord), h⟩ : HnIdx I 0)) (zeroNF_eq j)

@[instance_reducible] private def zeroIndexUnique : Unique (HnIdx I 0) where
  default := zeroIndex
  uniq := zeroIndex_eq

private def heightZeroLinearEquiv : k ≃ₗ[k] Hn D Sc 0 := by
  letI := zeroIndexUnique (I := I)
  exact (Module.Basis.singleton (HnIdx I 0) k).equiv (Hn.basis D Sc 0) (Equiv.refl _)

private theorem heightZeroLinearEquiv_one :
    heightZeroLinearEquiv D Sc 1 = Hn.wordIdempotent (vacuumWord (I := I)) := by
  let := zeroIndexUnique (I := I)
  have h := Module.Basis.equiv_apply (b := Module.Basis.singleton (HnIdx I 0) k)
    (b' := Hn.basis D Sc 0) (e := Equiv.refl _) (zeroIndex (I := I))
  rw [Module.Basis.singleton_apply, Equiv.refl_apply] at h
  change heightZeroLinearEquiv D Sc 1 = _ at h
  rw [h, Hn.basis_apply, ELVOld.vacuum_nf D Sc]
  rfl

variable [Fintype I]

private theorem heightZeroIdempotent_one :
    Hn.wordIdempotent (vacuumWord (I := I)) = (1 : Hn D Sc 0) := by
  classical
  have hu : (Finset.univ : Finset (Word I 0)) = {vacuumWord} := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact zeroWord_eq s
  change OddMath.FiniteHomMatrix.idem vacuumWord = OddMath.FiniteHomMatrix.localUnit Finset.univ
  rw [hu]
  simp [OddMath.FiniteHomMatrix.localUnit]

private theorem heightZeroLinearEquiv_scalar (c : k) :
    heightZeroLinearEquiv D Sc c = algebraMap k (Hn D Sc 0) c := by
  have h := (heightZeroLinearEquiv D Sc).map_smul c (1 : k)
  simpa only [smul_eq_mul, mul_one, heightZeroLinearEquiv_one,
    heightZeroIdempotent_one, Algebra.algebraMap_eq_smul_one] using h

/-- The scalar coordinate of the height-zero algebra, with no cyclotomic
relation or scalar specialization imposed on its empty-word component. -/
def heightZeroScalarEquiv : k ≃ₐ[k] Hn D Sc 0 :=
  AlgEquiv.ofLinearEquiv (heightZeroLinearEquiv D Sc)
    (by rw [heightZeroLinearEquiv_one, heightZeroIdempotent_one])
    (by intro x y; simp only [heightZeroLinearEquiv_scalar, map_mul])

variable (m : I → ℕ)

private theorem probeVacuumVector_val :
    (probeOldVacuumVector D Sc m).val = (1 : Hn D Sc 0) := by
  change Hn.wordIdempotent (vacuumWord (I := I)) = _
  exact heightZeroIdempotent_one D Sc

/-- The scalar parametrization of the literal empty word value of the regular
probe. Its value at one is the original empty idempotent vector. -/
def probeVacuumScalarEquiv :
    k ≃ₗ[k] (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m) where
  toFun c := c • probeOldVacuumVector D Sc m
  invFun v := (heightZeroScalarEquiv D Sc).symm v.val
  left_inv c := by
    change (heightZeroScalarEquiv D Sc).symm (c • (probeOldVacuumVector D Sc m).val) = c
    rw [probeVacuumVector_val]
    change (heightZeroScalarEquiv D Sc).symm (algebraMap k (Hn D Sc 0) c) = c
    rw [← heightZeroLinearEquiv_scalar]
    exact (heightZeroScalarEquiv D Sc).symm_apply_apply c
  right_inv v := by
    apply Subtype.ext
    change (heightZeroScalarEquiv D Sc).symm v.val • (probeOldVacuumVector D Sc m).val = v.val
    rw [probeVacuumVector_val]
    change algebraMap k (Hn D Sc 0) ((heightZeroScalarEquiv D Sc).symm v.val) = v.val
    rw [← heightZeroLinearEquiv_scalar]
    exact (heightZeroScalarEquiv D Sc).apply_symm_apply v.val
  map_add' c d := add_smul c d _
  map_smul' c d := by simp only [RingHom.id_apply, mul_smul, smul_eq_mul]

/-- This coordinate uses the unrescaled prescribed vacuum vector. -/
theorem probeVacuumScalarEquiv_one :
    probeVacuumScalarEquiv D Sc m 1 = probeOldVacuumVector D Sc m := one_smul k _

/-- Every vector of the empty regular probe is even. -/
theorem probeVacuum_even
    (v : (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)) :
    v ∈ ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)).part 0 := by
  obtain ⟨c, rfl⟩ := (probeVacuumScalarEquiv D Sc m).surjective v
  apply Submodule.smul_mem
  change probeOldVacuumVector D Sc m ∈ (probeOldWordSVec D m Sc []
    (SuperBimodule.regular (heightParity D Sc
      (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) 0)) (probeOldVacuumObject D Sc m)).part 0
  dsimp only [probeOldVacuumRegular, probeOldModule, probeOldModuleFunctor,
    probeOldWordSVec, probeOldVacuumVector]
  apply (SVec.mem_sub_part_iff _ _ _).mpr
  change (probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) :
    heightAlgebra D Sc (probePolynomial (k := k) (probeDotExponent D) m) 0) ∈
      (SuperBimodule.regularSVec (heightParity D Sc
        (probePolynomial (k := k) (probeDotExponent D) m)
        (probePolynomial_parity D m) 0)).part 0
  apply (SuperBimodule.mem_regularSVec_part_iff _).mpr
  exact probeOldWordIdempotent_parity D m Sc [] (probeOldVacuumObject D Sc m)

end OddMath.QuiverHecke
