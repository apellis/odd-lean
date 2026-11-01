import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendSpecialization

/-! # Actual old append-dot units on specialized probe modules
Relative word-corner units act as genuine endomorphism units of the actual
word-idempotent subspaces, rather than only as units in an abstract ring.
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
variable (ν : List I)
local notation "C" => ELVOld.OldContentCategory D Sc cut ν

theorem probeOldWordIdempotent_idem (v : C) :
    IsIdempotentElem (probeOldWordIdempotent D m Sc ν v) := by
  change probeOldWordIdempotent D m Sc ν v * probeOldWordIdempotent D m Sc ν v = _
  unfold probeOldWordIdempotent
  rw [← map_mul, Hn.wordIdempotent_sq]

variable {B : Type u} [Ring B] [Algebra k B] {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

private theorem probeOldCornerAction_mem (v : C)
    (c : (probeOldWordIdempotent_idem D m Sc ν v).Corner)
    (x : M.toSVec) (_hx : x ∈ probeOldWordSubmodule D m Sc ν M v) :
    M.lact c.val x ∈ probeOldWordSubmodule D m Sc ν M v := by
  have hc := ((Subsemigroup.mem_corner_iff (probeOldWordIdempotent_idem D m Sc ν v)).mp c.property).1
  have h := congrArg (fun z => M.lact z x) hc
  change M.lact _ (M.lact c.val x) = M.lact c.val x
  simpa only [M.lact_mul, SVec.comp_apply] using h

/-- The relative unit of the word corner acts as the actual identity on its subspace. -/
def probeOldWordCornerAction (v : C) :
    (probeOldWordIdempotent_idem D m Sc ν v).Corner →+*
      End (probeOldWordSVec D m Sc ν M v) where
  toFun c := End.of (SVec.restrictHom (M.lact c.val) (probeOldCornerAction_mem D m Sc ν M v c))
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (probeOldWordIdempotent D m Sc ν v) x.val = x.val
    exact x.property
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact 0 x.val = 0
    rw [map_zero]
    rfl
  map_add' c d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (c.val + d.val) x.val = M.lact c.val x.val + M.lact d.val x.val
    rw [map_add]
    rfl
  map_mul' c d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (c.val * d.val) x.val = M.lact c.val (M.lact d.val x.val)
    rw [M.lact_mul]
    rfl

/-- At positive content this is the existing literal cyclotomic word corner. -/
def probeOldPositiveCornerAction (i : I) (ρ : List I)
    {B' : Type u} [Ring B'] [Algebra k B'] {GB' : ZMod 2 → Submodule k B'}
    (N : SuperBimodule
      (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
        (probePolynomial_parity D m) (ρ.length + 1)) GB')
    (v : ELVOld.OldContentCategory D Sc cut (i :: ρ)) :
    CyclotomicWordCorner D Sc a
      (probeContentWord (i :: ρ) (ELVOld.oldContentWord D Sc cut (i :: ρ) v)) →+*
        End (probeOldWordSVec D m Sc (i :: ρ) N v) :=
  probeOldWordCornerAction D m Sc (i :: ρ) N v

/-- The actual old append-dot component acts invertibly on an actual probe
word subspace, not merely in a relative corner ring. -/
theorem probeOldAppendDot_action_isUnit (i : I) (ρ : List I)
    {B' : Type u} [Ring B'] [Algebra k B'] {GB' : ZMod 2 → Submodule k B'}
    (N : SuperBimodule
      (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
        (probePolynomial_parity D m) (ρ.length + 1)) GB')
    (v : ELVOld.OldContentCategory D Sc cut ρ) :
    IsUnit (End.of ((probeOldModule D m Sc (i :: ρ) N).map
      (show (ELVOld.oldContentAppend D Sc cut ρ i).obj v ⟶
        (ELVOld.oldContentAppend D Sc cut ρ i).obj v from
          ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj))) := by
  let s := probeContentWord ρ (ELVOld.oldContentWord D Sc cut ρ v)
  let w := (ELVOld.oldContentAppend D Sc cut ρ i).obj v
  have hu := (elvProbeOldAppendDotCorner_isUnit D m Sc s i).map
    (probeOldPositiveCornerAction D m Sc i ρ N w)
  change IsUnit ((probeOldPositiveCornerAction D m Sc i ρ N w)
    (elvProbeOldAppendDotCorner D m Sc s i))
  exact hu

end OddMath.QuiverHecke
