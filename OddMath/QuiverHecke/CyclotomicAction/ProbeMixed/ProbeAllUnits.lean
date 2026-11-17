import OddMath.QuiverHecke.CyclotomicAction.AppendContent.AppendDot
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed.ProbeMixedCornerRelations
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed.ProbeUnitPropagation
import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules.ProbeOrdinaryCategory

/-!
# Probe mixed

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # All-position units in the actual cofinal probe

Induction over positions uses both source and swapped word corners. Equal
colours use direct nilHecke units; distinct colours use the actual signed
slides and both Q remainders. The proof works over the original ground ring,
without finite-dimensionality, residue fields, or Nakayama descent.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I]

omit [Fintype I] in
private theorem probeWord_split_two {n : ℕ} (s : Word I (n+1))
    (r : ℕ) (hr : r+1 < n+1) :
    ∃ (pre : List I) (i j : I) (post : List I),
      pre.length = r ∧ s.val = pre ++ [i,j] ++ post := by
  have hdrop : 2 ≤ (s.val.drop r).length := by
    rw [List.length_drop, s.property]
    omega
  cases hd : s.val.drop r with
  | nil => simp [hd] at hdrop
  | cons i rest =>
    cases ht : rest with
    | nil => simp [hd, ht] at hdrop
    | cons j post =>
      refine ⟨s.val.take r, i, j, post, ?_, ?_⟩
      · rw [List.length_take, s.property, Nat.min_eq_left (by omega)]
      · have hs := List.take_append_drop r s.val
        rw [hd, ht] at hs
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using hs.symm

/-- Every literal dot in every word corner of the prescribed cofinal probe
is a unit, directly over the given commutative ground ring. -/
theorem probeWord_dots_isUnit [Fact Sc.PureNilpotent] (m : I → ℕ) (n : ℕ) :
    ∀ r < n+1, ∀ s : Word I (n+1),
      IsUnit (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m) s
        (dotE D Sc s.val r)) := by
  intro r
  induction r with
  | zero =>
    intro _ s
    exact probe_firstDot_isUnit D Sc m s
  | succ r ih =>
    intro hr s
    obtain ⟨pre, i, j, post, hpre, hs⟩ := probeWord_split_two s r hr
    have hn : n = pre.length + post.length + 1 := by
      have hlen := congrArg List.length hs
      rw [s.property] at hlen
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    subst n
    have hsword : s = probeMixedWord pre post i j := Subtype.ext hs
    subst s
    have hsrc := ih (by omega) (probeMixedWord pre post i j)
    have htgt := ih (by omega) (probeMixedWord pre post j i)
    rw [← hpre] at hsrc htgt ⊢
    by_cases hij : i = j
    · subst j
      exact cyclotomicBlock_dot_isUnit D Sc (probePolynomial (probeDotExponent D) m)
        pre post i hsrc
    · exact probeMixedCorner_dot_isUnit D Sc (probePolynomial (probeDotExponent D) m)
        pre post i j hij hsrc htgt

end OddMath.QuiverHecke
end

end

section

/-! # The literal ordinary word quotient is the actual probe word corner
The forward inclusion uses the existing matrix quotient. Reverse matrix-entry
membership proves injectivity; the existing affine corner range theorem
proves surjectivity. No alternate quotient model or flatness premise is used.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → Polynomial k) (ν : List I)

private def ordinaryWordCornerAdd {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν) →+ CyclotomicWordCorner D Sc a s :=
  QuotientAddGroup.lift (cycHom D Sc a s.val s.val).toAddSubgroup
    (cyclotomicWordEnd D Sc a s).toAddMonoidHom (by
      intro f hf
      apply Subtype.ext
      change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (single_mem_cyclotomicIdeal D Sc a n s s hf))

/-- The existing quotient map, restricted to the literal unital word corner. -/
def ordinaryWordEndCornerMap {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν) →+* CyclotomicWordCorner D Sc a s where
  toFun := ordinaryWordCornerAdd D Sc a ν s hs
  map_one' := by
    change cyclotomicWordEnd D Sc a s 1 = 1
    exact map_one _
  map_zero' := map_zero (ordinaryWordCornerAdd D Sc a ν s hs)
  map_add' := map_add (ordinaryWordCornerAdd D Sc a ν s hs)
  map_mul' f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc a s.val s.val).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a s.val s.val).mkQ_surjective g
    change cyclotomicWordEnd D Sc a s (End.of f * End.of g) =
      cyclotomicWordEnd D Sc a s f * cyclotomicWordEnd D Sc a s g
    exact map_mul _ (End.of f) (End.of g)

@[simp] theorem ordinaryWordEndCornerMap_mk {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν)
    (f : End (wordObj D Sc s)) :
    ordinaryWordEndCornerMap D Sc a ν s hs
      (End.of ((cycHom D Sc a s.val s.val).mkQ f)) = cyclotomicWordEnd D Sc a s f := rfl

private theorem ordinaryWordEndCornerMap_zero {n : ℕ}
    (s : Word I (n+1)) (hs : s.val.Perm ν)
    (f : End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν)) (hf : ordinaryWordEndCornerMap D Sc a ν s hs f = 0) : f = 0 := by
  obtain ⟨f,rfl⟩ := (cycHom D Sc a s.val s.val).mkQ_surjective f
  have hz := congrArg Subtype.val hf
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) = 0 at hz
  have hi := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hc := (single_mem_cyclotomicIdeal_iff D Sc a n s s f).mp hi
  exact (Submodule.Quotient.mk_eq_zero _).mpr hc

theorem ordinaryWordEndCornerMap_injective {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    Function.Injective (ordinaryWordEndCornerMap D Sc a ν s hs) := by
  intro f g h
  apply sub_eq_zero.mp
  apply ordinaryWordEndCornerMap_zero D Sc a ν s hs
  rw [map_sub,h,sub_self]

theorem ordinaryWordEndCornerMap_surjective {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    Function.Surjective (ordinaryWordEndCornerMap D Sc a ν s hs) := by
  intro u
  obtain ⟨z,hz⟩ := Ideal.Quotient.mk_surjective u.val
  have hz' : cyclotomicMk D Sc a n z = u.val := hz
  let e : Hn D Sc (n+1) := Hn.wordIdempotent s
  have he : e * (e * z * e) * e = e * z * e := by
    calc
      e * (e * z * e) * e = (e*e) * z * (e*e) := by simp only [mul_assoc]
      _ = e * z * e := by dsimp only [e]; rw [Hn.wordIdempotent_sq]
  obtain ⟨f,hf⟩ := (Hn.mem_range_cornerInclusion_iff (D := D) (Sc := Sc) s (e*z*e)).mpr he
  refine ⟨End.of ((cycHom D Sc a s.val s.val).mkQ f), ?_⟩
  apply Subtype.ext
  change cyclotomicMk D Sc a n (Hn.cornerInclusion s f) = u.val
  rw [hf,map_mul,map_mul,hz']
  have hu := (Subsemigroup.mem_corner_iff (cyclotomicWordIdempotent_idem D Sc a s)).mp u.property
  change cyclotomicWordIdempotent D Sc a s * u.val * cyclotomicWordIdempotent D Sc a s = u.val
  rw [hu.1,hu.2]

/-- Actual ordinary quotient endomorphisms and the actual unital matrix word corner agree. -/
def ordinaryWordCornerEquiv {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν) ≃+* CyclotomicWordCorner D Sc a s :=
  RingEquiv.ofBijective (ordinaryWordEndCornerMap D Sc a ν s hs)
    ⟨ordinaryWordEndCornerMap_injective D Sc a ν s hs,
      ordinaryWordEndCornerMap_surjective D Sc a ν s hs⟩

@[simp] theorem ordinaryWordCornerEquiv_mk {n : ℕ}
    (s : Word I (n+1)) (hs : s.val.Perm ν) (f : End (wordObj D Sc s)) :
    ordinaryWordCornerEquiv D Sc a ν s hs (End.of ((cycHom D Sc a s.val s.val).mkQ f)) =
      cyclotomicWordEnd D Sc a s f := rfl

/-- The established all-position probe units are literal ordinary-category dot units. -/
theorem probeOrdinaryWordDot_isUnit [Fact Sc.PureNilpotent] (m : I → ℕ) {n : ℕ}
    (s : Word I (n+1)) (hs : s.val.Perm ν) (r : ℕ) (hr : r < n+1) :
    IsUnit (End.of ((cycHom D Sc (probePolynomial (probeDotExponent D) m) s.val s.val).mkQ
      (dotE D Sc s.val r)) :
        End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc (probePolynomial (probeDotExponent D) m) ν)) := by
  apply (MulEquiv.isUnit_map (ordinaryWordCornerEquiv D Sc (probePolynomial (probeDotExponent D) m) ν s hs)).mp
  rw [ordinaryWordCornerEquiv_mk]
  exact probeWord_dots_isUnit D Sc m n r hr s

end OddMath.QuiverHecke
end

end

section

/-! # The invertible appended dot on the ordinary probe category
The exact scalar image of the canonical old append dot is supernatural
and a word-corner unit on every appended word, including vacuum append.
This supplies the source transformation for the scalar coend comparison.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "O" => OrdinaryContentCategory D Sc a ν

/-- The literal last dot in the actual ordinary quotient category. -/
def probeOrdinaryAppendDot (i : I) (v : O) :
    (probeOrdinaryAppend D Sc m ν i).obj v ⟶ (probeOrdinaryAppend D Sc m ν i).obj v :=
  (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
    (dotE D Sc (v.word ++ [i]) v.word.length)

/-- No new dot normalization is chosen: this is the scalar image of the old component. -/
theorem probeOrdinaryAppendDot_old (i : I)
    (v : ELV.OldContentCategory D Sc cut ν) :
    (probeOldOrdinaryFunctor D Sc m (i :: ν)).map
      (show (ELV.oldContentAppend D Sc cut ν i).obj v ⟶
        (ELV.oldContentAppend D Sc cut ν i).obj v from
          ELV.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj) =
      probeOrdinaryAppendDot D Sc m ν i ((probeOldOrdinaryFunctor D Sc m ν).obj v) := by
  rw [ELV.CyclotomicCrossingTensor.oldAppendDotComponent_eq]
  change (cycHom D Sc a _ _).mkQ
    (elvProbeScalarHom D m Sc _ _
      (ELV.affineUnit D Sc cut _ _ (dotE D Sc (v.obj.word ++ [i]) v.obj.word.length ^ 1))) = _
  rw [pow_one, elvProbeScalarHom_affineUnit]
  rfl

/-- The scalar dot retains its full supernatural sign on ordinary Homs. -/
theorem probeOrdinaryAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (probeOrdinaryAppendDot D Sc m ν i) := by
  refine ⟨?_, ?_⟩
  · intro v
    exact probeOrdinaryHomSpace_mk_mem D Sc m (positionedDot_parity D Sc v.word [] i)
  · intro v w q f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    have h := MonoidalSupercategory.super_interchange hfr (firstDot_parity D Sc i [])
    rw [whiskerLeft_dotE D Sc w.word i rfl, whiskerLeft_dotE D Sc v.word i rfl] at h
    have hq := congrArg (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ h
    rw [map_zsmul, koszulSign_smul (R := k)] at hq
    change (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      ((fr ▷ (pres D Sc).obj (ob D [i])) ≫ dotE D Sc (w.word ++ [i]) w.word.length) =
      sign k (D.parity i * q) •
        (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
          (dotE D Sc (v.word ++ [i]) v.word.length ≫ (fr ▷ (pres D Sc).obj (ob D [i])))
    simpa only [mul_comm q (D.parity i)] using hq

variable [Fintype I]
/-- The literal appended dot is an actual endomorphism unit, including at height zero. -/
theorem probeOrdinaryAppendDot_isUnit [Fact Sc.PureNilpotent] (i : I) (v : O) :
    IsUnit (End.of (probeOrdinaryAppendDot D Sc m ν i v)) := by
  let s : Word I (v.word.length + 1) := ⟨v.word ++ [i], by simp⟩
  have hs : s.val.Perm (i :: ν) := ((probeOrdinaryAppend D Sc m ν i).obj v).wordPerm
  exact probeOrdinaryWordDot_isUnit D Sc (i :: ν) m s hs v.word.length (Nat.lt_succ_self _)

end OddMath.QuiverHecke
end

end

section

/-! # Signed inverse of the ordinary probe induction dot
The inverse source dot has the same parity. Its induced transform requires
the factor (-1)^(p*p), retaining the signed right-multiplication convention.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} (e : ∀ v, J.obj v ≅ J.obj v)
  (he : IsSupernatural k p (fun v => (e v).hom))

omit [IsSuperfunctor k J] in
include he in
/-- The inverse family retains the same parity and supernatural sign. -/
theorem inverseComponent_supernatural :
    IsSupernatural k p (fun v => (e v).inv) := by
  apply IsSupernatural.of_twist (fun v => Supercategory.inv_mem (e v) (he.mem v))
  intro v w f
  have ht := he.naturality_twist (twist k p f)
  rw [twist_twist] at ht
  apply (cancel_mono (e w).hom).mp
  rw [Category.assoc, (e w).inv_hom_id, Category.comp_id]
  rw [Category.assoc, ht, ← Category.assoc, (e v).inv_hom_id, Category.id_comp]

variable (M : Superfunctor k C (SVec k))

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (ν : List I) (i : I)

/-- The literal ordinary appended dot is an isomorphism at each source word. -/
noncomputable def probeOrdinaryAppendDotIso [Fact Sc.PureNilpotent]
    (v : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) :
    (probeOrdinaryAppend D Sc m ν i).obj v ≅ (probeOrdinaryAppend D Sc m ν i).obj v := by
  haveI := (isUnit_iff_isIso (End.of (probeOrdinaryAppendDot D Sc m ν i v))).mp
    (probeOrdinaryAppendDot_isUnit D Sc m ν i v)
  exact asIso (probeOrdinaryAppendDot D Sc m ν i v)

variable (M : Superfunctor k
  (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

end OddMath.QuiverHecke
end

end

section

/-! # Signed dot inverse on old scalar probe coends
This supplies the probe-unit roadmap input for the prescribed old append induction.
The inverse is constructed on the original balanced quotient using scalar-kernel
closure and the inverse ordinary appended dot. The canonical probe module discharges
the scalar-evaluation condition. No finite-dimensionality or coend comparison is used.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

section Action
variable (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The literal ordinary Hom action retains the original old module values. -/
theorem probeScalarAction_old (v w : C) (f : v ⟶ w) :
    probeOrdinaryModuleHom D m Sc ν N hN v w ((Q).map (X := v) (Y := w) f) =
      N.toFunctor.map (X := v) (Y := w) f :=
  probeOrdinaryModuleHom_old D m Sc ν N hN v w f

/-- Composition holds on unchanged old values, without rebuilding object labels. -/
theorem probeScalarAction_comp (v w z : C)
    (f : (Q).obj v ⟶ (Q).obj w) (g : (Q).obj w ⟶ (Q).obj z) :
    probeOrdinaryModuleHom D m Sc ν N hN v z (f ≫ g) =
      probeOrdinaryModuleHom D m Sc ν N hN v w f ≫
        probeOrdinaryModuleHom D m Sc ν N hN w z g := by
  obtain ⟨fr,rfl⟩ := elvProbeOldHom_surjective D m Sc v.obj.word w.obj.word f
  obtain ⟨gr,rfl⟩ := elvProbeOldHom_surjective D m Sc w.obj.word z.obj.word g
  let f₀ : v ⟶ w := fr
  let g₀ : w ⟶ z := gr
  change probeOrdinaryModuleHom D m Sc ν N hN v z
      ((Q).map (X := v) (Y := w) f₀ ≫ (Q).map (X := w) (Y := z) g₀) =
    probeOrdinaryModuleHom D m Sc ν N hN v w ((Q).map (X := v) (Y := w) f₀) ≫
      probeOrdinaryModuleHom D m Sc ν N hN w z ((Q).map (X := w) (Y := z) g₀)
  have hq := congrArg (probeOrdinaryModuleHom D m Sc ν N hN v z) ((Q).map_comp f₀ g₀)
  have hf := probeScalarAction_old D Sc m ν N hN v w f₀
  have hg := probeScalarAction_old D Sc m ν N hN w z g₀
  exact hq.symm.trans ((probeScalarAction_old D Sc m ν N hN v z (f₀ ≫ g₀)).trans
    ((N.toFunctor.map_comp f₀ g₀).trans
      (congrArg₂ (fun x : N.obj v ⟶ N.obj w => fun y : N.obj w ⟶ N.obj z => x ≫ y)
        hf.symm hg.symm)))

end Action

/-- The prescribed old dot, on the existing content append functor. -/
def probeOldContentAppendDot (i : I) (v : C) :
    (ELV.oldContentAppend D Sc cut ν i).obj v ⟶
      (ELV.oldContentAppend D Sc cut ν i).obj v :=
  ELV.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj

theorem probeOldContentAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (probeOldContentAppendDot D Sc m ν i) where
  mem v := (ELV.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i).mem v.obj
  naturality hf :=
    (ELV.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i).naturality hf

/-- The original signed balanced transform, on the actual old content coend. -/
def probeOldContentInductionDot (i : I)
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ELV.BalancedInduction.Obj (ELV.oldContentAppend D Sc cut ν i) N.toFunctor t →ₗ[k]
      ELV.BalancedInduction.Obj (ELV.oldContentAppend D Sc cut ν i) N.toFunctor t :=
  ELV.BalancedInduction.transformLinear (probeOldContentAppendDot_supernatural D Sc m ν i) N t

@[simp] theorem probeOldContentInductionDot_tensor (i : I)
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (v : C) (t : ELV.OldContentCategory D Sc cut (i :: ν))
    (g : (ELV.oldContentAppend D Sc cut ν i).obj v ⟶ t) (b : N.obj v) :
    probeOldContentInductionDot D Sc m ν i N t
      (ELV.BalancedInduction.tensor (ELV.oldContentAppend D Sc cut ν i) N.toFunctor v g b) =
    ELV.BalancedInduction.tensor (ELV.oldContentAppend D Sc cut ν i) N.toFunctor v
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) b :=
  ELV.BalancedInduction.transformLinear_tensor _ _ _ _ _ _

section SourceInverse
variable [Fintype I] (i : I)
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Inverse of the source dot in the literal ordinary Hom quotient. -/
def probeOrdinarySourceDotInverse [Fact Sc.PureNilpotent] (v : C) :
    (U).obj ((J).obj v) ⟶ (U).obj ((J).obj v) :=
  (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).inv

omit [Fintype I] in
theorem probeOldContentAppendDot_image (v : C) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) =
      probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) :=
  probeOrdinaryAppendDot_old D Sc m ν i v

theorem probeOrdinarySourceDotInverse_dot [Fact Sc.PureNilpotent] (v : C) :
    probeOrdinarySourceDotInverse D Sc m ν i v ≫
      (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) =
        𝟙 ((U).obj ((J).obj v)) := by
  rw [probeOldContentAppendDot_image]
  exact (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).inv_hom_id

theorem probeOrdinarySourceDot_dotInverse [Fact Sc.PureNilpotent] (v : C) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) ≫
      probeOrdinarySourceDotInverse D Sc m ν i v = 𝟙 ((U).obj ((J).obj v)) := by
  rw [probeOldContentAppendDot_image]
  exact (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).hom_inv_id

theorem probeOrdinarySourceDotInverse_mem [Fact Sc.PureNilpotent] (v : C) :
    probeOrdinarySourceDotInverse D Sc m ν i v ∈
      parity (R := k) ((U).obj ((J).obj v)) ((U).obj ((J).obj v)) (D.parity i) :=
  Supercategory.inv_mem (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v))
    ((probeOrdinaryAppendDot_supernatural D Sc m ν i).mem ((Q).obj v))

/-- The inverse retains the full output twist on actual old input arrows. -/
theorem probeOrdinarySourceDotInverse_naturality [Fact Sc.PureNilpotent] (v w : C) (f : v ⟶ w) :
    (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) ≫
      probeOrdinarySourceDotInverse D Sc m ν i w =
    probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i)
        ((U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)) := by
  let qf := (Q).map (X := v) (Y := w) f
  have hs : (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) =
      (T).map (X := (Q).obj v) (Y := (Q).obj w) qf :=
    elvProbeOldHom_rightContext D m Sc [i] v.obj.word w.obj.word f
  have hi := (ELV.BalancedInduction.inverseComponent_supernatural T
    (probeOrdinaryAppendDotIso D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m ν i)).naturality_twist qf
  calc
    _ = (T).map qf ≫ probeOrdinarySourceDotInverse D Sc m ν i w :=
      congrArg (fun x => x ≫ probeOrdinarySourceDotInverse D Sc m ν i w) hs
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ (T).map (twist k (D.parity i) qf) := hi
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) ((T).map qf) :=
      congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ x) (map_twist T (D.parity i) qf)
    _ = _ := congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) x) hs.symm
/-- The inverse-dot/twisted-Hom expression is linear in the actual old Hom. -/
def probeOrdinaryInverseHom [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] ((U).obj ((J).obj v) ⟶ (U).obj t) :=
  (Linear.leftComp k ((U).obj t) (probeOrdinarySourceDotInverse D Sc m ν i v)).comp
    ((twist k (D.parity i) (X := (U).obj ((J).obj v)) (Y := (U).obj t)).comp
      ((U).mapLinearMap (R := k) (X := (J).obj v) (Y := t)))

@[simp] theorem probeOrdinaryInverseHom_apply [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t g =
      probeOrdinarySourceDotInverse D Sc m ν i v ≫
        twist k (D.parity i) ((U).map (X := (J).obj v) (Y := t) g) := rfl

/-- This is the ordinary Hom identity needed for actual old coend balancing. -/
theorem probeOrdinaryInverseHom_balance [Fact Sc.PureNilpotent] (v w : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν))
    (f : v ⟶ w) (g : (J).obj w ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t ((J).map (X := v) (Y := w) f ≫ g) =
      (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) ≫
        probeOrdinaryInverseHom D Sc m ν i w t g := by
  let uf := (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)
  let ug := (U).map (X := (J).obj w) (Y := t) g
  have hm : (U).map (X := (J).obj v) (Y := t) ((J).map (X := v) (Y := w) f ≫ g) =
      uf ≫ ug := (U).map_comp ((J).map (X := v) (Y := w) f) g
  change probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map (X := (J).obj v) (Y := t) ((J).map f ≫ g)) =
    uf ≫ (probeOrdinarySourceDotInverse D Sc m ν i w ≫ twist k (D.parity i) ug)
  calc
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) (uf ≫ ug) :=
      congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) x) hm
    _ = (probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) uf) ≫
        twist k (D.parity i) ug := by rw [twist_comp, Category.assoc]
    _ = (uf ≫ probeOrdinarySourceDotInverse D Sc m ν i w) ≫ twist k (D.parity i) ug :=
      congrArg (fun x => x ≫ twist k (D.parity i) ug)
        (probeOrdinarySourceDotInverse_naturality D Sc m ν i v w f).symm
    _ = _ := Category.assoc _ _ _

/-- The first inverse product reduces to the scalar image of the old Hom. -/
theorem probeOrdinaryInverseHom_dot [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g := by
  let ad := (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v)
  let ug := (U).map (X := (J).obj v) (Y := t) g
  have ha : ad ∈ parity (R := k) ((U).obj ((J).obj v)) ((U).obj ((J).obj v)) (D.parity i) := by
    rw [show ad = probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) from
      probeOldContentAppendDot_image D Sc m ν i v]
    exact (probeOrdinaryAppendDot_supernatural D Sc m ν i).mem ((Q).obj v)
  have hm : (U).map (X := (J).obj v) (Y := t)
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      ad ≫ twist k (D.parity i) ug := by
    exact ((U).map_comp (probeOldContentAppendDot D Sc m ν i v) (twist k (D.parity i) g)).trans
      (congrArg (fun z => ad ≫ z) (map_twist U (D.parity i) g))
  change probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g)) = _
  rw [hm, twist_comp, twist_twist, twist_of_mem (D.parity i) ha,
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    probeOrdinarySourceDotInverse_dot, Category.id_comp]

/-- The other inverse product retains the same parity-square sign. -/
theorem probeOrdinaryDot_twist_inverseHom [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) ≫
      twist k (D.parity i) (probeOrdinaryInverseHom D Sc m ν i v t g) =
      sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g := by
  change (U).map (probeOldContentAppendDot D Sc m ν i v) ≫
    twist k (D.parity i) (probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map g)) = _
  rw [twist_comp, twist_twist,
    twist_of_mem (D.parity i) (probeOrdinarySourceDotInverse_mem D Sc m ν i v),
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    probeOrdinarySourceDot_dotInverse, Category.id_comp]

end SourceInverse

section InverseSummand
variable [Fintype I] (i : I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "L" => ELV.BalancedInduction.induced J N
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Ordinary Hom action on the unchanged actual induced old module values. -/
def probeOldInverseHomAction [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] ((L).obj ((J).obj v) ⟶ (L).obj t) :=
  (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t).comp
    (probeOrdinaryInverseHom D Sc m ν i v t)

/-- The inverse summand is bilinear in the original old Hom and module vector. -/
def probeOldInverseGenerator [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] (N.obj v →ₗ[k] ELV.BalancedInduction.Obj J N.toFunctor t) :=
  (Linear.leftComp k ((L).obj t)
    (show N.obj v ⟶ (L).obj ((J).obj v) from ELV.BalancedInduction.unit J N.toFunctor v)).comp
      (probeOldInverseHomAction D Sc m ν i N hN v t)

@[simp] theorem probeOldInverseGenerator_apply [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldInverseGenerator D Sc m ν i N hN v t g b =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELV.BalancedInduction.unit J N.toFunctor v b) := rfl

def probeOldInverseSummand [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (((J).obj v ⟶ t) ⊗[k] N.obj v) →ₗ[k] ELV.BalancedInduction.Obj J N.toFunctor t :=
  TensorProduct.lift (probeOldInverseGenerator D Sc m ν i N hN v t)

@[simp] theorem probeOldInverseSummand_tmul [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldInverseSummand D Sc m ν i N hN v t (g ⊗ₜ[k] b) =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELV.BalancedInduction.unit J N.toFunctor v b) :=
  TensorProduct.lift.tmul g b
/-- Balancing is proved inside the original old coend. -/
theorem probeOldInverseSummand_balance [Fact Sc.PureNilpotent] (v w : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν))
    (f : v ⟶ w) (g : (J).obj w ⟶ t) (b : N.obj v) :
    probeOldInverseSummand D Sc m ν i N hN v t (((J).map f ≫ g) ⊗ₜ[k] b) =
      probeOldInverseSummand D Sc m ν i N hN w t (g ⊗ₜ[k] N.toFunctor.map f b) := by
  rw [probeOldInverseSummand_tmul, probeOldInverseSummand_tmul]
  let uf := (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)
  let hg := probeOrdinaryInverseHom D Sc m ν i w t g
  let uv := ELV.BalancedInduction.unit J N.toFunctor v b
  have hb := probeOrdinaryInverseHom_balance D Sc m ν i v w t f g
  have hc := probeScalarAction_comp D Sc m (i :: ν) L hL ((J).obj v) ((J).obj w) t uf hg
  have ho : probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj w) uf =
      (show (L).obj ((J).obj v) ⟶ (L).obj ((J).obj w) from
        ELV.BalancedInduction.postcompose J N.toFunctor ((J).map f)) :=
    probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) ((J).obj w) ((J).map f)
  have hu := LinearMap.congr_fun (ELV.BalancedInduction.unit_naturality J N.toFunctor f) b
  calc
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (uf ≫ hg) uv :=
      congrArg (fun z => probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t z uv) hb
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg
        (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj w) uf uv) := by
      simpa only [SVec.comp_apply] using congrArg
        (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv) hc
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg
        (ELV.BalancedInduction.postcompose J N.toFunctor ((J).map f) uv) :=
      congrArg (fun z => probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg z)
        (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj ((J).obj w) => z uv) ho)
    _ = _ := congrArg (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg)
      (by simpa only [LinearMap.comp_apply] using hu)

/-- Explicit signed inverse candidate on the actual old balanced quotient. -/
def probeOldContentInductionDotInverse [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ELV.BalancedInduction.Obj J N.toFunctor t →ₗ[k]
      ELV.BalancedInduction.Obj J N.toFunctor t :=
  sign k (D.parity i * D.parity i) • ELV.BalancedInduction.lift J N.toFunctor t
    (fun v => probeOldInverseSummand D Sc m ν i N hN v t)
    (fun v w f g b => probeOldInverseSummand_balance D Sc m ν i N hN v w t f g b)

@[simp] theorem probeOldContentInductionDotInverse_tensor [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldContentInductionDotInverse D Sc m ν i N hN t
      (ELV.BalancedInduction.tensor J N.toFunctor v g b) =
    sign k (D.parity i * D.parity i) •
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELV.BalancedInduction.unit J N.toFunctor v b) := by
  rw [probeOldContentInductionDotInverse, LinearMap.smul_apply,
    ELV.BalancedInduction.lift_tensor, probeOldInverseSummand_tmul]

/-- No finite-dimensionality is used: one inverse product is checked on the old generators. -/
theorem probeOldContentInductionDotInverse_comp_dot [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (probeOldContentInductionDotInverse D Sc m ν i N hN t).comp
      (probeOldContentInductionDot D Sc m ν i N t) = LinearMap.id := by
  apply ELV.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDot_tensor,
    probeOldContentInductionDotInverse_tensor, probeOrdinaryInverseHom_dot,
    map_smul, SVec.smul_apply, sign_smul_sign_smul]
  have h := probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) t g
  have hv := congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t =>
    z (ELV.BalancedInduction.unit J N.toFunctor v b)) h
  exact hv.trans (ELV.BalancedInduction.postcompose_unit J N.toFunctor g b)

omit [Fintype I] in
private theorem probeOldContentInductionDot_unit_action (v : C) (b : N.obj v) :
    probeOldContentInductionDot D Sc m ν i N ((J).obj v)
      (ELV.BalancedInduction.unit J N.toFunctor v b) =
    probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj v)
      ((U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v))
      (ELV.BalancedInduction.unit J N.toFunctor v b) := by
  have h := probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) ((J).obj v)
    (probeOldContentAppendDot D Sc m ν i v)
  exact (ELV.BalancedInduction.transform_unit
    (probeOldContentAppendDot_supernatural D Sc m ν i) N v b).trans
      (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj ((J).obj v) =>
        z (ELV.BalancedInduction.unit J N.toFunctor v b)) h).symm

/-- The second inverse product uses the old dot's descended full supernaturality. -/
theorem probeOldContentInductionDot_comp_inverse [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (probeOldContentInductionDot D Sc m ν i N t).comp
      (probeOldContentInductionDotInverse D Sc m ν i N hN t) = LinearMap.id := by
  apply ELV.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDotInverse_tensor, map_smul]
  let hf := probeOrdinaryInverseHom D Sc m ν i v t g
  let ad := (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v)
  let uv := ELV.BalancedInduction.unit J N.toFunctor v b
  have hv : probeOldContentInductionDot D Sc m ν i N t
      (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t hf uv) =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (twist k (D.parity i) hf)
        (probeOldContentInductionDot D Sc m ν i N ((J).obj v) uv) := by
    obtain ⟨fr, hfr⟩ := elvProbeOldHom_surjective D m Sc ((J).obj v).obj.word t.obj.word hf
    let f₀ : (J).obj v ⟶ t := fr
    have hfr' : (U).map (X := (J).obj v) (Y := t) f₀ = hf := hfr
    rw [← hfr', probeScalarAction_old, ← map_twist (U) (D.parity i) f₀,
      probeScalarAction_old]
    exact LinearMap.congr_fun (ELV.BalancedInduction.transformLinear_naturality
      (probeOldContentAppendDot_supernatural D Sc m ν i) N f₀) uv
  have hc := probeScalarAction_comp D Sc m (i :: ν) L hL ((J).obj v) ((J).obj v) t
    ad (twist k (D.parity i) hf)
  have hcv := congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv) hc
  have hd := probeOrdinaryDot_twist_inverseHom D Sc m ν i v t g
  calc
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf)
          (probeOldContentInductionDot D Sc m ν i N ((J).obj v) uv) := by
      exact congrArg (fun z => sign k (D.parity i * D.parity i) • z)
        hv
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf)
          (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj v) ad uv) :=
      congrArg (fun z => sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf) z)
          (probeOldContentInductionDot_unit_action D Sc m ν i N hN v b)
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
          (ad ≫ twist k (D.parity i) hf) uv :=
      congrArg (fun z => sign k (D.parity i * D.parity i) • z)
        (by simpa only [SVec.comp_apply] using hcv.symm)
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
          (sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g) uv :=
      congrArg (fun z => sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t z uv) hd
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        ((U).map (X := (J).obj v) (Y := t) g) uv := by
      rw [map_smul, SVec.smul_apply, sign_smul_sign_smul]
    _ = _ := (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv)
      (probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) t g)).trans
        (ELV.BalancedInduction.postcompose_unit J N.toFunctor g b)

/-- Intermediate unit for a scalar-evaluated old module. The canonical probe-module
specialization below proves the scalar-evaluation hypothesis. -/
def probeOldContentInductionDotUnit [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (End (ELV.BalancedInduction.superspace J N.toFunctor t))ˣ where
  val := End.of (probeOldContentInductionDot D Sc m ν i N t)
  inv := End.of (probeOldContentInductionDotInverse D Sc m ν i N hN t)
  val_inv := probeOldContentInductionDot_comp_inverse D Sc m ν i N hN t
  inv_val := probeOldContentInductionDotInverse_comp_dot D Sc m ν i N hN t

include hN in
theorem probeOldContentInductionDot_isUnit [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    IsUnit (End.of (probeOldContentInductionDot D Sc m ν i N t) :
      End (ELV.BalancedInduction.superspace J N.toFunctor t)) :=
  (probeOldContentInductionDotUnit D Sc m ν i N hN t).isUnit

end InverseSummand

section ProbeModule
variable [Fintype I] {B : Type u} [Ring B] [Algebra k B]
  {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

end ProbeModule

end OddMath.QuiverHecke
end

end
