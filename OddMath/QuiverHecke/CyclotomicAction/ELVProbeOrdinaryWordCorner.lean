import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryCategory
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicMatrixEntries
import OddMath.QuiverHecke.CyclotomicAction.ProbeAllUnits

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
