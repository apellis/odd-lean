/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor

/-! # The lower-balanced cyclotomic crossing tensor

The source of the right vertical arrow in `DeformedCyclotomicTopRow.md` §4
is balanced over the lower cyclotomic category, not a crossing image.
The last equal-colour crossing defines a map from this tensor to the enlarged
cyclotomic quotient. No injectivity of that map is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace CyclotomicCrossingTensor

/-- Right append on the full old cyclotomic category. -/
def append (i : I) : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff where
  obj s := ⟨s.word ++ [i]⟩
  map {s t} := (ideal D Sc cutoff s.word t.word).mapQ
    (ideal D Sc cutoff (s.word ++ [i]) (t.word ++ [i]))
    (rightContext D Sc cutoff [i] s.word t.word)
    (fun _ hr => ideal_rightContext D Sc cutoff [i] hr)
  map_id s := by
    change (ideal D Sc cutoff _ _).mkQ (rightContext D Sc cutoff [i] _ _ (𝟙 _)) = _
    rw [rightContext_id]
    rfl
  map_comp {s t w} f g := by
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    change (ideal D Sc cutoff _ _).mkQ (rightContext D Sc cutoff [i] _ _ (f ≫ g)) =
      (ideal D Sc cutoff _ _).mkQ
        (rightContext D Sc cutoff [i] _ _ f ≫ rightContext D Sc cutoff [i] _ _ g)
    rw [rightContext_comp]

/-- Total-parity twist on quotient morphisms, with no change of objects. -/
def parityFunctor (p : ZMod 2) : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff where
  obj s := s
  map {s t} := oldTwist D Sc cutoff p s.word t.word
  map_id s := by
    change (ideal D Sc cutoff _ _).mkQ (twist k p (𝟙 _)) = _
    rw [twist_id]
    rfl
  map_comp {s t w} f g := by
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    change (ideal D Sc cutoff _ _).mkQ (twist k p (f ≫ g)) =
      (ideal D Sc cutoff _ _).mkQ (twist k p f ≫ twist k p g)
    rw [twist_comp]

/-- The parity-shifted quotient Hom space, using total coefficient parity. -/
def shiftedHom (p : ZMod 2) (v w : List I) : SVec k where
  carrier := Old D Sc cutoff v w
  odd := oldProj D Sc cutoff v w (1 + p)
  odd_comp_odd := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective b
    change (ideal D Sc cutoff v w).mkQ (proj k (1 + p) (proj k (1 + p) b)) = _
    rw [proj_proj]
    rfl

/-- The right coefficient module has a twisted left action and ordinary right action. -/
def coefficient (p : ZMod 2) (i : I) (v : List I) :
    OldCategory D Sc cutoff ⥤ SVec k where
  obj s := shiftedHom D Sc cutoff p v (s.word ++ [i])
  map {s t} r := oldComp D Sc cutoff v (s.word ++ [i]) (t.word ++ [i]) |>.flip
    ((append D Sc cutoff i).map ((parityFunctor D Sc cutoff p).map r))
  map_id s := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
    change (ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k p (𝟙 _))) = _
    rw [twist_id, rightContext_id, Category.comp_id]
    rfl
  map_comp {s t w} r r' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective r
    obtain ⟨r', rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective r'
    change (ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k p (r ≫ r'))) =
      (ideal D Sc cutoff _ _).mkQ
        ((b ≫ rightContext D Sc cutoff [i] _ _ (twist k p r)) ≫
          rightContext D Sc cutoff [i] _ _ (twist k p r'))
    rw [twist_comp, rightContext_comp, Category.assoc]

/-- Matrix-Hom component of `Be ⊗_D Πᵖ(eB)`, with its prescribed lower balance. -/
abbrev Source (i : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) (⟨t⟩ : OldCategory D Sc cutoff)

/-- A tensor in the prescribed source; neither factor is an image coordinate. -/
def tensor (i : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    Source D Sc cutoff i v t :=
  BalancedInduction.tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨s⟩ c b

/-- The literal crossing word on affine representatives, in diagram order. -/
def crossing (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      hom D Sc cutoff v (s ++ [i]) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) where
  toFun c :=
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ ∘ₗ
      (Linear.rightComp k _ (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c)) ∘ₗ rightContext D Sc cutoff [i] _ _
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      LinearMap.add_apply, map_add, Preadditive.comp_add]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      LinearMap.smul_apply, map_smul, Linear.comp_smul, RingHom.id_apply]

/-- Both cyclotomic ideals descend separately before imposing lower balance. -/
def pairing (i : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [i]) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  LinearMap.liftQ₂ _ _ (crossing D Sc cutoff i v s t)
    (by
      intro c hc
      apply LinearMap.ext
      intro b
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact comp_ideal D Sc cutoff _
        (comp_ideal D Sc cutoff _ (ideal_rightContext D Sc cutoff [i] hc)))
    (by
      intro b hb
      ext c
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ideal_comp D Sc cutoff (ideal_rightContext D Sc cutoff [i] hb) _)

@[simp] theorem pairing_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    pairing D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c)
      ((ideal D Sc cutoff _ _).mkQ b) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := rfl

/-- Lower cyclotomic balance retains the total-parity twist on the coefficient. -/
theorem pairing_balance (i : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i) i v).obj s) :
    pairing D Sc cutoff i v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      pairing D Sc cutoff i v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i) i v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] _ _ b ≫
      affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i) ≫
      rightContext D Sc cutoff [i] _ _ (rightContext D Sc cutoff [i] _ _ r ≫ c)) =
    (ideal D Sc cutoff _ _).mkQ
      (rightContext D Sc cutoff [i] _ _ (b ≫ rightContext D Sc cutoff [i] _ _
        (twist k (D.parity i) r)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s'.word i i) ≫
        rightContext D Sc cutoff [i] _ _ c)
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have h := crossLast_comp_rightContext D Sc cutoff i i r
  rw [hp] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i)), h]
  simp only [Category.assoc]

/-- The prescribed crossing column after both cyclotomic descent and lower balance. -/
def toCyclotomic (i : I) (v t : List I) : Source D Sc cutoff i v t →ₗ[k]
    Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (pairing D Sc cutoff i v s.word t))
    (fun s s' r c b => pairing_balance D Sc cutoff i v s s' ⟨t⟩ r c b)

@[simp] theorem toCyclotomic_tensor (i : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t (tensor D Sc cutoff i v s t c b) =
      pairing D Sc cutoff i v s t c b := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- In algebra order this is exactly `c τₙ b`, without a coefficient permutation. -/
theorem toCyclotomic_tensor_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t (tensor D Sc cutoff i v s t
      ((ideal D Sc cutoff _ _).mkQ c) ((ideal D Sc cutoff _ _).mkQ b)) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := by
  rw [toCyclotomic_tensor, pairing_mk]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
