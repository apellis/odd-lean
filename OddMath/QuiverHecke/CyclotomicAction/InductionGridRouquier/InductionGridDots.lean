import OddMath.Algebra.FiniteSupermoduleFamily
import OddMath.Algebra.FiniteSupermoduleInverseRows
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed.InductionMixedCrossTensor
import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation.KernelMatrices
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords.RouquierData
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend.WeightedMatrixRows
import OddMath.SKM.AugmentedInverseProfile
import OddMath.SKM.RouquierBoundary

/-!
# Induction grid rouquier

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Dots under the induction-composition comparison

Brundan–Ellis (1.7)–(1.8): the chosen composition comparison transports
inner and outer module dots to the corresponding whiskered source arrows.
These module equations retain the given induced objects and ordinary maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]

private theorem module_square_of_total
    {M N : Superfunctor k B (SVec k)} (a : End M) (e : M ⟶ N) (b : End N)
    (h : ∀ w, SVec.toLinearMap (e.total w) ∘ₗ SVec.toLinearMap (a.total w) =
      SVec.toLinearMap (b.total w) ∘ₗ SVec.toLinearMap (e.total w)) :
    a ≫ e = e ≫ b := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  exact LinearMap.congr_fun (h w) x

private theorem induction_map_total
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {M N : Superfunctor k A (SVec k)} {p : ZMod 2} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) _ _ p) (w : B) :
    ((induction K).map f).total w = mapComponent K f p w := by
  have hm := Supercategory.map_mem (induction K) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

private theorem dot_total
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k)) (w : A) :
    (dotEnd J hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [dotEnd, SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2}

/-- Flattening intertwines induction of the inner dot with its source whisker. -/
theorem inductionComp_inner_dot
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction K).map (dotEnd J hα M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K).hom.app M ≫ dotEnd (J ⋙ K) (hα.whiskerRight K) M := by
  apply module_square_of_total
  intro w
  rw [induction_map_total K (dotEnd_mem J hα M), dot_total]
  have h := compForward_transform_inner K hα M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, dotEnd, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

/-- Flattening intertwines the outer dot with its source whisker. -/
theorem inductionComp_outer_dot
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    dotEnd K hβ ((induction J).obj M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K).hom.app M ≫ dotEnd (J ⋙ K) (hβ.whiskerLeft J) M := by
  apply module_square_of_total
  intro w
  rw [dot_total, dot_total]
  have h := compForward_transform_outer J hβ M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Distinct slides through the two chosen induction charts

Brundan–Ellis (1.8): the rectangular positive crossing retains the signed
dot slides through its two prescribed induction-composition charts.
Four categories and all four append functors remain independent.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem rectangular_slide_of_squares
    {k C : Type*} [CommRing k] [Category C] [Preadditive C] [Linear k C]
    {A A' B B' : C} (e : A ≅ A') (f : B ≅ B')
    (c : A' ⟶ B') (x : End B) (x' : End B') (y : End A) (y' : End A')
    (a : k) (hx : x ≫ f.hom = f.hom ≫ x')
    (hy : y ≫ e.hom = e.hom ≫ y') (hs : c ≫ x' = a • (y' ≫ c)) :
    (e.hom ≫ c ≫ f.inv) ≫ x = a • (y ≫ (e.hom ≫ c ≫ f.inv)) := by
  have hx' : x = f.hom ≫ x' ≫ f.inv := by
    calc
      x = (x ≫ f.hom) ≫ f.inv := by simp
      _ = f.hom ≫ x' ≫ f.inv := by rw [hx, Category.assoc]
  have hy' : y = e.hom ≫ y' ≫ e.inv := by
    calc
      y = (y ≫ e.hom) ≫ e.inv := by simp
      _ = e.hom ≫ y' ≫ e.inv := by rw [hy, Category.assoc]
  rw [hx', hy']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, Linear.comp_smul, Linear.smul_comp] using
    congrArg (fun z => e.hom ≫ z ≫ f.inv) hs

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {q : ZMod 2} {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ T).obj s}
  (hγ : IsSupernatural k q γ)

/-- The crossing intertwines the chosen inner target dot and outer source dot. -/
theorem rectangularCrossComponent_slide_inner_outer
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    {β : ∀ s, T.obj s ⟶ T.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (a : k)
    (hs : ∀ s, L.map (α s) ≫ γ s = a • (γ s ≫ β (K.obj s)))
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hγ N ≫ (induction L).map (dotEnd J hα N) =
      a • (dotEnd T hβ ((induction K).obj N) ≫ rectangularCrossComponent J K L T hγ N) := by
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  have he : rectangularCrossComponent J K L T hγ N =
      e.hom ≫ transformComponent hγ N ≫ f.inv := rfl
  have h := rectangular_slide_of_squares e f
    (transformComponent hγ N)
    ((induction L).map (dotEnd J hα N)) (transformComponent (hα.whiskerRight L) N)
    (dotEnd T hβ ((induction K).obj N)) (transformComponent (hβ.whiskerLeft K) N) a
    (inductionComp_inner_dot J L hα N) (inductionComp_outer_dot K T hβ N)
    (transformComponent_rectangular_slide (hα.whiskerRight L) hγ (hβ.whiskerLeft K) a hs N)
  rw [he]
  convert! h using 1

/-- The crossing also intertwines the chosen outer target dot and inner source dot. -/
theorem rectangularCrossComponent_slide_outer_inner
    {p : ZMod 2} {α : ∀ s, L.obj s ⟶ L.obj s}
    {β : ∀ s, K.obj s ⟶ K.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (a : k)
    (hs : ∀ s, α (J.obj s) ≫ γ s = a • (γ s ≫ T.map (β s)))
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hγ N ≫ dotEnd L hα ((induction J).obj N) =
      a • ((induction T).map (dotEnd K hβ N) ≫ rectangularCrossComponent J K L T hγ N) := by
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  have he : rectangularCrossComponent J K L T hγ N =
      e.hom ≫ transformComponent hγ N ≫ f.inv := rfl
  have h := rectangular_slide_of_squares e f
    (transformComponent hγ N)
    (dotEnd L hα ((induction J).obj N)) (transformComponent (hα.whiskerLeft J) N)
    ((induction T).map (dotEnd K hβ N)) (transformComponent (hβ.whiskerRight T) N) a
    (inductionComp_outer_dot J L hα N) (inductionComp_inner_dot K T hβ N)
    (transformComponent_rectangular_slide (hα.whiskerLeft J) hγ (hβ.whiskerRight T) a hs N)
  rw [he]
  convert! h using 1

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Quadratic transport through the chosen rectangular induction charts

Brundan–Ellis (1.7): signed source quadratics pass to whole module maps
through both prescribed composition charts. The source polynomial is
separate from the crossings; concrete applications must prove its relation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem conjugate_pair_comp {V : Type*} [Category V]
    {x x' y y' : V} (e : x ≅ x') (f : y ≅ y')
    (c : x' ⟶ y') (d : y' ⟶ x') :
    (e.hom ≫ c ≫ f.inv) ≫ (f.hom ≫ d ≫ e.inv) =
      e.hom ≫ (c ≫ d) ≫ e.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  {F G : C ⥤ E}
  [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  {p : ZMod 2} {a : ∀ s, F.obj s ⟶ G.obj s} {b : ∀ s, G.obj s ⟶ F.obj s}
  {Q : ∀ s, F.obj s ⟶ F.obj s}
  (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
  (hQ : IsSupernatural k 0 Q)
  (hs : ∀ s, sign k p • (a s ≫ b s) = Q s)

omit [IsSuperfunctor k F] [IsSuperfunctor k G] in
include ha hb hs in
/-- The literal signed source polynomial inherits even supernaturality. -/
theorem signedQuadratic_supernatural : IsSupernatural k 0 Q := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hc : IsSupernatural k 0 (fun s => a s ≫ b s) := by
    simpa only [hpp] using ha.comp hb
  have hsm : IsSupernatural k 0 (fun s => sign k p • (a s ≫ b s)) := {
    mem := fun s => Submodule.smul_mem _ _ (hc.mem s)
    naturality := by
      intro s t q f hf
      simp only [Linear.comp_smul, Linear.smul_comp]
      rw [hc.naturality hf]
      simp only [zero_mul, Supercategory.sign_zero, one_smul] }
  simpa only [hs] using hsm

include hs in
/-- The superopposite composition sign is absorbed by the signed source polynomial. -/
theorem transformComponent_signed_quadratic (N : Superfunctor k C (SVec k)) :
    transformComponent hb N ≫ transformComponent ha N = transformComponent hQ N := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hl (w : E) : transformLinear ha N w ∘ₗ transformLinear hb N w =
      transformLinear hQ N w := by
    rw [transformLinear_comp]
    apply hom_ext
    intro s g n
    simp only [LinearMap.smul_apply, transformLinear_tensor]
    change sign k (p * p) • tensor F N.toFunctor s
      ((a s ≫ b s) ≫ twist k (p + p) g) n =
      tensor F N.toFunctor s (Q s ≫ twist k 0 g) n
    rw [hpp, twist_zero, hsq, ← hs s, Linear.smul_comp]
    simp only [tensor, ← TensorProduct.smul_tmul', map_smul]
  apply Superfunctor.hom_ext
  intro r w
  have he := hl w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp,
      zero_add, add_zero] <;> exact he

section Rectangular
variable {A B : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ T).obj s}
  {β : ∀ s, (K ⋙ T).obj s ⟶ (J ⋙ L).obj s}
  {P : ∀ s, (K ⋙ T).obj s ⟶ (K ⋙ T).obj s}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)
  (hP : IsSupernatural k 0 P)
  (hsource : ∀ s, sign k p • (β s ≫ α s) = P s)

include hsource in
/-- Both selected flattenings cancel between the actual rectangular crossings. -/
theorem rectangularCrossComponent_signed_quadratic (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hα N ≫
      rectangularCrossComponent K J T L hβ N =
      (inductionComp K T).hom.app N ≫ transformComponent hP N ≫
        (inductionComp K T).inv.app N := by
  have he := transformComponent_signed_quadratic hβ hα hP hsource N
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  exact (conjugate_pair_comp e f (transformComponent hα N) (transformComponent hβ N)).trans
    (congrArg (fun c => e.hom ≫ c ≫ e.inv) he)
include hsource in
/-- The reverse crossing may retain its own propositionally equal parity label. -/
theorem rectangularCrossComponent_signed_quadratic_of_parity
    {q : ZMod 2} (hβ' : IsSupernatural k q β) (hpq : q = p)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hα N ≫
      rectangularCrossComponent K J T L hβ' N =
      (inductionComp K T).hom.app N ≫ transformComponent hP N ≫
        (inductionComp K T).inv.app N := by
  cases hpq
  exact rectangularCrossComponent_signed_quadratic J K L T hα hβ' hP hsource N

end Rectangular
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Ordered original-parameter polynomials in arbitrary induction dots

DeformedActionAssembly §6 (9): the generic balanced induction dot powers
realize the signed source evaluation with original coefficients. Arbitrary
source and target categories and all coefficient parities are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

/-- Evaluation of a source endomorphism against a fixed balanced generator. -/
def inductionEndTensorEval (N : Superfunctor k C (SVec k)) (w : E) (s : C)
    (g : F.obj s ⟶ w) (n : N.obj s) : End (F.obj s) →ₗ[k] Obj F N.toFunctor w where
  toFun a := tensor F N.toFunctor s (a ≫ g) n
  map_add' a b := by
    change F.obj s ⟶ F.obj s at a b
    change tensor F N.toFunctor s ((a + b) ≫ g) n =
      tensor F N.toFunctor s (a ≫ g) n + tensor F N.toFunctor s (b ≫ g) n
    simp only [Preadditive.add_comp, tensor, TensorProduct.add_tmul, map_add]
  map_smul' c a := by
    change F.obj s ⟶ F.obj s at a
    change tensor F N.toFunctor s ((c • a) ≫ g) n =
      c • tensor F N.toFunctor s (a ≫ g) n
    simp only [Linear.smul_comp, tensor, ← TensorProduct.smul_tmul', map_smul]

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)

/-- Supported powers retain only the quadratic sign of the original source evaluation. -/
theorem transformLinear_supported_power (N : Superfunctor k C (SVec k)) (w : E)
    (r : ℕ) (hr : (r : ZMod 2) * D.parity i = 0) (c : k)
    (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    (c • (transformLinear ha N w ^ r)) (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ)) * c) • (a s ^ r)) := by
  rw [LinearMap.smul_apply, transformLinear_pow_tensor, hr, twist_zero]
  change c • (sign k (D.parity i * (r / 2 : ℕ)) • tensor F N.toFunctor s ((a s ^ r) ≫ g) n) = _
  rw [map_smul, smul_smul, sign_eq_zsign, mul_comm c]
  rfl

/-- The ordered interior term uses support from the parameter axioms, not a new premise. -/
theorem transformLinear_pair_monomial (N : Superfunctor k C (SVec k)) (w : E)
    (r t : ℕ) (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    (Sc.s i j r t • ((transformLinear hb N w ^ t) * (transformLinear ha N w ^ r)))
      (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (t / 2 : ℕ)) * Sc.s i j r t) •
          (a s ^ r * b s ^ t)) := by
  by_cases hc : Sc.s i j r t = 0
  · simp [hc]
  · obtain ⟨hr, ht⟩ := elvParameter_support D Sc hc
    rw [LinearMap.smul_apply, Module.End.mul_apply, transformLinear_pow_tensor,
      map_smul, transformLinear_pow_tensor, hr, ht, twist_zero, twist_zero]
    change Sc.s i j r t • (sign k (D.parity i * (r / 2 : ℕ)) •
      (sign k (D.parity j * (t / 2 : ℕ)) •
        tensor F N.toFunctor s ((b s ^ t) ≫ (a s ^ r) ≫ g) n)) = _
    rw [map_smul]
    change _ = _ • tensor F N.toFunctor s (((a s ^ r * b s ^ t) : End (F.obj s)) ≫ g) n
    simp only [smul_smul, sign_eq_zsign, End.mul_def, Category.assoc]
    rw [mul_comm (Sc.s i j r t), ← SKM.zsign_add]

/-- The actual ordered dot polynomial evaluates the original signed source polynomial. -/
theorem transformLinear_pairPolynomial_tensor (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    orderedPairOperatorPolynomial D Sc i j (transformLinear ha N w) (transformLinear hb N w)
      (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n (elvSignedPairQuadEval D Sc i j (a s) (b s)) := by
  unfold orderedPairOperatorPolynomial elvSignedPairQuadEval
  split_ifs with hd
  · simp [inductionEndTensorEval, End.one_def]
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro t _
      exact transformLinear_pair_monomial F D Sc i j ha hb N w r t s g n
    · congr 1
      · exact transformLinear_supported_power F D i ha N w _
          (CyclotomicAction.dn_cast_mul_parity D hij) _ s g n
      · exact transformLinear_supported_power F D j hb N w _
          (CyclotomicAction.dn_cast_mul_parity D hij.symm) _ s g n
/-- Whole linear operators realize the signed polynomial, once its even naturality is proved. -/
theorem transformLinear_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc (R := End (F.obj s)) i j (a s) (b s)))
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear hQ N w =
      orderedPairOperatorPolynomial D Sc i j (transformLinear ha N w) (transformLinear hb N w) := by
  apply hom_ext
  intro s g n
  rw [transformLinear_tensor, twist_zero,
    transformLinear_pairPolynomial_tensor F D Sc i j ha hb hij N w s g n]
  rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Original-parameter quadratic polynomials through the chosen induction chart

DeformedActionAssembly §6 (9): the polynomial of the two independent
induction dots equals the signed source polynomial transported through
the prescribed composition isomorphism, as whole module endomorphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem transform_total {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {a : ∀ s, F.obj s ⟶ G.obj s}
    (ha : IsSupernatural k p a) (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent ha N).total w = transformLinear ha N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app, ite_true, ite_false,
      zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

/-- Pointwise equal source arrows have equal whole balanced induction maps. -/
theorem transformComponent_congr_pointwise {p : ZMod 2}
    {a b : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
    (h : ∀ s, a s = b s) (N : Superfunctor k C (SVec k)) :
    transformComponent ha N = transformComponent hb N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [transform_total, transform_total]
  apply hom_ext
  intro s g n
  rw [transformLinear_tensor, transformLinear_tensor, h s]

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)

/-- The original-parameter polynomial is an equality of whole module morphisms. -/
theorem transformComponent_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc (R := End (F.obj s)) i j (a s) (b s)))
    (N : Superfunctor k C (SVec k)) :
    transformComponent hQ N = orderedPairOperatorPolynomial (R := End (induced F N)) D Sc i j
      (transformComponent ha N) (transformComponent hb N) := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F N) →ₐ[k] Module.End k ((induced F N).obj w) :=
    (svecEndEvaluation ((induced F N).obj w)).comp (supernaturalEndEvaluation (induced F N) w)
  change (transformComponent hQ N).total w =
    ev (orderedPairOperatorPolynomial (R := End (induced F N)) D Sc i j (transformComponent ha N) (transformComponent hb N))
  rw [orderedPairOperatorPolynomial_map_hom]
  change (transformComponent hQ N).total w = orderedPairOperatorPolynomial (R := Module.End k ((induced F N).obj w)) D Sc i j
    ((transformComponent ha N).total w) ((transformComponent hb N).total w)
  rw [transform_total, transform_total, transform_total]
  exact transformLinear_pairPolynomial F D Sc i j ha hb hij hQ N w

section Conjugation
variable {V : Type*} [Category V] [Preadditive V] [Linear k V]
/-- The exact chosen chart transports the endomorphism algebra without reversing products. -/
def inductionEndConjugation {x y : V} (e : x ≅ y) : End y →ₐ[k] End x :=
  AlgHom.ofLinearMap
    { toFun := fun f => e.hom ≫ f ≫ e.inv
      map_add' := by
        intro f g
        change y ⟶ y at f g
        change e.hom ≫ (f + g) ≫ e.inv = (e.hom ≫ f ≫ e.inv) + (e.hom ≫ g ≫ e.inv)
        simp only [Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro r f
        change y ⟶ y at f
        change e.hom ≫ (r • f) ≫ e.inv = r • (e.hom ≫ f ≫ e.inv)
        simp only [Linear.comp_smul, Linear.smul_comp] }
    (by
      change e.hom ≫ (𝟙 y) ≫ e.inv = 𝟙 x
      simp only [Category.id_comp, Iso.hom_inv_id])
    (fun f g => by
      change e.hom ≫ (g ≫ f) ≫ e.inv = (e.hom ≫ g ≫ e.inv) ≫ (e.hom ≫ f ≫ e.inv)
      simp only [Category.assoc, Iso.inv_hom_id_assoc])

@[simp] theorem inductionEndConjugation_apply {x y : V} (e : x ≅ y) (f : End y) :
    inductionEndConjugation (k := k) e f = e.hom ≫ f ≫ e.inv := rfl

/-- A commuting dot square fixes the corresponding conjugated endomorphism. -/
theorem inductionEndConjugation_of_square {x y : V} (e : x ≅ y) (a : End x) (b : End y)
    (h : a ≫ e.hom = e.hom ≫ b) : inductionEndConjugation (k := k) e b = a := by
  change e.hom ≫ b ≫ e.inv = a
  have he := congrArg (fun f => f ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
end Conjugation

section Pair
variable {A : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {α : ∀ s, End (J.obj s)} {β : ∀ s, End (K.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)

/-- The chosen inner and outer induction dots give the original polynomial under flattening. -/
theorem inductionComp_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc
      (R := End ((J ⋙ K).obj s)) i j (K.map (α s)) (β (J.obj s))))
    (N : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app N ≫ transformComponent hQ N ≫ (inductionComp J K).inv.app N =
      orderedPairOperatorPolynomial (R := End (induced K (induced J N))) D Sc i j
        ((induction K).map (dotEnd J hα N)) (dotEnd K hβ ((induction J).obj N)) := by
  let e : induced K (induced J N) ≅ induced (J ⋙ K) N := (inductionComp J K).app N
  have h := transformComponent_pairPolynomial (J ⋙ K) D Sc i j
    (hα.whiskerRight K) (hβ.whiskerLeft J) hij hQ N
  have hc := congrArg (fun z : End (induced (J ⋙ K) N) => inductionEndConjugation (k := k) e z) h
  rw [orderedPairOperatorPolynomial_map_hom] at hc
  have h₁ : inductionEndConjugation (k := k) e (transformComponent (hα.whiskerRight K) N) =
      (induction K).map (dotEnd J hα N) :=
    inductionEndConjugation_of_square e _ _ (inductionComp_inner_dot J K hα N)
  have h₂ : inductionEndConjugation (k := k) e (transformComponent (hβ.whiskerLeft J) N) =
      dotEnd K hβ ((induction J).obj N) :=
    inductionEndConjugation_of_square e _ _ (inductionComp_outer_dot J K hβ N)
  rw [h₁, h₂, inductionEndConjugation_apply] at hc
  exact hc
end Pair
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Rectangular transformation squares for induction composition

Brundan–Ellis (1.9), the changing-category braid comparisons: the chosen
induction-composition isomorphisms intertwine the independent inner and
outer source transformations, with distinct source and target functors.
These entire module-map squares retain the supernaturality kernel twists.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]

private theorem rectangular_square_of_total
    {M₀ M₁ N₀ N₁ : Superfunctor k B (SVec k)}
    (f : M₀ ⟶ M₁) (e₀ : M₀ ⟶ N₀) (e₁ : M₁ ⟶ N₁) (g : N₀ ⟶ N₁)
    (h : ∀ w, SVec.toLinearMap (e₁.total w) ∘ₗ SVec.toLinearMap (f.total w) =
      SVec.toLinearMap (g.total w) ∘ₗ SVec.toLinearMap (e₀.total w)) :
    f ≫ e₁ = e₀ ≫ g := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  exact LinearMap.congr_fun (h w) x

private theorem rectangular_induction_map_total
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {M N : Superfunctor k A (SVec k)} {p : ZMod 2} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) _ _ p) (w : B) :
    ((induction K).map f).total w = mapComponent K f p w := by
  have hm := Supercategory.map_mem (induction K) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

private theorem rectangular_transform_total
    {J J' : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J'.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable (J J' : C ⥤ A)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The actual outer induction maps the inner transformation to its source whisker. -/
theorem inductionComp_inner_transform {p : ZMod 2}
    {α : ∀ s, J.obj s ⟶ J'.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction K).map (transformComponent hα M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J' K).hom.app M ≫ transformComponent (hα.whiskerRight K) M := by
  apply rectangular_square_of_total
  intro w
  rw [rectangular_induction_map_total K (transformComponent_mem hα M), rectangular_transform_total]
  have h := compForward_transform_inner K hα M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

/-- The independent outer transformation maps to its source whisker after flattening. -/
theorem inductionComp_outer_transform
    (K' : A ⥤ B) [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
    {p : ZMod 2} {β : ∀ s, K.obj s ⟶ K'.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hβ ((induction J).obj M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K').hom.app M ≫ transformComponent (hβ.whiskerLeft J) M := by
  apply rectangular_square_of_total
  intro w
  rw [rectangular_transform_total, rectangular_transform_total]
  have h := compForward_transform_outer J hβ M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
