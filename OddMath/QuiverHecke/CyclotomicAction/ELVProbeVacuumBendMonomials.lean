import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightNegativeCap
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirPostUnitStandard

/-! # Vacuum coordinates of the ordered mixed-bend monomials

SwappedHomInversion §3 (4)–(5): compare the prescribed negative pre-cap
and dotted post-unit before summing the finite padded Dx expansion.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction
universe u
local instance bendMonomialHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem unitColumn_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0) (r : ℕ) :
    unitDotColumn J hα M r ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα N r := by
  have hd (n : ℕ) : IsSupernatural k (n • p) (F := induction J) (G := induction J)
      (fun P => dotEnd J hα P ^ n) := by
    induction n with
    | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
        (isSupernatural_id (R := k) (F := induction J))
    | succ n ih =>
      simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using
        (transformComponent_supernatural hα).comp ih
  have hu := isSupernatural_of_natTrans (R := k) (adjunctionUnit J) (adjunctionUnit_mem J)
  have hs : IsSupernatural k (r • p) (F := 𝟭 (Superfunctor k C (SVec k)))
      (G := induction J ⋙ restriction J) (fun P => unitDotColumn J hα P r) := by
    simpa only [zero_add, unitDotColumn, adjunction] using
      hu.comp ((hd r).whiskerRight (restriction J))
  have h := hs.naturality hf
  simp only [mul_zero, sign_zero, one_smul] at h
  convert h.symm using 1 <;> rfl

private def shiftedPreRow {k : Type u} [CommRing k]
    {A B R : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A) (Z : A ⟶ R)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A) :
    (SKM.homPre (k := k) E).obj ((SKM.homParityShift (k := k) (C := B ⟶ R) σ).obj (F ≫ Z)) ⟶ Z :=
  z • (E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ Z)).hom ≫
    f ▷ (F ≫ Z) ≫ g ▷ Z)

private theorem negativeCap_row
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (x : X) {a b : X}
    (edge : -a + D.α i = -b) [IsIso (T.dot i edge)] (n : ℕ)
    (Z : T.obj (-a) ⟶ W x) :
    SKM.homPreNegativeCap T W i x edge n Z =
      shiftedPreRow (R := W x) (T.E i edge) (T.F i edge) Z
        (SKM.leftAdjParity D i (-a))
        (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
        (SKM.rouquierPower (inv (T.dot i edge)) n)
        (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) := by
  rw [SKM.homPreNegativeCap_coordinates]
  unfold shiftedPreRow
  erw [PiSCat.associator_inv, PiSCat.leftUnitor_hom, Category.comp_id, Category.id_comp]

private theorem shiftedPreRow_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    {A B : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A)
    (Z : A ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : A)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A)
    (hSrc : (((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ x) σ).obj
          (F ≫ Z))).obj N) δ =
      ((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ contentModuleTarget D Sc cutoff bound δ.1) σ).obj
          (F ≫ Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N) :
    ((shiftedPreRow (R := elvWeightSpace D Sc cutoff bound Λ x) E F Z σ z f g).total N) δ =
      eqToHom hSrc ≫ (shiftedPreRow (R := contentModuleTarget D Sc cutoff bound δ.1) E F
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)) σ z f g).total N := by
  fin_cases σ
  all_goals
    have hh : hSrc = rfl := Subsingleton.elim _ _
    rw [hh]
    simp only [eqToHom_refl, Category.id_comp]
    rfl

private theorem negativeCap_product
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b) [IsIso (T.dot i edge)]
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
          (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N)
    (n : ℕ) :
    (SKM.homPreNegativeCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homPreNegativeCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ))).total N := by
  rw [negativeCap_row, negativeCap_row]
  exact shiftedPreRow_block D Sc cutoff bound Λ x δ (T.E i edge) (T.F i edge) Z N
    (SKM.leftAdjParity D i (-a))
    (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
    (SKM.rouquierPower (inv (T.dot i edge)) n)
    (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) hSrc

private theorem negativeCap_product_input
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b) [IsIso (T.dot i edge)]
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (V : T.obj (-a) ⟶ contentModuleTarget D Sc cutoff bound δ.1)
    (hz : Z.comp (elvBlockEval D Sc cutoff bound Λ δ) = V)
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj V)).obj N)
    (n : ℕ) :
    (SKM.homPreNegativeCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homPreNegativeCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n V).total N ≫
        eqToHom (congrArg (fun U : T.obj (-a) ⟶ contentModuleTarget D Sc cutoff bound δ.1 => U.obj N) hz.symm) := by
  subst V
  simpa only [eqToHom_refl, Category.comp_id] using
    negativeCap_product D Sc cutoff bound Λ x δ T i edge Z N hSrc n

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I) {muP nuR : X} (edgeP : -ΛP + D.α i = -muP)
  (edgeR : -ΛR + D.α i = nuR) (β : I →₀ ℕ)
variable (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR (-ΛR))

/-- The output block functor retains the entire probe module. -/
def vacuumBendBlock : ProbeVacuumCap.modulePiCategory D Sc m ⟶ (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) :=
  H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))
/-- The selected module in the prescribed shifted post-pair. -/
def vacuumPostPairModule : ContentModules D Sc cutoff bound (0 : Multiset I) :=
  (((SKM.homContentPostF (probeOldWeightSpace D Sc m ΛP) (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR).obj
    ((SKM.homContentPostE (probeOldWeightSpace D Sc m ΛP) (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR).obj (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H))).obj (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)

/-- The canonical append/restrict target on the native regular probe. -/
def vacuumPostRegularModule : ContentModules D Sc cutoff bound (0 : Multiset I) :=
  (restriction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).obj ((induction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).obj (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)))

/-- The prescribed post-target comparison, stored successor-content
chart, and regular-input comparison, in chronological order. -/
def vacuumPostTarget :
    vacuumPostPairModule D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H ≅
      vacuumPostRegularModule D Sc m cutoff bound ΛR i H := by
  let e₁ := (totalEvaluation (regularProbe D Sc m ΛP) ⋙ Pi.eval
    (fun γ : WeightBlocks D ΛR (-ΛR) => ContentModules D Sc cutoff bound γ.1) (emptyBlock D ΛR)).mapIso
      (SKM.homContentPostTargetIso ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H))
  let e₂ := eqToIso (elvWeightFollowing_obj D Sc cutoff bound i ΛR edgeR (emptyBlock D ΛR) (((preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).obj (regularProbe D Sc m ΛP)))
  let e₃ := eqToIso (storedAppendUpper_obj D Sc cutoff bound (emptyBlock D ΛR).1 i
    (blockSucc D ΛR i edgeR (emptyBlock D ΛR)).1 (elvBlockSucc_content_eq D i ΛR edgeR (emptyBlock D ΛR)) ((((preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).obj (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)))
  let e₄ := (induction (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) ⋙ restriction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).mapIso
    (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).toFunctor.mapIso (eqToIso (emptyProbe_regular D Sc m ΛP)))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- At the empty reservoir block, the actual shifted post-cup becomes
the raw native unit/dot column, with the regular-input cast retained. -/
theorem vacuumBendPostCup_eq (r : ℕ) :
    ((SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    ((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)) ≫
      unitDotColumn (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) r := by
  have hp := reservoirPostCup_canonical D Sc cutoff bound ΛR hcR ((probeOldRouquierFamily D Sc m ΛP hcP)).obj i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) (regularProbe D Sc m ΛP) (emptyBlock D ΛR)
  have hn := unitColumn_even (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)))
    (Supercategory.map_mem (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))).toFunctor (eqToHom_mem_parity_zero (k := k) (emptyProbe_regular D Sc m ΛP))) r
  rw [unitDotColumn_eq_restrictedDotEnd] at hn
  have ht := congrArg (fun f => f ≫
    (restriction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).map ((induction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).map
      (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP))))) hp
  change _ = _ at ht
  simpa only [vacuumPostTarget, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso.hom, Functor.comp_map, totalEvaluation, Pi.eval, Category.assoc] using ht.trans hn

/-- Selecting the output block commutes with each branch of the prescribed
precomposition parity shift. -/
private theorem preSourceBlock_eq :
    (((SKM.homContentPreE (probeOldRouquierFamily D Sc m ΛP hcP)
        (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP).obj
      ((SKM.homContentPreF (probeOldRouquierFamily D Sc m ΛP hcP)
        (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP).obj
        (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H))).obj
      (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) =
    ((SKM.homContentPreE (probeOldRouquierFamily D Sc m ΛP hcP)
        (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (-ΛR) edgeP).obj
      ((SKM.homContentPreF (probeOldRouquierFamily D Sc m ΛP hcP)
        (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (-ΛR) edgeP).obj
        (preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
          (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H)))).obj (regularProbe D Sc m ΛP) := by
  simp only [SKM.homContentPreF, Functor.comp_obj, SKM.homParityShift]
  split_ifs <;> rfl

/-- The source chart retains the output-block comparison before the
normalized vacuum pre-cap source chart. -/
def vacuumPreBlockSourceIso [Fact Sc.PureNilpotent] :=
  eqToIso (preSourceBlock_eq D Sc m cutoff bound ΛP ΛR hcP i edgeP H) ≪≫
    vacuumPreSourceIso D Sc m ΛP hcP
      (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) (-ΛR) i edgeP
      (vacuumBendBlock D Sc m cutoff bound ΛR H)

local instance bendMonomialProbeDotIso [Fact Sc.PureNilpotent] : IsIso (((probeOldRouquierFamily D Sc m ΛP hcP)).dot i edgeP) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m ΛP hcP i edgeP)

private theorem negativeCap_block [Fact Sc.PureNilpotent] (n : ℕ) :
    ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP)
      (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n
      (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total
      (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) =
    eqToHom (preSourceBlock_eq D Sc m cutoff bound ΛP ΛR hcP i edgeP H) ≫
      (SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP)
        (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (-ΛR) edgeP n
        (preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
          (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H))).total (regularProbe D Sc m ΛP) := by
  have hz : (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H).comp
      (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)) =
    preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
      (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H) := rfl
  have h := negativeCap_product_input D Sc cutoff bound ΛR (-ΛR) (emptyBlock D ΛR)
    (probeOldRouquierFamily D Sc m ΛP hcP) i edgeP
    (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)
    (regularProbe D Sc m ΛP)
    (preCapInput D Sc m ΛP hcP (fun _ => contentModuleTarget D Sc cutoff bound (0 : Multiset I))
      (-ΛR) (vacuumBendBlock D Sc m cutoff bound ΛR H)) hz
    (preSourceBlock_eq D Sc m cutoff bound ΛP ΛR hcP i edgeP H) n
  have ht : congrArg (fun U : (probeOldRouquierFamily D Sc m ΛP hcP).obj (-ΛP) ⟶
      contentModuleTarget D Sc cutoff bound (0 : Multiset I) => U.obj (regularProbe D Sc m ΛP)) hz.symm = rfl :=
    Subsingleton.elim _ _
  rw [ht, eqToHom_refl, Category.comp_id] at h
  exact h

/-- Each prescribed negative pre-cap followed by a dotted post-unit is
the corresponding raw vacuum bend monomial, with no compatibility premise. -/
theorem vacuumBendMonomial_eq [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n r : ℕ) :
    ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ≫
            restrictedDotEnd (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ^ r := by
  have hp := vacuumBendPostCup_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H r
  have hn := vacuumPreNegativeCap_eq D Sc m ΛP hcP (fun _ => (contentModuleTarget D Sc cutoff bound (0 : Multiset I))) (-ΛR) i edgeP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) hP hi n
  have hc : ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      ((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)) =
      (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
        (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
          ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) := by
    rw [negativeCap_block D Sc m cutoff bound ΛP ΛR hcP i edgeP H n]
    dsimp only [vacuumBendBlock]
    rw [Category.assoc, hn]
    simp only [vacuumPreBlockSourceIso, Iso.trans_hom, eqToIso.hom,
      vacuumBendBlock, Category.assoc]
  rw [Superfunctor.comp_total]
  change (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
    ((SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hc, unitDotColumn_eq_restrictedDotEnd]
  simp only [Category.assoc]

/-- Even colour: each prescribed negative pre-cap followed by a dotted post-unit is
the corresponding raw vacuum bend monomial, with no compatibility premise. -/
theorem vacuumBendMonomial_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0)
    (n r : ℕ) :
    ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ≫
            restrictedDotEnd (contentAppend D Sc cutoff bound (0 : Multiset I) [i]) (canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i) (((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).obj (probeOldVacuumRegular D Sc m)) ^ r := by
  have hp := vacuumBendPostCup_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H r
  have hn := vacuumPreNegativeCap_even D Sc m ΛP hcP (fun _ => (contentModuleTarget D Sc cutoff bound (0 : Multiset I))) (-ΛR) i edgeP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) hP hi n
  have hc : ((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
      ((H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))).map (eqToHom (emptyProbe_regular D Sc m ΛP)) =
      (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
        (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)))) ^ n) ≫
          ProbeVacuumCap.shiftedPreCap D Sc m (contentModuleTarget D Sc cutoff bound (0 : Multiset I)) i hP (H.comp (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR))) := by
    rw [negativeCap_block D Sc m cutoff bound ΛP ΛR hcP i edgeP H n]
    dsimp only [vacuumBendBlock]
    rw [Category.assoc, hn]
    simp only [vacuumPreBlockSourceIso, Iso.trans_hom, eqToIso.hom,
      vacuumBendBlock, Category.assoc]
  rw [Superfunctor.comp_total]
  change (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP n (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR) ≫
    ((SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR)) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hc, unitDotColumn_eq_restrictedDotEnd]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
