/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Basic
import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross

/-! # Supernaturality of the swapped upward crossing

The image of the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, in the swapped Hom construction
(`OddMath/QuiverHecke/SwappedAssembly/Generators/Cross.lean`) is supernatural of parity
`pᵢ pⱼ`, entry by entry (`docs/Nondegeneracy/SwappedActionAssembly.md`, end of §3).

The reduction of a two-letter matrix to its components at sectors in general position is
`twoTwo_supernatural`. The components are composites of the factor crossings and dots of the
Rouquier families, whiskered by Hom-sector functors, of associators, of the comparisons of the
parity shifts and of the mixed interchange `J`; each is supernatural of its parity. The
polynomial `Q` is even: its monomials of odd parity have zero coefficient by the parity
conditions on the scalars `sᵢⱼ^{pq}` and on the `dᵢⱼ` (Brundan–Ellis (1.4), (1.6)).

For equal colours, the coefficient `a` of the mixed block is data; its supernaturality, of
parity `pᵢ`, is the hypothesis `CrossCoeff.IsSupernatural`.

Main declarations: `ProbeReservoir.twoTwo_supernatural`,
`ProbeReservoir.crossImage_supernatural`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct

universe u

section Generic

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D] [Supercategory R D]

theorem IsSupernatural.add {p : ZMod 2} {F G : C ⥤ D} {x y : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) (hy : IsSupernatural R p y) :
    IsSupernatural R p fun X => x X + y X where
  mem X := Submodule.add_mem _ (hx.mem X) (hy.mem X)
  naturality hf := by
    rw [Preadditive.comp_add, hx.naturality hf, hy.naturality hf, ← smul_add,
      Preadditive.add_comp]

theorem IsSupernatural.smul {p : ZMod 2} {F G : C ⥤ D} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) (r : R) : IsSupernatural R p fun X => r • x X where
  mem X := Submodule.smul_mem _ r (hx.mem X)
  naturality hf := by
    rw [Linear.comp_smul, hx.naturality hf, smul_comm, Linear.smul_comp]

theorem IsSupernatural.neg {p : ZMod 2} {F G : C ⥤ D} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) : IsSupernatural R p fun X => -x X where
  mem X := Submodule.neg_mem _ (hx.mem X)
  naturality hf := by
    rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]

theorem IsSupernatural.sum {p : ZMod 2} {F G : C ⥤ D} {ι : Type*} (s : Finset ι)
    {x : ι → ∀ X, F.obj X ⟶ G.obj X} (hx : ∀ a ∈ s, IsSupernatural R p (x a)) :
    IsSupernatural R p fun X => ∑ a ∈ s, x a X := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSupernatural_zero (R := R) p (F := F) (G := G)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsSupernatural.add (hx a (Finset.mem_insert_self a s))
      (ih fun b hb => hx b (Finset.mem_insert_of_mem hb))

theorem IsSupernatural.zsmul {p : ZMod 2} {F G : C ⥤ D} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) (n : ℤ) : IsSupernatural R p fun X => n • x X where
  mem X := zsmul_mem (hx.mem X) n
  naturality hf := by
    rw [Preadditive.comp_zsmul, hx.naturality hf, smul_comm, Preadditive.zsmul_comp]

theorem IsSupernatural.of_parity_eq {p q : ZMod 2} {F G : C ⥤ D}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x) (h : p = q) :
    IsSupernatural R q x := h ▸ hx

/-- Products of supernatural endomorphism families multiply in the order of `End`. -/
theorem IsSupernatural.mul {p q : ZMod 2} {F : C ⥤ D} [F.Additive] [F.Linear R]
    {x y : ∀ X, End (F.obj X)} (hx : IsSupernatural R p x) (hy : IsSupernatural R q y) :
    IsSupernatural R (p + q) fun X => x X * y X :=
  IsSupernatural.of_parity_eq (hy.comp hx) (add_comm q p)

theorem IsSupernatural.pow {p : ZMod 2} {F : C ⥤ D} [F.Additive] [F.Linear R]
    {x : ∀ X, End (F.obj X)} (hx : IsSupernatural R p x) (n : ℕ) :
    IsSupernatural R (n * p) fun X => x X ^ n := by
  induction n with
  | zero => simpa using isSupernatural_id (R := R) (F := F)
  | succ n ih =>
    simp only [pow_succ]
    exact IsSupernatural.of_parity_eq (IsSupernatural.mul ih hx) (by push_cast; ring)

theorem isSupernatural_one {F : C ⥤ D} [F.Linear R] :
    IsSupernatural R 0 fun X => (1 : End (F.obj X)) :=
  isSupernatural_id

end Generic

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]

/-! ## Comparisons of Hom functors -/

section HomFunctors

omit [∀ a b : B, PiSupercategory k (a ⟶ b)]

theorem homPreComp_hom_mem {a b c d : B} (E : a ⟶ b) (F : b ⟶ c) (Z : c ⟶ d) :
    (homPreComp (k := k) E F).hom.app Z ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E F Z)

theorem homPreComp_inv_mem {a b c d : B} (E : a ⟶ b) (F : b ⟶ c) (Z : c ⟶ d) :
    (homPreComp (k := k) E F).inv.app Z ∈ parity (R := k) _ _ 0 :=
  TwoSupercategory.associator_hom_mem (R := k) E F Z

theorem homSectorInterchange_inv_mem {a b c d : B} (E : a ⟶ b) (F : c ⟶ d) (Z : b ⟶ c) :
    (homSectorInterchange (k := k) E F).inv.app Z ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E Z F)

end HomFunctors

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A two-morphism between composites, reassociated on both sides and whiskered by the
argument, is supernatural of its parity on the precomposition functors. -/
theorem homPreReassoc_supernatural {a b b' c d : B} (E₁ : a ⟶ b) (E₂ : b ⟶ c)
    (E₂' : a ⟶ b') (E₁' : b' ⟶ c) {p : ZMod 2} (η : E₁ ≫ E₂ ⟶ E₂' ≫ E₁')
    (hη : η ∈ parity (R := k) _ _ p) :
    IsSupernatural k p
      (F := homPre (k := k) (c := d) E₂ ⋙ homPre (k := k) E₁)
      (G := homPre (k := k) (c := d) E₁' ⋙ homPre (k := k) E₂')
      (fun Z => (associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₂' E₁' Z).hom) := by
  have hA := isSupernatural_of_natTrans (R := k) (homPreComp (k := k) (d := d) E₁ E₂).hom
    (homPreComp_hom_mem E₁ E₂)
  have hB := (homPreTransform (k := k) (c := d) η hη).isSupernatural p
  have hC := isSupernatural_of_natTrans (R := k) (homPreComp (k := k) (d := d) E₂' E₁').inv
    (homPreComp_inv_mem E₂' E₁')
  have := hA.comp (hB.comp hC)
  simp only [add_zero, zero_add] at this
  refine IsSupernatural.of_eq_conj rfl rfl this _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp [homPreComp, homPreTransform]

/-- **The mixed interchange `J` is supernatural**, of the sum of the two shift parities. -/
theorem homMixedInterchange_supernatural {a b c d : B} (E : a ⟶ b) (F : c ⟶ d)
    (κ τ : ZMod 2) :
    IsSupernatural k (κ + τ)
      (F := homPost (k := k) F ⋙ homParityShift (k := k) κ ⋙ homPre (k := k) E)
      (G := homPre (k := k) E ⋙ homPost (k := k) F ⋙ homParityShift (k := k) τ)
      (fun Z => (homMixedInterchange (k := k) E F κ τ Z).hom) := by
  have hA := ((homParityShiftDatum (k := k) κ).supernatural.whiskerLeft
    (homPost (k := k) (a := b) F)).whiskerRight (homPre (k := k) E)
  have hB := isSupernatural_of_natTrans (R := k) (homSectorInterchange (k := k) E F).inv
    (homSectorInterchange_inv_mem E F)
  have hC := (isSupernatural_iso_inv (k := k)
    (F := homParityShift (k := k) (C := a ⟶ d) τ) (G := 𝟭 _)
    (fun Z => (homParityShiftDatum (k := k) (C := a ⟶ d) τ).iso Z)
    (homParityShiftDatum (k := k) (C := a ⟶ d) τ).supernatural).whiskerLeft
      (homPre (k := k) E ⋙ homPost (k := k) (a := a) F)
  have := hA.comp (hB.comp hC)
  simp only [zero_add] at this
  exact this

/-! ## Parity-shift comparisons -/

section ParityShift

variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  [PiSupercategory k C]

/-- The comparison of two successive parity shifts with a single shift is even. -/
theorem homParityShiftAdd_hom_mem (p q : ZMod 2) (Z : C) :
    (homParityShiftAdd (k := k) (C := C) p q).hom.app Z ∈ parity (R := k) _ _ 0 := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl <;>
  rcases (show q = 0 ∨ q = 1 by fin_cases q; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · simpa [homParityShiftAdd, homParityShift] using Supercategory.id_mem (R := k) Z
  · simpa [homParityShiftAdd, homParityShift] using
      Supercategory.id_mem (R := k) ((PiSupercategory.pi (R := k)).obj Z)
  · simpa [homParityShiftAdd, homParityShift] using
      Supercategory.id_mem (R := k) ((PiSupercategory.pi (R := k)).obj Z)
  · simpa [homParityShiftAdd, homParityShift] using PiSupercategory.ξ_hom_mem (R := k) Z

variable {C' : Type*} [Category C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  [PiSupercategory k C']

/-- Moving a parity shift past a superfunctor is even. -/
theorem homParityShiftCommute_inv_mem (G : C ⥤ C') [G.Additive] [G.Linear k]
    [IsSuperfunctor k G] (p : ZMod 2) (Z : C) :
    (homParityShiftCommute (k := k) G p).inv.app Z ∈ parity (R := k) _ _ 0 := by
  rw [homParityShiftCommute_inv_app]
  have h := Supercategory.comp_mem
    (IsSuperfunctor.map_mem (R := k) (F := G) ((homParityShiftDatum (k := k) p).hom_mem Z))
    ((homParityShiftDatum (k := k) p).inv_mem (G.obj Z))
  rw [Supercategory.zmod2_add_self] at h
  exact h

end ParityShift

/-! ## Comparisons of postcomposition functors -/

section HomPost

omit [∀ a b : B, PiSupercategory k (a ⟶ b)]

theorem homPostComp_hom_mem {a b c d : B} (E : b ⟶ c) (F : c ⟶ d) (Z : a ⟶ b) :
    (homPostComp (k := k) E F).hom.app Z ∈ parity (R := k) _ _ 0 :=
  TwoSupercategory.associator_hom_mem (R := k) Z E F

theorem homPostComp_inv_mem {a b c d : B} (E : b ⟶ c) (F : c ⟶ d) (Z : a ⟶ b) :
    (homPostComp (k := k) E F).inv.app Z ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) Z E F)

/-- A two-morphism between composites, whiskered by the argument and reassociated on both
sides, is supernatural of its parity on the postcomposition functors. -/
theorem homPostReassoc_supernatural {a b c c' d : B} (E₁ : b ⟶ c) (E₂ : c ⟶ d)
    (E₂' : b ⟶ c') (E₁' : c' ⟶ d) {p : ZMod 2} (η : E₁ ≫ E₂ ⟶ E₂' ≫ E₁')
    (hη : η ∈ parity (R := k) _ _ p) :
    IsSupernatural k p
      (F := homPost (k := k) (a := a) E₁ ⋙ homPost (k := k) E₂)
      (G := homPost (k := k) (a := a) E₂' ⋙ homPost (k := k) E₁')
      (fun Z => (associator Z E₁ E₂).hom ≫ Z ◁ η ≫ (associator Z E₂' E₁').inv) := by
  have hA := isSupernatural_of_natTrans (R := k) (homPostComp (k := k) (a := a) E₁ E₂).hom
    (homPostComp_hom_mem E₁ E₂)
  have hB := (homPostTransform (k := k) (a := a) η hη).isSupernatural p
  have hC := isSupernatural_of_natTrans (R := k) (homPostComp (k := k) (a := a) E₂' E₁').inv
    (homPostComp_inv_mem E₂' E₁')
  have := hA.comp (hB.comp hC)
  simp only [add_zero, zero_add] at this
  refine IsSupernatural.of_eq_conj rfl rfl this _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp [homPostComp, homPostTransform]

end HomPost

variable {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-! ## Two-letter matrices -/

/-- The entry of a matrix between two-letter words at the paths through given summands. -/
theorem twoTwo_two (c₁ c₂ d₁ d₂ : Col I X) (f : P.TwoEntry c₁ c₂ d₁ d₂)
    {t s s' : Sector I} (σ₁ σ₂ τ₁ τ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t)) (hw₁ : StepValid d₁.l τ₁ t)
    (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (e : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) = s)
    (e' : nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t) = s') (hs : s = s') (Z : P.H s')
    (Z' : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))) (hZ : HEq Z' Z) :
    P.twoTwo c₁ c₂ d₁ d₂ f (SPath.two σ₁ σ₂ hv₁ hv₂ e) (SPath.two τ₁ τ₂ hw₁ hw₂ e') hs Z =
      eqToHom (by subst e e'; obtain rfl := eq_of_heq hZ; rfl) ≫
        f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ (e.trans (hs.trans e'.symm)) Z' ≫
        eqToHom (by subst e e'; obtain rfl := eq_of_heq hZ; rfl) := by
  subst e e'; obtain rfl := eq_of_heq hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- **Supernaturality of a matrix between two-letter words** from that of its components. -/
theorem twoTwo_supernatural (c₁ c₂ d₁ d₂ : Col I X) (p : ZMod 2) (f : P.TwoEntry c₁ c₂ d₁ d₂)
    (hf : ∀ t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs, IsSupernatural k p
      (F := P.castH hs ⋙ P.step c₂.l σ₂ _ hv₂ ⋙ P.step c₁.l σ₁ t hv₁)
      (G := P.step d₂.l τ₂ _ hw₂ ⋙ P.step d₁.l τ₁ t hw₁)
      (f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs))
    {t s : Sector I} (q : SPath [c₁, c₂] t s) (q' : SPath [d₁, d₂] t s) :
    IsSupernatural k p (fun Z => P.twoTwo c₁ c₂ d₁ d₂ f q q' rfl Z) := by
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_two q
  subst e
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e', rfl⟩ := SPath.exists_eq_two q'
  have hx := (hf t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ e'.symm).whiskerLeft (P.castH e')
  have hF : P.pathFunctor (SPath.two (c₁ := c₁) (c₂ := c₂) σ₁ σ₂ hv₁ hv₂ rfl) =
      P.castH e' ⋙ P.castH e'.symm ⋙ P.step c₂.l σ₂ _ hv₂ ⋙ P.step c₁.l σ₁ t hv₁ := by
    rw [P.pathFunctor_two, ← Functor.assoc, P.castH_comp_castH, P.castH_rfl]
    rfl
  refine IsSupernatural.of_eq_conj hF (P.pathFunctor_two τ₁ τ₂ hw₁ hw₂ e') hx _
    (fun Z => Functor.congr_obj hF Z) (fun _ => by rw [P.pathFunctor_two]) fun Z => ?_
  rw [P.twoTwo_two c₁ c₂ d₁ d₂ f σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ rfl e' rfl Z
    ((P.castH e').obj Z) (P.castH_obj_heq e' Z)]

/-! ## The mixed paths -/

/-- The mixed interchange `J` is supernatural of the parity of the crossing. -/
theorem mixedJ_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, i) true (nextSector (true, j) false t) trivial ⋙
        P.step (true, j) false t hR)
      (fun Z => (P.mixedJ i j t hR Z).hom) := by
  refine IsSupernatural.of_parity_eq (homMixedInterchange_supernatural (k := k)
    (P.T.E i (P.muP_preE i t)) (P.W.E j (P.muM_postE j hR))
    (homContentShift D j (t.1 + Finsupp.single i 1)) (homContentShift D j t.1)) ?_
  rw [homContentShift_add_single, add_comm, ← add_assoc, Supercategory.zmod2_add_self,
    zero_add, mul_comm]

/-- The inverse of the mixed interchange is supernatural of the parity of the crossing. -/
theorem mixedJ_inv_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := P.step (true, i) true (nextSector (true, j) false t) trivial ⋙
        P.step (true, j) false t hR)
      (G := P.step (true, j) false (nextSector (true, i) true t) hR ⋙
        P.step (true, i) true t trivial)
      (fun Z => (P.mixedJ i j t hR Z).inv) :=
  isSupernatural_iso_inv (k := k)
    (F := P.step (true, j) false (nextSector (true, i) true t) hR ⋙
      P.step (true, i) true t trivial)
    (G := P.step (true, i) true (nextSector (true, j) false t) trivial ⋙
      P.step (true, j) false t hR)
    (fun Z => P.mixedJ i j t hR Z) (P.mixedJ_supernatural i j t hR)

/-- The probe dot of the path `(P,R)` is supernatural of the parity of its colour. -/
theorem prPreDot_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity i)
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (P.prPreDot i j t hR) := by
  have hx := ((homPreTransform (k := k)
    (c := P.W.obj (P.muM (nextSector (true, i) true t)))
    (P.T.dot i (P.muP_preE i t)) (P.T.dot_mem i _)).isSupernatural (D.parity i)).whiskerLeft
      (P.step (true, j) false _ hR)
  refine IsSupernatural.of_eq_conj
    (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
    (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
    rfl rfl hx _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp only [homPreTransform, prPreDot, eqToHom_refl, Category.id_comp,
    Category.comp_id, ite_true]

/-- The reservoir dot of the path `(P,R)` is supernatural of the parity of its colour. -/
theorem prPostDot_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity j)
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (P.prPostDot i j t hR) := by
  have hx := homContentPostDot_power_supernatural (k := k) P.T.obj P.W j
    (nextSector (true, i) true t).1 (P.muP (nextSector (true, i) true t)) (P.muM_postE j hR) 1
  simp only [Nat.cast_one, one_mul, pow_one] at hx
  exact hx.whiskerRight (P.step (true, i) true t trivial)

theorem natCast_dn_mul_parity (D : Datum I X) (i j : I) :
    (D.dn i j : ZMod 2) * D.parity i = 0 := by
  rcases parity_eq_zero_or_one (D.parity i) with h | h
  · rw [h, mul_zero]
  · rw [h, mul_one, ZMod.natCast_eq_zero_iff_even, ← Int.even_coe_nat]
    rcases le_or_gt 0 (D.d i j) with h0 | h0
    · rw [Datum.dn, Int.toNat_of_nonneg h0]
      exact D.even_d_of_odd h j
    · rw [Datum.dn, Int.toNat_eq_zero.mpr h0.le]
      exact Even.zero

/-- **The parameter polynomial `Q` is even**: its monomials of odd parity have zero
coefficient (Brundan–Ellis (1.4), (1.6)). -/
theorem mixedQ_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k 0
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (P.mixedQ i j t hR) := by
  unfold mixedQ
  split_ifs
  · exact IsSupernatural.smul isSupernatural_one _
  · refine IsSupernatural.add (IsSupernatural.add ?_ ?_)
      (IsSupernatural.sum _ fun p _ => IsSupernatural.sum _ fun q _ => ?_)
    · refine IsSupernatural.smul (IsSupernatural.of_parity_eq
        (IsSupernatural.pow (P.prPreDot_supernatural i j t hR) _) ?_) _
      exact natCast_dn_mul_parity D i j
    · refine IsSupernatural.smul (IsSupernatural.of_parity_eq
        (IsSupernatural.pow (P.prPostDot_supernatural i j t hR) _) ?_) _
      exact natCast_dn_mul_parity D j i
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs]
        simpa only [zero_smul] using isSupernatural_zero (R := k) 0
      · have hp : (p : ZMod 2) * D.parity i = 0 := by
          rcases parity_eq_zero_or_one ((p : ZMod 2) * D.parity i) with h | h
          · exact h
          · exact absurd (Sc.s_eq_zero i j p q h) hs
        have hq : (q : ZMod 2) * D.parity j = 0 := by
          rcases parity_eq_zero_or_one ((q : ZMod 2) * D.parity j) with h | h
          · exact h
          · exact absurd ((Sc.s_symm i j p q).trans (Sc.s_eq_zero j i q p h)) hs
        refine IsSupernatural.smul (IsSupernatural.of_parity_eq (IsSupernatural.mul
          (IsSupernatural.pow (P.prPreDot_supernatural i j t hR) p)
          (IsSupernatural.pow (P.prPostDot_supernatural i j t hR) q)) ?_) _
        rw [hp, hq, add_zero]

/-! ## The probe/probe and reservoir/reservoir paths -/

/-- The `(P,P)` entry of the distinct-colour crossing is supernatural of the parity of the
crossing. -/
theorem preCrossNe_supernatural (i j : I) (t : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) true t)) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := P.castH hs ⋙ P.step (true, j) true _ trivial ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, i) true _ trivial ⋙ P.step (true, j) true t trivial)
      (P.preCrossNe i j t hs) := by
  have h₄ : -P.muP (nextSector (true, j) true t) + D.α i =
      -P.muP (nextSector (true, j) true (nextSector (true, i) true t)) := by
    rw [hs]; exact P.muP_preE i _
  have hx := (homPreReassoc_supernatural (k := k)
    (d := P.W.obj (P.muM (nextSector (true, j) true (nextSector (true, i) true t))))
    (P.T.E i (P.muP_preE i t)) (P.T.E j (P.muP_preE j _)) (P.T.E j (P.muP_preE j t))
    (P.T.E i h₄) _
    (P.T.cross_mem j i (P.muP_preE i t) (P.muP_preE j _) (P.muP_preE j t) h₄)).whiskerLeft
      (P.castH hs)
  have hE := (isSupernatural_eqToHom (R := k)
    (eq_of_heq (P.preE_functor_heq i hs h₄ (P.muP_preE i _)))
    (fun Z => eq_of_heq (P.preE_obj_heq i hs h₄ (P.muP_preE i _) Z))).whiskerRight
      (P.step (true, j) true t trivial)
  have := hx.comp hE
  rw [add_zero, mul_comm] at this
  refine IsSupernatural.of_eq_conj rfl rfl this _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp only [preCrossNe, Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The `(P,P)` entry of the same-colour crossing is supernatural of the parity of the
crossing. -/
theorem preCrossSame_supernatural (i : I) (t : Sector I) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := P.step (true, i) true _ trivial ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, i) true _ trivial ⋙ P.step (true, i) true t trivial)
      (P.preCrossSame i t) := by
  have hx := homPreReassoc_supernatural (k := k)
    (d := P.W.obj (P.muM (nextSector (true, i) true (nextSector (true, i) true t))))
    (P.T.E i (P.muP_preE i t)) (P.T.E i (P.muP_preE i _)) (P.T.E i (P.muP_preE i t))
    (P.T.E i (P.muP_preE i _)) _
    (P.T.cross_mem i i (P.muP_preE i t) (P.muP_preE i _) (P.muP_preE i t) (P.muP_preE i _))
  exact IsSupernatural.zsmul hx _

omit [AddCommGroup X] in
/-- The comparison of the two parity shifts of a reservoir/reservoir path with a single shift
is an even supernatural isomorphism. -/
theorem postPairIso_supernatural {x a b c : B} (Ei : b ⟶ c) (Ej : a ⟶ b) (κi κj : ZMod 2) :
    IsSupernatural k 0
      (F := homPost (k := k) (a := x) Ej ⋙ homParityShift (k := k) κj ⋙
        homPost (k := k) Ei ⋙ homParityShift (k := k) κi)
      (G := homPost (k := k) (a := x) Ej ⋙ homPost (k := k) Ei ⋙
        homParityShift (k := k) (κj + κi))
      (fun Z => (postPairIso (k := k) Ei Z Ej κi κj).hom) := by
  have hA := ((isSupernatural_of_natTrans (R := k)
    (homParityShiftCommute (k := k) (homPost (k := k) (a := x) Ei) κj).inv
    (fun Z => homParityShiftCommute_inv_mem _ κj Z)).whiskerLeft
      (homPost (k := k) (a := x) Ej)).whiskerRight (homParityShift (k := k) κi)
  have hB := (isSupernatural_of_natTrans (R := k)
    (homParityShiftAdd (k := k) (C := x ⟶ c) κj κi).hom
    (fun Z => homParityShiftAdd_hom_mem κj κi Z)).whiskerLeft
      (homPost (k := k) (a := x) Ej ⋙ homPost (k := k) Ei)
  have := hA.comp hB
  rw [add_zero] at this
  exact this

/-- The `(R,R)` entry of the distinct-colour crossing is supernatural of the parity of the
crossing. -/
theorem postCrossNe_supernatural (i j : I) (t : Sector I) (hv₁ : StepValid (true, i) false t)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) false t))
    (hw₁ : StepValid (true, j) false t)
    (hw₂ : StepValid (true, i) false (nextSector (true, j) false t))
    (hs : nextSector (true, j) false (nextSector (true, i) false t) =
      nextSector (true, i) false (nextSector (true, j) false t)) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := P.castH hs ⋙ P.step (true, j) false _ hv₂ ⋙ P.step (true, i) false t hv₁)
      (G := P.step (true, i) false _ hw₂ ⋙ P.step (true, j) false t hw₁)
      (P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs) := by
  have h₃ : P.muM (nextSector (true, j) false (nextSector (true, i) false t)) + D.α i =
      P.muM (nextSector (true, j) false t) := by
    rw [hs]; exact P.muM_postE i hw₂
  have h1 := postPairIso_supernatural (k := k)
    (x := P.T.obj (-P.muP (nextSector (true, j) false (nextSector (true, i) false t))))
    (P.W.E i (P.muM_postE i hv₁)) (P.W.E j (P.muM_postE j hv₂))
    (homContentShift D i t.1) (homContentShift D j t.1)
  have h2 := (homPostReassoc_supernatural (k := k)
    (a := P.T.obj (-P.muP (nextSector (true, j) false (nextSector (true, i) false t))))
    (P.W.E j (P.muM_postE j hv₂)) (P.W.E i (P.muM_postE i hv₁)) (P.W.E i h₃)
    (P.W.E j (P.muM_postE j hw₁)) _
    (P.W.cross_mem i j (P.muM_postE j hv₂) (P.muM_postE i hv₁) h₃
      (P.muM_postE j hw₁))).whiskerRight
    (homParityShift (k := k) (homContentShift D j t.1 + homContentShift D i t.1))
  have h3 := isSupernatural_eqToHom (R := k)
    (F := homPost (k := k)
        (a := P.T.obj (-P.muP (nextSector (true, j) false (nextSector (true, i) false t))))
        (P.W.E i h₃) ⋙ homPost (k := k) (P.W.E j (P.muM_postE j hw₁)) ⋙
      homParityShift (k := k) (homContentShift D j t.1 + homContentShift D i t.1))
    (G := homPost (k := k)
        (a := P.T.obj (-P.muP (nextSector (true, j) false (nextSector (true, i) false t))))
        (P.W.E i h₃) ⋙ homPost (k := k) (P.W.E j (P.muM_postE j hw₁)) ⋙
      homParityShift (k := k) (homContentShift D i t.1 + homContentShift D j t.1))
    (by rw [add_comm]) (fun _ => by rw [add_comm])
  have h4 := isSupernatural_iso_inv (k := k)
    (F := homPost (k := k)
        (a := P.T.obj (-P.muP (nextSector (true, j) false (nextSector (true, i) false t))))
        (P.W.E i h₃) ⋙ homParityShift (k := k) (homContentShift D i t.1) ⋙
      homPost (k := k) (P.W.E j (P.muM_postE j hw₁)) ⋙
        homParityShift (k := k) (homContentShift D j t.1))
    (G := homPost (k := k)
        (a := P.T.obj (-P.muP (nextSector (true, j) false (nextSector (true, i) false t))))
        (P.W.E i h₃) ⋙ homPost (k := k) (P.W.E j (P.muM_postE j hw₁)) ⋙
      homParityShift (k := k) (homContentShift D i t.1 + homContentShift D j t.1))
    (fun Z => postPairIso (k := k) (P.W.E j (P.muM_postE j hw₁)) Z (P.W.E i h₃)
      (homContentShift D j t.1) (homContentShift D i t.1))
    (postPairIso_supernatural (k := k) _ _ _ _)
  have hx := (h1.comp (h2.comp (h3.comp h4))).whiskerLeft (P.castH hs)
  have h5 := (isSupernatural_eqToHom (R := k)
    (eq_of_heq (P.postE_functor_heq i t.1 hs h₃ (P.muM_postE i hw₂)))
    (fun Z => eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z))).whiskerRight
      (P.step (true, j) false t hw₁)
  have := hx.comp h5
  simp only [add_zero, zero_add] at this
  refine IsSupernatural.of_eq_conj rfl rfl this _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp only [postCrossNe, Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

/-- The `(R,R)` entry of the same-colour crossing is supernatural of the parity of the
crossing. -/
theorem postCrossSame_supernatural (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t)) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := P.step (true, i) false _ hw ⋙ P.step (true, i) false t hv)
      (G := P.step (true, i) false _ hw ⋙ P.step (true, i) false t hv)
      (P.postCrossSame i t hv hw) := by
  have hA := isSupernatural_of_natTrans (R := k)
    (homContentPostWordIso P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
      (P.muM_postE i hv)).hom
    (homContentPostWordIso_mem P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
      (P.muM_postE i hv))
  have hB := isSupernatural_of_natTrans (R := k)
    (homContentPostWordIso P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
      (P.muM_postE i hv)).inv
    (fun Z => inv_mem ((homContentPostWordIso P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
      (P.muM_postE i hv)).app Z)
      (homContentPostWordIso_mem P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
        (P.muM_postE i hv) Z))
  have ht := (homPostTransform (k := k) (a := P.T.obj (-P.muP t))
    (P.W.cross i i (P.muM_postE i hw) (P.muM_postE i hv) (P.muM_postE i hw)
      (P.muM_postE i hv))
    (P.W.loc i (P.muM_postE i hw) (P.muM_postE i hv)).cross_mem).isSupernatural (D.parity i)
  have := hA.comp (ht.comp hB)
  simp only [add_zero, zero_add] at this
  rw [zmod2_mul_self]
  refine IsSupernatural.of_eq_conj
    (F := P.step (true, i) false _ hw ⋙ P.step (true, i) false t hv)
    (G := P.step (true, i) false _ hw ⋙ P.step (true, i) false t hv)
    rfl rfl this _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp only [postCrossSame, homContentPostCrossingApp, homPostTransform, ite_true,
    eqToHom_refl, Category.id_comp, Category.comp_id]

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A transport along an equality of a sector with itself does not change supernaturality. -/
theorem isSupernatural_castH_self {s t' : Sector I} (hs : s = s) {p : ZMod 2}
    {F G : P.H s ⥤ P.H t'} {x : ∀ Z, F.obj Z ⟶ G.obj Z} (hx : IsSupernatural k p x) :
    IsSupernatural k p (F := P.castH hs ⋙ F) (G := G) x :=
  hx

/-- **The entries of the distinct-colour crossing are supernatural** of the parity of the
crossing. -/
theorem crossNeEntry_supernatural (i j : I) (r₁ r₂ r₁' r₂' : X) {t s : Sector I}
    (q : SPath [⟨(true, i), r₁⟩, ⟨(true, j), r₂⟩] t s)
    (q' : SPath [⟨(true, j), r₁'⟩, ⟨(true, i), r₂'⟩] t s) :
    IsSupernatural k (D.parity i * D.parity j)
      (fun Z => P.twoTwo _ _ _ _ (P.crossNeEntry i j r₁ r₂ r₁' r₂') q q' rfl Z) := by
  refine P.twoTwo_supernatural _ _ _ _ _ _
    (fun t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs => ?_) q q'
  cases σ₁ <;> cases σ₂ <;> cases τ₁ <;> cases τ₂
  · exact P.postCrossNe_supernatural i j t hv₁ hv₂ hw₁ hw₂ hs
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · have := (P.mixedJ_inv_supernatural j i t hw₂).comp (P.mixedQ_supernatural j i t hw₂)
    rw [add_zero, mul_comm] at this
    exact P.isSupernatural_castH_self hs this
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact P.isSupernatural_castH_self hs (P.mixedJ_supernatural i j t hv₂)
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact P.preCrossNe_supernatural i j t hs

end ProbeReservoir

/-- Supernaturality of the coefficient `a` of the same-colour mixed block, of the parity of
its colour. -/
def ProbeReservoir.CrossCoeff.IsSupernatural {P : ProbeReservoir k B D Sc}
    (c : P.CrossCoeff) : Prop :=
  ∀ (i : I) (t : Sector I) (hv : StepValid (true, i) false t),
    StringDiagrams.Supercategory.IsSupernatural k (D.parity i)
      (F := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
        P.step (true, i) false t hv)
      (G := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
        P.step (true, i) false t hv)
      (c.a i t hv)

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- **The entries of the same-colour crossing are supernatural** of the parity of the
crossing, when the coefficient `a` is. -/
theorem crossSameEntry_supernatural (c : P.CrossCoeff) (hc : c.IsSupernatural) (i : I)
    (r₁ r₂ r₁' r₂' : X) {t s : Sector I}
    (q : SPath [⟨(true, i), r₁⟩, ⟨(true, i), r₂⟩] t s)
    (q' : SPath [⟨(true, i), r₁'⟩, ⟨(true, i), r₂'⟩] t s) :
    IsSupernatural k (D.parity i * D.parity i)
      (fun Z => P.twoTwo _ _ _ _ (P.crossSameEntry c i r₁ r₂ r₁' r₂') q q' rfl Z) := by
  have hp : D.parity i * D.parity i + (D.parity i * D.parity i + D.parity i) =
      D.parity i * D.parity i := by
    rw [zmod2_mul_self, ← add_assoc, Supercategory.zmod2_add_self, zero_add]
  have hp' : D.parity i + (D.parity i + D.parity i * D.parity i) =
      D.parity i * D.parity i := by
    rw [zmod2_mul_self, ← add_assoc, Supercategory.zmod2_add_self, zero_add]
  refine P.twoTwo_supernatural _ _ _ _ _ _
    (fun t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs => ?_) q q'
  cases σ₁ <;> cases σ₂ <;> cases τ₁ <;> cases τ₂
  · exact P.isSupernatural_castH_self hs (P.postCrossSame_supernatural i t hv₁ hv₂)
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · have := hc i t hv₁
    rw [← zmod2_mul_self (D.parity i)] at this
    exact P.isSupernatural_castH_self hs this
  · have := IsSupernatural.neg ((hc i t hv₁).comp ((hc i t hv₁).comp
      (P.mixedJ_inv_supernatural i i t hw₂)))
    rw [hp'] at this
    exact P.isSupernatural_castH_self hs this
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact P.isSupernatural_castH_self hs (P.mixedJ_supernatural i i t hv₂)
  · have := IsSupernatural.neg ((P.mixedJ_supernatural i i t hv₂).comp ((hc i t hv₂).comp
      (P.mixedJ_inv_supernatural i i t hv₂)))
    rw [add_comm (D.parity i) (D.parity i * D.parity i), hp] at this
    exact P.isSupernatural_castH_self hs this
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact isSupernatural_zero _
  · exact P.isSupernatural_castH_self hs (P.preCrossSame_supernatural i t)

/-- **The image of the upward crossing is supernatural** of parity `pᵢ pⱼ`, when the
coefficient of the same-colour mixed block is. -/
theorem crossImage_supernatural (c : P.CrossCoeff) (hc : c.IsSupernatural) (i j : I) (ν : X)
    {t s : Sector I} (q : SPath (wd D ν (SKM.Shape.cross i j).dom) t s)
    (q' : SPath (wd D ν (SKM.Shape.cross i j).cod) t s) :
    IsSupernatural k (D.parity i * D.parity j) (fun Z => P.crossImage c i j ν q q' Z) := by
  by_cases h : i = j
  · subst h
    simp only [crossImage, dite_true]
    exact P.crossSameEntry_supernatural c hc i _ _ _ _ q q'
  · simp only [crossImage, h, dite_false]
    exact P.crossNeEntry_supernatural i j _ _ _ _ q q'

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
