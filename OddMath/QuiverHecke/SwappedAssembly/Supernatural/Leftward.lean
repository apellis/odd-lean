/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixInverse
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Generators

/-! # Supernaturality of the equal-colour leftward data

The equal-colour leftward data `L` of the swapped generators (the leftward crossing
`Fᵢ Eᵢ → Eᵢ Fᵢ` and the `♦`-cups and caps) are characterized by `LeftwardData.IsInverse`: they
are the entries of the two-sided inverses of the augmented maps of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,

* (1.13), `⟨hᵢ, ν⟩ ≥ 0`: `(σ, ε, ε x, …) : Eᵢ Fᵢ → Fᵢ Eᵢ ⊕ 1^{⟨hᵢ,ν⟩}`, with inverse
  `(-lcross, ♦-cups)`;
* (1.14), `⟨hᵢ, ν⟩ ≤ 0`: `(-σ, η, x η, …) : Eᵢ Fᵢ ⊕ 1^{-⟨hᵢ,ν⟩} → Fᵢ Eᵢ`, with inverse
  `(lcross, ♦-caps)`.

The entries of the augmented maps are built from the upward generators, so they are
supernatural when the coefficient `a` of the equal-colour mixed block is: of parity `pᵢ²` on
`σ` and `pᵢ n` on the `n`-th component. In (1.13) this parity depends only on the target index,
in (1.14) only on the source index, so `isSupernatural_of_inverse_target` and
`isSupernatural_of_inverse_source` give the supernaturality of the inverse entries.

Main declaration: `ProbeReservoir.LeftwardData.isSupernatural_of_isInverse`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-! ## Evaluations of linear combinations -/

theorem compEval_zero (gens : P.Generators) {a b : Obj (SKM.sig D)} {s t : Sector I}
    (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compEval gens (0 : LinDiagram k a b) p q Z = 0 :=
  Finsupp.sum_zero_index

theorem compEval_add (gens : P.Generators) {a b : Obj (SKM.sig D)} (x y : LinDiagram k a b)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compEval gens (x + y) p q Z = compEval gens x p q Z + compEval gens y p q Z :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem compEval_neg (gens : P.Generators) {a b : Obj (SKM.sig D)} (x : LinDiagram k a b)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compEval gens (-x) p q Z = -compEval gens x p q Z := by
  have h := compEval_sub gens 0 x p q Z
  rwa [zero_sub, compEval_zero, zero_sub] at h

/-! ## Entries of the `♦`-cups and caps -/

theorem compDiag_dcupL (gens : P.Generators) (i : I) (n : ℕ) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν []) s t) (q : SPath (wd D ν [up i, dn i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dcupL i n) (SKM.sChain_dcupL i n)) p q Z =
      gens.dcup i n ν p q Z := by
  show compList gens (a := SKM.ob D ν []) (b := SKM.ob D ν [up i, dn i])
    [SKM.lay D ν [] (SKM.Shape.dcup i n) []] ((SKM.sChain_dcupL i n).chain D ν) p q Z = _
  erw [compList_one]
  simp only [SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.dcup i n) []) (.nil s) p q
    (.nil t) p q (by cases p; rfl) (SPath.append_nil_pair q) Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem compDiag_dcapL (gens : P.Generators) (i : I) (n : ℕ) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [dn i, up i]) s t) (q : SPath (wd D ν []) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dcapL i n) (SKM.sChain_dcapL i n)) p q Z =
      gens.dcap i n ν p q Z := by
  show compList gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [])
    [SKM.lay D ν [] (SKM.Shape.dcap i n) []] ((SKM.sChain_dcapL i n).chain D ν) p q Z = _
  erw [compList_one]
  simp only [SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.dcap i n) []) (.nil s) p q
    (.nil t) p q (SPath.append_nil_pair p) (by cases q; rfl) Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-! ## Entries built from dots, cups and caps -/

/-- A chain of layers of dots, cups and caps has the same entries for the swapped and the
upward generators. -/
theorem compDiag_swappedGens_eq_upward (c : P.CrossCoeff) (L : P.LeftwardData) (ν : X)
    {w w' : List (Letter I)} (ls : List (SKM.LayerData I)) (h : SKM.SChain w ls w')
    (hls : ∀ x ∈ ls, ∃ i, x.2.1 = .dot i ∨ x.2.1 = .cup i ∨ x.2.1 = .cap i)
    {s t : Sector I} (p : SPath (wd D ν w) s t) (q : SPath (wd D ν w') s t) (Z : P.H t) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν ls h) p q Z =
      compList (P.upwardGens c) (SKM.layList D ν ls) (h.chain D ν) p q Z := by
  refine compList_congr _ _ _ ?_ (h.chain D ν) p q Z
  intro L' hL'
  simp only [SKM.layList, List.mem_map] at hL'
  obtain ⟨x, hx, rfl⟩ := hL'
  obtain ⟨i, hi | hi | hi⟩ := hls x hx <;>
  · obtain ⟨u, g, v⟩ := x
    simp only at hi
    subst hi
    intros
    rfl

theorem parity_layList (ν : X) (ls : List (SKM.LayerData I)) :
    ((SKM.layList D ν ls).map fun L => L.gen.1.parity D).sum =
      (ls.map fun x => x.2.1.parity D).sum := by
  simp only [SKM.layList, List.map_map]
  rfl

theorem epsL_upward (i : I) (n : ℕ) :
    ∀ x ∈ SKM.epsL i n, ∃ j, x.2.1 = .dot j ∨ x.2.1 = .cup j ∨ x.2.1 = .cap j := by
  intro x hx
  simp only [SKM.epsL, SKM.dotsL, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ⟨_, rfl⟩ | rfl
  · exact ⟨i, .inl rfl⟩
  · exact ⟨i, .inr (.inr rfl)⟩

theorem etaL_upward (i : I) (n : ℕ) :
    ∀ x ∈ SKM.etaL i n, ∃ j, x.2.1 = .dot j ∨ x.2.1 = .cup j ∨ x.2.1 = .cap j := by
  intro x hx
  simp only [SKM.etaL, SKM.dotsL, List.mem_replicate, List.mem_cons,
    List.singleton_append] at hx
  rcases hx with rfl | ⟨_, rfl⟩
  · exact ⟨i, .inr (.inl rfl)⟩
  · exact ⟨i, .inl rfl⟩

/-- The entries of `ε xⁿ` are supernatural of parity `n pᵢ`. -/
theorem compDiag_epsL_supernatural (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (i : I) (n : ℕ) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, dn i]) s t) (q : SPath (wd D ν []) s t) :
    IsSupernatural k ((n : ZMod 2) * D.parity i) (fun Z =>
      compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.epsL i n) (SKM.sChain_epsL i n)) p q Z) := by
  have e := fun Z => compDiag_swappedGens_eq_upward c L ν (SKM.epsL i n) (SKM.sChain_epsL i n)
    (epsL_upward i n) p q Z
  simp only [e]
  have hs := compList_supernatural (upwardGens_supernatural c hc) (SKM.layList D ν (SKM.epsL i n))
    ((SKM.sChain_epsL i n).chain D ν) p q
  rwa [parity_layList, SKM.parity_epsL] at hs

/-- The entries of `xⁿ η` are supernatural of parity `n pᵢ`. -/
theorem compDiag_etaL_supernatural (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (i : I) (n : ℕ) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν []) s t) (q : SPath (wd D ν [dn i, up i]) s t) :
    IsSupernatural k ((n : ZMod 2) * D.parity i) (fun Z =>
      compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.etaL i n) (SKM.sChain_etaL i n)) p q Z) := by
  have e := fun Z => compDiag_swappedGens_eq_upward c L ν (SKM.etaL i n) (SKM.sChain_etaL i n)
    (etaL_upward i n) p q Z
  simp only [e]
  have hs := compList_supernatural (upwardGens_supernatural c hc) (SKM.layList D ν (SKM.etaL i n))
    ((SKM.sChain_etaL i n).chain D ν) p q
  rwa [parity_layList, SKM.parity_etaL] at hs

/-! ## The inverse of the augmented map (1.13) -/

/-- The entries of `σ : Eᵢ Fᵢ → Fᵢ Eᵢ` for the swapped generators are supernatural of parity
`pᵢ²`. -/
theorem compDiag_sigmaL_supernatural (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (i : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s) :
    IsSupernatural k (D.parity i * D.parity i) (fun Z =>
      compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.sigmaL i i) (SKM.sChain_sigmaL i i))
        p q Z) := by
  simp only [compDiag_sigmaL_swappedGens]
  exact sigmaEntry_supernatural c hc i i ν p q

open Classical in
/-- **The inverse of the augmented map (1.13) is supernatural**: for `⟨hᵢ, ν⟩ ≥ 0`, the
entries of the equal-colour leftward crossing have parity `pᵢ²` and those of the `♦`-cup
with label `n < ⟨hᵢ, ν⟩` have parity `n pᵢ`. -/
theorem leftward_supernatural_of_nonneg (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (hL : L.IsInverse c) (i : I) (ν : X) (hh : 0 ≤ D.h i ν)
    {t s : Sector I} :
    (∀ (q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      IsSupernatural k (D.parity i * D.parity i) (fun Z =>
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i))
          q p Z)) ∧
    (∀ (n : Fin (D.h i ν).toNat) (r : SPath (wd D ν []) t s)
      (p : SPath (wd D ν [up i, dn i]) t s),
      IsSupernatural k (((n : ℕ) : ZMod 2) * D.parity i) (fun Z =>
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.dcupL i n) (SKM.sChain_dcupL i n))
          r p Z)) := by
  let gens := P.swappedGens c L
  let N := (D.h i ν).toNat
  let A := SPath (wd D ν [up i, dn i]) t s
  let A' := SPath (wd D ν [dn i, up i]) t s
  let A₀ := SPath (wd D ν []) t s
  let : Fintype A := Fintype.ofFinite _
  let : Fintype A' := Fintype.ofFinite _
  let : Fintype A₀ := Fintype.ofFinite _
  let F : A → P.H s ⥤ P.H t := fun p => P.pathFunctor p
  let G : A' ⊕ (Fin N × A₀) → P.H s ⥤ P.H t :=
    Sum.elim (fun q => P.pathFunctor q) (fun nr => P.pathFunctor nr.2)
  let ρ : A' ⊕ (Fin N × A₀) → ZMod 2 :=
    Sum.elim (fun _ => D.parity i * D.parity i) (fun nr => ((nr.1 : ℕ) : ZMod 2) * D.parity i)
  let a : ∀ x y Z, (F x).obj Z ⟶ (G y).obj Z := fun p y Z =>
    Sum.rec (motive := fun y => (F p).obj Z ⟶ (G y).obj Z)
      (fun q => compDiag gens (SKM.mkD D ν (SKM.sigmaL i i) (SKM.sChain_sigmaL i i)) p q Z)
      (fun nr => compDiag gens (SKM.mkD D ν (SKM.epsL i nr.1) (SKM.sChain_epsL i nr.1)) p nr.2 Z)
      y
  let b : ∀ y x Z, (G y).obj Z ⟶ (F x).obj Z := fun y p Z =>
    Sum.rec (motive := fun y => (G y).obj Z ⟶ (F p).obj Z)
      (fun q => -compDiag gens (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i)) q p Z)
      (fun nr => compDiag gens (SKM.mkD D ν (SKM.dcupL i nr.1) (SKM.sChain_dcupL i nr.1)) nr.2 p Z)
      y
  have ha : ∀ x y, IsSupernatural k (ρ y) (a x y) := by
    rintro p (q | ⟨n, r⟩)
    · exact compDiag_sigmaL_supernatural c L hc i ν p q
    · exact compDiag_epsL_supernatural c L hc i n ν p r
  have ea : ∀ (p : A) (q : A') Z, a p (.inl q) Z =
      compDiag gens (SKM.mkD D ν (SKM.sigmaL i i) (SKM.sChain_sigmaL i i)) p q Z :=
    fun _ _ _ => rfl
  have ea' : ∀ (p : A) (n : Fin N) (r : A₀) Z, a p (.inr (n, r)) Z =
      compDiag gens (SKM.mkD D ν (SKM.epsL i n) (SKM.sChain_epsL i n)) p r Z :=
    fun _ _ _ _ => rfl
  have eb : ∀ (q : A') (p : A) Z, b (.inl q) p Z =
      -compDiag gens (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i)) q p Z :=
    fun _ _ _ => rfl
  have eb' : ∀ (n : Fin N) (r : A₀) (p : A) Z, b (.inr (n, r)) p Z =
      compDiag gens (SKM.mkD D ν (SKM.dcupL i n) (SKM.sChain_dcupL i n)) r p Z :=
    fun _ _ _ _ => rfl
  have hab : ∀ x x' Z, ∑ y, a x y Z ≫ b y x' Z = famDelta F x x' Z := by
    intro p p' Z
    have h : compEval gens (a := SKM.ob D ν [up i, dn i]) (b := SKM.ob D ν [up i, dn i])
        (SKM.relation D Sc (.invP₁ i ν hh)) p p' Z = 0 :=
      hL (.invP₁ i ν hh) rfl (by simp [IsInvNe]) p p' Z
    simp only [SKM.relation] at h
    rw [compEval_sub, compEval_add, compEval_neg, compEval_sum,
      compEval_dg_append gens ν (SKM.sigmaL i i) (SKM.lcrossL i i) (SKM.sChain_sigmaL i i)
        (SKM.sChain_lcrossL i i)] at h
    rw [Finset.sum_congr rfl fun n _ => compEval_dg_append gens ν (SKM.epsL i n) (SKM.dcupL i n)
      (SKM.sChain_epsL i n) (SKM.sChain_dcupL i n) p p' Z] at h
    rw [compEval_of, sub_eq_zero] at h
    have e : famDelta F p p' Z = compDiag gens (𝟙 (SKM.ob D ν [up i, dn i])) p p' Z := by
      rw [compDiag_id]
      by_cases hp : p = p'
      · subst hp; simp [famDelta]; rfl
      · simp [famDelta, hp]
    rw [e, ← h, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [ea, ea', eb, eb', Preadditive.comp_neg, Finset.sum_neg_distrib]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun n => ∑ r : A₀,
      compDiag gens (SKM.mkD D ν (SKM.epsL i n) (SKM.sChain_epsL i n)) p r Z ≫
        compDiag gens (SKM.mkD D ν (SKM.dcupL i n) (SKM.sChain_dcupL i n)) r p' Z) N
  have hba : ∀ y y' Z, ∑ x, b y x Z ≫ a x y' Z = famDelta G y y' Z := by
    rintro (q | ⟨n, r⟩) (q' | ⟨m, r'⟩) Z
    · have h : compEval gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [dn i, up i])
          (SKM.relation D Sc (.invP₂ i ν hh)) q q' Z = 0 :=
        hL (.invP₂ i ν hh) rfl (by simp [IsInvNe]) q q' Z
      simp only [SKM.relation] at h
      rw [compEval_add, compEval_dg_append gens ν (SKM.lcrossL i i) (SKM.sigmaL i i)
        (SKM.sChain_lcrossL i i) (SKM.sChain_sigmaL i i), compEval_of] at h
      have e : famDelta G (.inl q) (.inl q') Z =
          compDiag gens (𝟙 (SKM.ob D ν [dn i, up i])) q q' Z := by
        rw [compDiag_id]
        by_cases hq : q = q'
        · subst hq; simp [famDelta]; rfl
        · simp [famDelta, hq]
      rw [e, ← neg_eq_of_add_eq_zero_right h]
      simp only [eb, ea, Preadditive.neg_comp, Finset.sum_neg_distrib]
      rfl
    · have h : compEval gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [])
          (SKM.relation D Sc (.invP₃ i ν m (Int.lt_toNat.mp m.2))) q r' Z = 0 :=
        hL (.invP₃ i ν m (Int.lt_toNat.mp m.2)) rfl (by simp [IsInvNe]) q r' Z
      simp only [SKM.relation] at h
      rw [compEval_dg_append gens ν (SKM.lcrossL i i) (SKM.epsL i m) (SKM.sChain_lcrossL i i)
        (SKM.sChain_epsL i m)] at h
      have e : famDelta G (.inl q) (.inr (m, r')) Z = 0 := by simp [famDelta]
      rw [e]
      simp only [eb, ea', Preadditive.neg_comp, Finset.sum_neg_distrib]
      rw [← neg_zero, ← h]
      rfl
    · have h : compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [dn i, up i])
          (SKM.relation D Sc (.invP₄ i ν n (Int.lt_toNat.mp n.2))) r q' Z = 0 :=
        hL (.invP₄ i ν n (Int.lt_toNat.mp n.2)) rfl (by simp [IsInvNe]) r q' Z
      simp only [SKM.relation] at h
      rw [compEval_dg_append gens ν (SKM.dcupL i n) (SKM.sigmaL i i) (SKM.sChain_dcupL i n)
        (SKM.sChain_sigmaL i i)] at h
      have e : famDelta G (.inr (n, r)) (.inl q') Z = 0 := by simp [famDelta]
      rw [e, ← h]
      simp only [eb', ea]
      rfl
    · have h : compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [])
          (SKM.relation D Sc (.invP₅ i ν m n (Int.lt_toNat.mp m.2) (Int.lt_toNat.mp n.2)))
          r r' Z = 0 :=
        hL (.invP₅ i ν m n (Int.lt_toNat.mp m.2) (Int.lt_toNat.mp n.2)) rfl
          (by simp [IsInvNe]) r r' Z
      simp only [SKM.relation] at h
      rw [compEval_sub, compEval_dg_append gens ν (SKM.dcupL i n) (SKM.epsL i m)
        (SKM.sChain_dcupL i n) (SKM.sChain_epsL i m), sub_eq_zero] at h
      simp only [eb', ea']
      by_cases hmn : n = m
      · subst hmn
        simp only [ite_true, compEval_of] at h
        have e : famDelta G (.inr (n, r)) (.inr (n, r')) Z =
            compDiag gens (𝟙 (SKM.ob D ν [])) r r' Z := by
          rw [compDiag_id]
          by_cases hr : r = r'
          · subst hr; simp [famDelta]; rfl
          · simp [famDelta, hr]
        rw [e, ← h]
        rfl
      · have hmn' : (m : ℕ) ≠ n := fun h' => hmn (Fin.ext h'.symm)
        simp only [hmn', ite_false, compEval_zero] at h
        have e : famDelta G (.inr (n, r)) (.inr (m, r')) Z = 0 := by
          simp [famDelta, hmn]
        rw [e, ← h]
        rfl
  refine ⟨fun q p => ?_, fun n r p => ?_⟩
  · have hn := IsSupernatural.neg (isSupernatural_of_inverse_target ρ a b ha hab hba (.inl q) p)
    simp only [eb, neg_neg] at hn
    exact hn
  · exact isSupernatural_of_inverse_target ρ a b ha hab hba (.inr (n, r)) p

/-! ## The inverse of the augmented map (1.14) -/

open Classical in
/-- **The inverse of the augmented map (1.14) is supernatural**: for `⟨hᵢ, ν⟩ ≤ 0`, the
entries of the equal-colour leftward crossing have parity `pᵢ²` and those of the `♦`-cap
with label `n < -⟨hᵢ, ν⟩` have parity `n pᵢ`. -/
theorem leftward_supernatural_of_nonpos (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (hL : L.IsInverse c) (i : I) (ν : X) (hh : D.h i ν ≤ 0)
    {t s : Sector I} :
    (∀ (q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      IsSupernatural k (D.parity i * D.parity i) (fun Z =>
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i))
          q p Z)) ∧
    (∀ (n : Fin (-D.h i ν).toNat) (q : SPath (wd D ν [dn i, up i]) t s)
      (r : SPath (wd D ν []) t s),
      IsSupernatural k (((n : ℕ) : ZMod 2) * D.parity i) (fun Z =>
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.dcapL i n) (SKM.sChain_dcapL i n))
          q r Z)) := by
  let gens := P.swappedGens c L
  let N := (-D.h i ν).toNat
  let A := SPath (wd D ν [up i, dn i]) t s
  let A' := SPath (wd D ν [dn i, up i]) t s
  let A₀ := SPath (wd D ν []) t s
  let : Fintype A := Fintype.ofFinite _
  let : Fintype A' := Fintype.ofFinite _
  let : Fintype A₀ := Fintype.ofFinite _
  let F : A ⊕ (Fin N × A₀) → P.H s ⥤ P.H t :=
    Sum.elim (fun p => P.pathFunctor p) (fun nr => P.pathFunctor nr.2)
  let G : A' → P.H s ⥤ P.H t := fun q => P.pathFunctor q
  let ρ : A ⊕ (Fin N × A₀) → ZMod 2 :=
    Sum.elim (fun _ => D.parity i * D.parity i) (fun nr => ((nr.1 : ℕ) : ZMod 2) * D.parity i)
  let a : ∀ x y Z, (F x).obj Z ⟶ (G y).obj Z := fun x q Z =>
    Sum.rec (motive := fun x => (F x).obj Z ⟶ (G q).obj Z)
      (fun p => -compDiag gens (SKM.mkD D ν (SKM.sigmaL i i) (SKM.sChain_sigmaL i i)) p q Z)
      (fun nr => compDiag gens (SKM.mkD D ν (SKM.etaL i nr.1) (SKM.sChain_etaL i nr.1)) nr.2 q Z)
      x
  let b : ∀ y x Z, (G y).obj Z ⟶ (F x).obj Z := fun q x Z =>
    Sum.rec (motive := fun x => (G q).obj Z ⟶ (F x).obj Z)
      (fun p => compDiag gens (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i)) q p Z)
      (fun nr => compDiag gens (SKM.mkD D ν (SKM.dcapL i nr.1) (SKM.sChain_dcapL i nr.1)) q nr.2 Z)
      x
  have ea : ∀ (p : A) (q : A') Z, a (.inl p) q Z =
      -compDiag gens (SKM.mkD D ν (SKM.sigmaL i i) (SKM.sChain_sigmaL i i)) p q Z :=
    fun _ _ _ => rfl
  have ea' : ∀ (n : Fin N) (r : A₀) (q : A') Z, a (.inr (n, r)) q Z =
      compDiag gens (SKM.mkD D ν (SKM.etaL i n) (SKM.sChain_etaL i n)) r q Z :=
    fun _ _ _ _ => rfl
  have eb : ∀ (q : A') (p : A) Z, b q (.inl p) Z =
      compDiag gens (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i)) q p Z :=
    fun _ _ _ => rfl
  have eb' : ∀ (q : A') (n : Fin N) (r : A₀) Z, b q (.inr (n, r)) Z =
      compDiag gens (SKM.mkD D ν (SKM.dcapL i n) (SKM.sChain_dcapL i n)) q r Z :=
    fun _ _ _ _ => rfl
  have ha : ∀ x y, IsSupernatural k (ρ x) (a x y) := by
    rintro (p | ⟨n, r⟩) q
    · exact IsSupernatural.neg (compDiag_sigmaL_supernatural c L hc i ν p q)
    · exact compDiag_etaL_supernatural c L hc i n ν r q
  have hab : ∀ x x' Z, ∑ y, a x y Z ≫ b y x' Z = famDelta F x x' Z := by
    rintro (p | ⟨n, r⟩) (p' | ⟨m, r'⟩) Z
    · have h : compEval gens (a := SKM.ob D ν [up i, dn i]) (b := SKM.ob D ν [up i, dn i])
          (SKM.relation D Sc (.invM₂ i ν hh)) p p' Z = 0 :=
        hL (.invM₂ i ν hh) rfl (by simp [IsInvNe]) p p' Z
      simp only [SKM.relation] at h
      rw [compEval_add, compEval_dg_append gens ν (SKM.sigmaL i i) (SKM.lcrossL i i)
        (SKM.sChain_sigmaL i i) (SKM.sChain_lcrossL i i), compEval_of] at h
      have e : famDelta F (.inl p) (.inl p') Z =
          compDiag gens (𝟙 (SKM.ob D ν [up i, dn i])) p p' Z := by
        rw [compDiag_id]
        by_cases hp : p = p'
        · subst hp; simp [famDelta]; rfl
        · simp [famDelta, hp]
      rw [e, ← neg_eq_of_add_eq_zero_right h]
      simp only [ea, eb, Preadditive.neg_comp, Finset.sum_neg_distrib]
      rfl
    · have h : compEval gens (a := SKM.ob D ν [up i, dn i]) (b := SKM.ob D ν [])
          (SKM.relation D Sc (.invM₄ i ν m (Int.lt_toNat.mp m.2))) p r' Z = 0 :=
        hL (.invM₄ i ν m (Int.lt_toNat.mp m.2)) rfl (by simp [IsInvNe]) p r' Z
      simp only [SKM.relation] at h
      rw [compEval_dg_append gens ν (SKM.sigmaL i i) (SKM.dcapL i m) (SKM.sChain_sigmaL i i)
        (SKM.sChain_dcapL i m)] at h
      have e : famDelta F (.inl p) (.inr (m, r')) Z = 0 := by simp [famDelta]
      rw [e]
      simp only [ea, eb', Preadditive.neg_comp, Finset.sum_neg_distrib]
      rw [← neg_zero, ← h]
      rfl
    · have h : compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [up i, dn i])
          (SKM.relation D Sc (.invM₃ i ν n (Int.lt_toNat.mp n.2))) r p' Z = 0 :=
        hL (.invM₃ i ν n (Int.lt_toNat.mp n.2)) rfl (by simp [IsInvNe]) r p' Z
      simp only [SKM.relation] at h
      rw [compEval_dg_append gens ν (SKM.etaL i n) (SKM.lcrossL i i) (SKM.sChain_etaL i n)
        (SKM.sChain_lcrossL i i)] at h
      have e : famDelta F (.inr (n, r)) (.inl p') Z = 0 := by simp [famDelta]
      rw [e, ← h]
      simp only [ea', eb]
      rfl
    · have h : compEval gens (a := SKM.ob D ν []) (b := SKM.ob D ν [])
          (SKM.relation D Sc (.invM₅ i ν n m (Int.lt_toNat.mp n.2) (Int.lt_toNat.mp m.2)))
          r r' Z = 0 :=
        hL (.invM₅ i ν n m (Int.lt_toNat.mp n.2) (Int.lt_toNat.mp m.2)) rfl
          (by simp [IsInvNe]) r r' Z
      simp only [SKM.relation] at h
      rw [compEval_sub, compEval_dg_append gens ν (SKM.etaL i n) (SKM.dcapL i m)
        (SKM.sChain_etaL i n) (SKM.sChain_dcapL i m), sub_eq_zero] at h
      simp only [ea', eb']
      by_cases hmn : n = m
      · subst hmn
        simp only [ite_true, compEval_of] at h
        have e : famDelta F (.inr (n, r)) (.inr (n, r')) Z =
            compDiag gens (𝟙 (SKM.ob D ν [])) r r' Z := by
          rw [compDiag_id]
          by_cases hr : r = r'
          · subst hr; simp [famDelta]; rfl
          · simp [famDelta, hr]
        rw [e, ← h]
        rfl
      · have hmn' : (n : ℕ) ≠ m := fun h' => hmn (Fin.ext h')
        simp only [hmn', ite_false, compEval_zero] at h
        have e : famDelta F (.inr (n, r)) (.inr (m, r')) Z = 0 := by
          simp [famDelta, hmn]
        rw [e, ← h]
        rfl
  have hba : ∀ y y' Z, ∑ x, b y x Z ≫ a x y' Z = famDelta G y y' Z := by
    intro q q' Z
    have h : compEval gens (a := SKM.ob D ν [dn i, up i]) (b := SKM.ob D ν [dn i, up i])
        (SKM.relation D Sc (.invM₁ i ν hh)) q q' Z = 0 :=
      hL (.invM₁ i ν hh) rfl (by simp [IsInvNe]) q q' Z
    simp only [SKM.relation] at h
    rw [compEval_sub, compEval_add, compEval_neg, compEval_sum,
      compEval_dg_append gens ν (SKM.lcrossL i i) (SKM.sigmaL i i) (SKM.sChain_lcrossL i i)
        (SKM.sChain_sigmaL i i)] at h
    rw [Finset.sum_congr rfl fun n _ => compEval_dg_append gens ν (SKM.dcapL i n) (SKM.etaL i n)
      (SKM.sChain_dcapL i n) (SKM.sChain_etaL i n) q q' Z] at h
    rw [compEval_of, sub_eq_zero] at h
    have e : famDelta G q q' Z = compDiag gens (𝟙 (SKM.ob D ν [dn i, up i])) q q' Z := by
      rw [compDiag_id]
      by_cases hq : q = q'
      · subst hq; simp [famDelta]; rfl
      · simp [famDelta, hq]
    rw [e, ← h, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [ea, ea', eb, eb', Preadditive.comp_neg, Finset.sum_neg_distrib]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun n => ∑ r : A₀,
      compDiag gens (SKM.mkD D ν (SKM.dcapL i n) (SKM.sChain_dcapL i n)) q r Z ≫
        compDiag gens (SKM.mkD D ν (SKM.etaL i n) (SKM.sChain_etaL i n)) r q' Z) N
  refine ⟨fun q p => ?_, fun n q r => ?_⟩
  · exact isSupernatural_of_inverse_source ρ a b ha hab hba q (.inl p)
  · exact isSupernatural_of_inverse_source ρ a b ha hab hba q (.inr (n, r))

/-! ## The equal-colour leftward data -/

/-- **The equal-colour leftward data are supernatural** (`LeftwardData.IsSupernatural`) when
they invert the augmented maps (1.13), (1.14) (`LeftwardData.IsInverse`) and the coefficient
`a` of the equal-colour mixed block is supernatural. -/
theorem LeftwardData.isSupernatural_of_isInverse (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (hL : L.IsInverse c) : L.IsSupernatural where
  lcrossSame i ν t s p p' := by
    have e : ∀ Z, L.lcrossSame i ν p p' Z = compDiag (P.swappedGens c L)
        (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i)) p p' Z := fun Z => by
      rw [compDiag_lcrossL, swappedGens_lcross_self]
    simp only [e]
    rcases le_total 0 (D.h i ν) with hh | hh
    · exact (leftward_supernatural_of_nonneg c L hc hL i ν hh).1 p p'
    · exact (leftward_supernatural_of_nonpos c L hc hL i ν hh).1 p p'
  dcup i n ν hn t s p p' := by
    have e : ∀ Z, L.dcup i n ν p p' Z = compDiag (P.swappedGens c L)
        (SKM.mkD D ν (SKM.dcupL i n) (SKM.sChain_dcupL i n)) p p' Z := fun Z => by
      rw [compDiag_dcupL, P.swappedGens_dcup_of_lt c L i n ν hn]
    simp only [e]
    have := (leftward_supernatural_of_nonneg c L hc hL i ν (by omega)).2
      ⟨n, Int.lt_toNat.mpr hn⟩ p p'
    rwa [mul_comm] at this
  dcap i n ν hn t s p p' := by
    have e : ∀ Z, L.dcap i n ν p p' Z = compDiag (P.swappedGens c L)
        (SKM.mkD D ν (SKM.dcapL i n) (SKM.sChain_dcapL i n)) p p' Z := fun Z => by
      rw [compDiag_dcapL, P.swappedGens_dcap_of_lt c L i n ν hn]
    simp only [e]
    have := (leftward_supernatural_of_nonpos c L hc hL i ν (by omega)).2
      ⟨n, Int.lt_toNat.mpr hn⟩ p p'
    rwa [mul_comm] at this

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
