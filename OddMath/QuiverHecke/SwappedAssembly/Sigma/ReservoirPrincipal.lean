import OddMath.QuiverHecke.SwappedAssembly.Sigma.Entry
import OddMath.QuiverHecke.SwappedAssembly.ReservoirDottedFactorCoordinates

/-! # The actual pure reservoir principal block -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}


/-- A closed four-letter reservoir path used by the pure principal
cup/cross/cap chain. Its region colours are arbitrary. -/
def reservoirFourPath (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (r₁ r₂ r₃ r₄ : X) :
    SPath [⟨dn i, r₁⟩, ⟨up i, r₂⟩, ⟨up i, r₃⟩, ⟨dn i, r₄⟩] t t := by
  have hle : Finsupp.single i 1 ≤ t.2 := (Finsupp.single_le_iff).mpr hv
  have h₂ : StepValid (true, i) false (nextSector (false, i) false t) := by
    simp [StepValid, nextSector]
  have h₃ : StepValid (true, i) false
      (nextSector (true, i) false (nextSector (false, i) false t)) := by
    simpa only [nextSector, add_tsub_cancel_right] using hv
  have he : nextSector (false, i) false (nextSector (true, i) false
      (nextSector (true, i) false (nextSector (false, i) false t))) = t := by
    simp only [nextSector, add_tsub_cancel_right, tsub_add_cancel_of_le hle]
  exact .cons _ false t trivial (.cons _ false _ h₂ (.cons _ false _ h₃
    (.cons _ false _ trivial (he.symm ▸ .nil t))))

omit [AddCommGroup X] in
theorem reservoirFourPath_sides (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (r₁ r₂ r₃ r₄ : X) :
    (reservoirFourPath i t hv r₁ r₂ r₃ r₄).sides = [false, false, false, false] := by
  unfold reservoirFourPath
  dsimp only [SPath.sides]
  rw [(SPath.sides_of_nil _).1]

private theorem one_final_ne_zero (gens : P.Generators) (L : Layer (SKM.sig D))
    {a b : Obj (SKM.sig D)} (h : Chain a [L] b) {s t : Sector I}
    (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t)
    (hz : compList gens [L] h p q Z ≠ 0) :
    compLayer gens L (p.cast (congrArg Obj.word h.2.1.symm))
      (q.cast (congrArg Obj.word h.2.2.symm)) Z ≠ 0 := by
  intro he
  rw [compList_one, he, Limits.zero_comp, Limits.comp_zero] at hz
  exact hz rfl

private theorem two_final_ne_zero (gens : P.Generators) (L L' : Layer (SKM.sig D))
    {a b : Obj (SKM.sig D)} (h : Chain a [L, L'] b) {s t : Sector I}
    (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t)
    (hz : compList gens [L, L'] h p q Z ≠ 0) :
    ∃ n : SPath L.cod.word s t,
      compLayer gens L (p.cast (congrArg Obj.word h.2.1.symm)) n Z ≠ 0 ∧
      compLayer gens L' (n.cast (congrArg Obj.word h.2.2.2.1.symm))
        (q.cast (congrArg Obj.word h.2.2.2.2.symm)) Z ≠ 0 := by
  rw [compList_cons_eq] at hz
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨-, hn⟩ := ne_zero_of_comp_ne_zero hn
  obtain ⟨hL, hn⟩ := ne_zero_of_comp_ne_zero hn
  exact ⟨n, hL, one_final_ne_zero gens L' h.2.2 n q Z hn⟩

/-- For pure source and target sides, the outer strands of the crossing
layer force every contributing path through the same pure side. This
does not use the distinct-colour crossing permutation rule. -/
private theorem sigma_pure_sides (gens : P.Generators) (i : I) (ν : X) {s t : Sector I}
    (Z : P.H t) (σ : Bool)
    (n₁ : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]).cod.word s t)
    (h₁ : ∃ τ, n₁.sides = [τ, τ, σ, σ])
    (e₁ : (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]).cod.word =
      (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]).dom.word)
    (n₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]).cod.word s t)
    (e₂ : (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]).cod.word =
      (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []).dom.word)
    (n₃ : SPath (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []).cod.word s t)
    (h₃ : n₃.sides = [σ, σ])
    (z₂ : compLayer gens (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]) (n₁.cast e₁) n₂ Z ≠ 0)
    (z₃ : compLayer gens (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []) (n₂.cast e₂) n₃ Z ≠ 0) :
    n₁.sides = [σ, σ, σ, σ] ∧ n₂.sides = [σ, σ, σ, σ] := by
  obtain ⟨τ, hτ⟩ := h₁
  obtain ⟨ρ, hρ⟩ := sides_of_cap gens ν i [dn i, up i] (n₂.cast e₂) n₃ Z z₃
  rw [SPath.sides_cast, h₃] at hρ
  obtain ⟨x, y, pu, pg, qg, pv, hin, hout⟩ := compLayer_ne_zero_sides gens _ (n₁.cast e₁) n₂ Z z₂
  obtain ⟨a, ha⟩ := SPath.exists_sides_one pu
  obtain ⟨b, hb⟩ := SPath.exists_sides_one pv
  obtain ⟨c, d, hcd⟩ := SPath.exists_sides_pair pg
  obtain ⟨f, g, hfg⟩ := SPath.exists_sides_pair qg
  rw [SPath.sides_cast, hτ, ha, hb, hcd] at hin
  rw [hρ, ha, hb, hfg] at hout
  have hτa : τ = a := by simpa using congrArg List.head? hin
  have hσa : σ = a := by simpa using congrArg List.head? hout
  have hσb : σ = b := by simpa using congrArg List.getLast? hin
  have hρb : ρ = b := by simpa using congrArg List.getLast? hout
  have hτσ : τ = σ := hτa.trans hσa.symm
  have hρσ : ρ = σ := hρb.trans hσb.symm
  subst hτσ hρσ
  exact ⟨hτ, by simpa using hρ⟩

/-- The actual same-colour pure principal entry has one contributing
cup/cross/cap chain. No mixed-coefficient identity is needed. -/
theorem sigmaEntry_pure_eq (c : P.CrossCoeff) (i : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s)
    (m₁ : SPath (wd D ν [dn i, up i, up i, dn i]) t s)
    (m₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]).cod.word t s) (Z : P.H s)
    (σ : Bool) (hp : p.sides = [σ, σ]) (hq : q.sides = [σ, σ])
    (h₁ : m₁.sides = [σ, σ, σ, σ]) (h₂ : m₂.sides = [σ, σ, σ, σ]) :
    P.sigmaEntry c i i ν p q Z =
      compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]) p m₁ Z ≫
        compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]) m₁ m₂ Z ≫
          eqToHom (by rw [P.pathFunctor_cast]) ≫
            compLayer (P.upwardGens c) (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) [])
              (m₂.cast (sigma_cross_cap_word i i ν)) (q.cast (sigma_cap_word i i ν)) Z ≫
              eqToHom (by rw [P.pathFunctor_cast]) := by
  classical
  have hc₂ : Chain (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]).cod
      [SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i],
        SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []] (SKM.ob D ν [dn i, up i]) :=
    ((SKM.sChain_sigmaL i i).chain D ν).2.2
  let inst1 := Fintype.ofFinite
    (SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]).cod.word t s)
  have e : P.sigmaEntry c i i ν p q Z =
      ∑ n₁ : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]).cod.word t s,
        eqToHom rfl ≫
          compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]) p n₁ Z ≫
            compList (P.upwardGens c) _ hc₂ n₁ q Z := rfl
  refine e.trans ((Finset.sum_eq_single
    (m₁ : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up i, dn i]).cod.word t s) ?_ ?_).trans ?_)
  · intro n₁ _ hn
    by_contra hz
    obtain ⟨-, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨z₁, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨n₂, z₂, z₃⟩ := two_final_ne_zero (P.upwardGens c)
      (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i])
      (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []) hc₂ n₁ q Z hz
    obtain ⟨τ, hτ⟩ := sides_of_cup _ ν i [up i, dn i] _ n₁ Z z₁
    rw [hp] at hτ
    obtain ⟨h₁', -⟩ := sigma_pure_sides _ i ν Z σ n₁ ⟨τ, hτ⟩ _ n₂ _ _
      (by simpa only [SPath.sides_cast] using hq) z₂ z₃
    exact hn (SPath.eq_of_sides _ _ (h₁'.trans h₁.symm))
  · exact fun h => (h (@Finset.mem_univ _ inst1 _)).elim
  refine ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)).trans ?_
  refine congrArg (_ ≫ ·) ?_
  let inst2 := Fintype.ofFinite
    (SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]).cod.word t s)
  have e₂ : compList (P.upwardGens c) _ hc₂ m₁ q Z =
      ∑ n₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]).cod.word t s,
        eqToHom rfl ≫
          compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i i) [dn i]) m₁ n₂ Z ≫
            compList (P.upwardGens c) _ hc₂.2.2 n₂ q Z := rfl
  refine e₂.trans ((Finset.sum_eq_single m₂ ?_ ?_).trans ?_)
  · intro n₂ _ hn
    by_contra hz
    obtain ⟨-, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨z₂, hz⟩ := ne_zero_of_comp_ne_zero hz
    have z₃ := one_final_ne_zero (P.upwardGens c)
      (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []) hc₂.2.2 n₂ q Z hz
    obtain ⟨-, h₂'⟩ := sigma_pure_sides (P.upwardGens c) i ν Z σ m₁ ⟨σ, h₁⟩ rfl n₂ _ _
      (by simpa only [SPath.sides_cast] using hq) z₂ z₃
    exact hn (SPath.eq_of_sides _ _ (h₂'.trans h₂.symm))
  · exact fun h => (h (@Finset.mem_univ _ inst2 _)).elim
  refine ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)).trans ?_
  refine congrArg (_ ≫ ·) ?_
  let inst3 := Fintype.ofFinite
    (SPath (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []).cod.word t s)
  have e₃ : compList (P.upwardGens c) _ hc₂.2.2 m₂ q Z =
      ∑ n₃ : SPath (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) []).cod.word t s,
        eqToHom (by rw [P.pathFunctor_cast]) ≫
          compLayer (P.upwardGens c) (SKM.lay D ν [dn i, up i] (SKM.Shape.cap i) [])
            (m₂.cast (sigma_cross_cap_word i i ν)) n₃ Z ≫
            compList (P.upwardGens c) [] hc₂.2.2.2.2 n₃ q Z := rfl
  refine e₃.trans ((Finset.sum_eq_single (q.cast (sigma_cap_word i i ν)) ?_ ?_).trans ?_)
  · intro n₃ _ hn
    rw [compList_nil_of_ne _ _ _ _ _ fun h => hn ?_, Limits.comp_zero, Limits.comp_zero]
    rw [← h, SPath.cast_cast, SPath.cast_self]
  · exact fun h => (h (@Finset.mem_univ _ inst3 _)).elim
  refine (congrArg (fun f => _ ≫ _ ≫ f)
    (compList_nil_of_eq (P.upwardGens c) hc₂.2.2.2.2 _ q Z
      (by rw [SPath.cast_cast, SPath.cast_self]))).trans ?_
  rfl


end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
