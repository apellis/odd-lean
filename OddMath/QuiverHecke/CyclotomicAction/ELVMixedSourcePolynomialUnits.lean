import OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceOddNorms
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.SKM.RouquierHomDistinctSourceUnits
import OddMath.QuiverHecke.SwappedAssembly.Sigma.TransposeNorms

/-! # Contentwise units of ELV mixed-source polynomials

SwappedDistinctMixedMates (13)–(15): source polynomials with a positive
reservoir-dot remainder are units. Their inverses are assembled at each
input and output content; a common nilpotence exponent is not required.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open SwappedAssembly CyclotomicAction
universe u v w r

section Product
variable {k : Type r} [CommRing k]
  {J : Type u} {C : J → Type v} [∀ j, Category.{w} (C j)]
  [∀ j, Preadditive (C j)] [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)]
  {A : Type*} [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]

private theorem even_end_pow {F : Superfunctor k A (∀ j, C j)} {f : End F}
    (hf : f ∈ parity (R := k) F F 0) (n : ℕ) :
    f ^ n ∈ parity (R := k) F F 0 := by
  induction n with
  | zero => exact id_mem F
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, add_zero] using comp_mem hf ih

private theorem admissible_even {F : Superfunctor k A (∀ j, C j)} {a b : End F}
    (ha : a ∈ parity (R := k) F F 0) (hb : b ∈ parity (R := k) F F 0)
    {N : End F} (hN : N ∈ SKM.admissibleMonomials (k := k) a b
      (fun _ => True) (fun _ => True) 1) : N ∈ parity (R := k) F F 0 := by
  apply Submodule.span_le.mpr ?_ hN
  rintro _ ⟨p, q, _, _, _, rfl⟩
  change a ^ p * b ^ q ∈ parity (R := k) F F 0
  simpa only [End.mul_def, add_zero] using comp_mem (even_end_pow hb q) (even_end_pow ha p)

private theorem admissible_map {R S : Type*} [Ring R] [Ring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) {a b N : R}
    (hN : N ∈ SKM.admissibleMonomials (k := k) a b
      (fun _ => True) (fun _ => True) 1) :
    φ N ∈ SKM.admissibleMonomials (k := k) (φ a) (φ b)
      (fun _ => True) (fun _ => True) 1 := by
  induction hN using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, hp, hq, hn, rfl⟩ := hz
    rw [map_mul, map_pow, map_pow]
    exact Submodule.subset_span ⟨p, q, hp, hq, hn, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Componentwise nilpotence supplies every even source polynomial unit,
including arbitrary linear combinations of positive post-dot monomials. -/
theorem product_source_polynomial_isUnit
    (F : Superfunctor k A (∀ j, C j)) (a b : End F)
    (ha : a ∈ parity (R := k) F F 0) (hb : b ∈ parity (R := k) F F 0)
    (hu : IsUnit a) (hab : Commute a b)
    (hn : ∀ M j, IsNilpotent (show End (F.obj M j) from b.app 0 M j))
    (c : kˣ) (n : ℕ) {N : End F}
    (hN : N ∈ SKM.admissibleMonomials (k := k) a b
      (fun _ => True) (fun _ => True) 1) : IsUnit ((c : k) • a ^ n + N) := by
  have hN0 := admissible_even ha hb hN
  have hpoly : (c : k) • a ^ n + N ∈ parity (R := k) F F 0 :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (even_end_pow ha n)) hN0
  apply superfunctorProductEnd_isUnit C F _ hpoly
  intro M j
  let φ : End F →ₐ[k] End (F.obj M j) :=
    (piEndEvaluation (F.obj M) j).comp (supernaturalEndEvaluation F M)
  have heval (f : End F) (hf : f ∈ parity (R := k) F F 0) : φ f = f.app 0 M j := by
    exact congrArg (fun z : End (F.obj M) => z j)
      (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf M)
  have hnil : IsNilpotent (φ b) := by rw [heval b hb]; exact hn M j
  have hh := SKM.isUnit_smul_pow_add_of_mem_admissibleMonomials (k := k)
    (Pa := fun _ => True) (Pb := fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun p q _ _ => (hab.map φ.toRingHom).pow_pow p q)
    hnil (hu.map φ.toRingHom) c (d := n) trivial (admissible_map φ hN)
  change IsUnit ((c : k) • (φ a) ^ n + φ N) at hh
  have hφ : φ ((c : k) • a ^ n + N) = (c : k) • (φ a) ^ n + φ N := by
    rw [map_add, map_smul, map_pow]
  rw [← hφ, heval _ hpoly] at hh
  exact hh

end Product

local instance elvPolynomialHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

attribute [local irreducible] SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot

private theorem source_post_even {k : Type u} [CommRing k]
    {A B C T : PiSCat.{u,u,u + 1} k}
    (E : A ⟶ B) {E' : C ⟶ T} {F' : T ⟶ C}
    (adj : SKM.SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : B ⟶ T)
    (y : End E') (hy : y ∈ parity (R := k) E' E' 0) :
    SKM.mixedPostSourcePostDot (k := k) E κ H adj y ∈
      parity (R := k)
        (E ≫ ((SKM.homParityShift (k := k) (C := B ⟶ T) κ).obj H ≫ F'))
        (E ≫ ((SKM.homParityShift (k := k) (C := B ⟶ T) κ).obj H ≫ F')) 0 := by
  delta SKM.mixedPostSourcePostDot
  exact Superfunctor.whiskerLeft_mem E
    (Superfunctor.whiskerLeft_mem _ (SKM.SuperAdjunction.rightTranspose_mem adj adj hy))

private theorem source_post_app {k : Type u} [CommRing k]
    {A B C T : PiSCat.{u,u,u + 1} k}
    (E : A ⟶ B) {E' : C ⟶ T} {F' : T ⟶ C}
    (adj : SKM.SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : B ⟶ T)
    (y : End E') (p : ZMod 2) (M : A) :
    (SKM.mixedPostSourcePostDot (k := k) E κ H adj y).app p M =
      (SKM.SuperAdjunction.rightTranspose adj adj y).app p
        (((SKM.homParityShift (k := k) (C := B ⟶ T) κ).obj H).obj (E.obj M)) := by
  delta SKM.mixedPostSourcePostDot
  rfl

section ELV
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

private theorem transpose_power_component_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (n : ℕ) (hn : 0 < n)
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (δ : WeightBlocks D Λ x) :
    IsNilpotent (show End (((elvF D Sc cutoff bound i Λ h).obj M) δ) from
      (SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n)).total M δ) := by
  let φ := (piEndEvaluation ((elvF D Sc cutoff bound i Λ h).obj M) δ).comp
    (supernaturalEndEvaluation (elvF D Sc cutoff bound i Λ h) M)
  have ht : IsNilpotent (φ (elvActionDotTranspose D Sc cutoff bound i Λ h)) := by
    obtain ⟨e, _, he⟩ := elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h hdot δ
    refine ⟨e, ?_⟩
    change (show End (((elvF D Sc cutoff bound i Λ h).obj M) δ) from
      (elvActionDotTranspose D Sc cutoff bound i Λ h).total M δ) ^ e = 0
    rw [OddMath.HomogeneousSuperfunctorIso.total_eq_app _
      (elvActionDotTranspose_mem D Sc cutoff bound i Λ h) M]
    exact he M
  have hp := SKM.SuperAdjunction.rightTranspose_power
    (elvActionAdjunction D Sc cutoff bound i Λ h)
    (elvActionDot_mem D Sc cutoff bound i Λ h) n
  simp only [SKM.rouquierPower_eq_pow] at hp
  change IsNilpotent (φ _)
  rw [SKM.rouquierPower_eq_pow, hp, map_zsmul, map_pow]
  exact (ht.pow_of_pos (Nat.ne_of_gt hn)).smul _

attribute [local irreducible] elvF elvActionAdjunction elvActionDot

/-- Every admissible source polynomial built from an even probe unit and a
positive even reservoir dot power is a unit on the entire input Hom functor. -/
theorem elvMixedSource_polynomialUnits [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    {A B : PiSCat.{u,u,u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
    (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)
    (a : End E) (ha : a ∈ parity (R := k) E E 0) (hu : IsUnit a)
    (n : ℕ) (hn : 0 < n) (heven : (n : ZMod 2) * D.parity i = 0) :
    SKM.MixedPostSourceUnits E (elvActionAdjunction D Sc cutoff bound i Λ h) κ H a
      (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n) := by
  let K := (SKM.homParityShift (k := k)
    (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H
  let F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x :=
    E ≫ (K ≫ elvF D Sc cutoff bound i Λ h)
  let b := SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n
  have hb : b ∈ parity (R := k) _ _ 0 := by
    simpa only [heven] using SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff bound i Λ h) n
  let t : End (elvF D Sc cutoff bound i Λ h) :=
    SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionAdjunction D Sc cutoff bound i Λ h) b
  have htb : t ∈ parity (R := k) _ _ 0 := SKM.SuperAdjunction.rightTranspose_mem
    (elvActionAdjunction D Sc cutoff bound i Λ h)
    (elvActionAdjunction D Sc cutoff bound i Λ h) hb
  let pre : End F := SKM.mixedPostSourcePreDot (k := k) E κ H
    (F' := elvF D Sc cutoff bound i Λ h) a
  let post : End F := SKM.mixedPostSourcePostDot (k := k) E κ H
    (elvActionAdjunction D Sc cutoff bound i Λ h) b
  have hpre : pre ∈ parity (R := k) F F 0 := by
    dsimp only [pre]
    delta SKM.mixedPostSourcePreDot
    exact TwoSupercategory.whiskerRight_mem (R := k) (K ≫ elvF D Sc cutoff bound i Λ h) ha
  have hpost : post ∈ parity (R := k) F F 0 :=
    source_post_even E (elvActionAdjunction D Sc cutoff bound i Λ h) κ H b hb
  have hpreu : IsUnit pre := SKM.mixedPostSourcePreDot_isUnit E κ H hu
  have hcomm : Commute pre post := SKM.commute_mixedPostSource E
    (elvActionAdjunction D Sc cutoff bound i Λ h) κ H ha (y := b)
  have hnil : ∀ M δ, IsNilpotent (show End (F.obj M δ) from post.app 0 M δ) := by
    intro M δ
    dsimp only [post]
    rw [source_post_app E (elvActionAdjunction D Sc cutoff bound i Λ h) κ H b 0 M]
    rw [← OddMath.HomogeneousSuperfunctorIso.total_eq_app t htb (K.obj (E.obj M))]
    exact transpose_power_component_isNilpotent D Sc cutoff bound i Λ h hdot n hn _ δ
  intro c e N hN
  exact product_source_polynomial_isUnit F pre post hpre hpost hpreu hcomm hnil c e hN

end ELV
end OddMath.QuiverHecke.ELVOld
