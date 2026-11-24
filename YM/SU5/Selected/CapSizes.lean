import YM.SU5.Selected.PurchaseBounds
import YM.SU5.Selected.Transfer
/-!
# Separability from the actual transfer

Destroy commonly assumed obstruction: although all wide pair tests can range over Borel
coefficients, use transfer into the NEXT rung where the operators out of ground *in norm
topology* have separable span/generated C*-algebra. This is for the Exhibition showing on
exactly these rankings; not an external assumption about nets on Borel unit balls.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false

open Tapestry TopologicalSpace Set
local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "L₀" s:max => prepare Y H V Q Qc j false C s
local notation "L" => basisRoom Y H V Q j false C
local notation "J" => (↑(R) →L[ℂ] A)
local notation "Ψ" => pipeline Y H V Q Qc j false C
variable {Z : Tapestry.Rack Λ l} {P : Tapestry.Clay Λ l} (U : Exhibition Y H i k I E Z P)

private lemma compRan {X X' : Type} [NormedAddCommGroup X] [NormedAddCommGroup X']
    [NormedSpace ℂ X] [NormedSpace ℂ X'] {g : X →L[ℂ] X'} (p : IsCompactOperator g) :
    IsSeparable (range g) := by
  let S (x:ℕ):= g '' closedBall (0:X) x
  have hp (x:ℕ) : IsSeparable (closure (S x)):= (IsCompactOperator.isCompact_closure_image_closedBall (f:=g.toLinearMap) p x).totallyBounded.isSeparable
  refine (IsSeparable.iUnion hp).mono ?_
  rintro _ ⟨x,rfl⟩; obtain ⟨n,t⟩:=exists_nat_gt ‖x‖
  exact mem_iUnion.mpr ⟨n,subset_closure (mem_image_of_mem _ (by simpa using t.le : x∈ closedBall (0:X) n))⟩

private lemma mon_closure {X : Type} [CStarAlgebra X] (S : Set X) (p : IsSeparable S) :
    IsSeparable (↑(Submonoid.closure S) : Set X) := by
  obtain ⟨x,h,q⟩ := p
  let B' := Submonoid.closure x
  have he : Set.Countable (↑(B') : Set X) := by
    haveI : Countable ↥x := h.to_subtype
    rw [show ((B' : Set X)) = _ from Submonoid.closure_eq_image_prod x, ← Set.range_list_map_coe,←Set.range_comp]; apply countable_range
  refine ⟨B',he,?_⟩
  change Submonoid.closure S ≤ B'.topologicalClosure
  exact Submonoid.closure_le.mpr (Set.Subset.trans q (closure_mono (show x ⊆ (B':Set X) from Submonoid.subset_closure)))
private lemma starSize {X : Type} [CStarAlgebra X] (S : Set X) (p : IsSeparable S) :
    IsSeparable (↑((StarAlgebra.adjoin ℂ S).topologicalClosure) : Set X):= by
  let s:=(StarAlgebra.adjoin ℂ S).toSubalgebra.toSubmodule
  change IsSeparable (closure (s:Set X))
  apply IsSeparable.closure; unfold s; rw [StarAlgebra.adjoin_eq_span, ← Set.image_star]
  exact IsSeparable.span («R»:=ℂ) (mon_closure _ (p.union (p.image continuous_star)))

lemma nextFace (S : Finset Cover) (s : ℕ) (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) :
    Tower.region j (meshface (Λ:=Λ) 0 (s+1)) (K).ℓ (wingspan Λ l S) := by
  have h := wingspan_region Y H S j (meshface (Λ:=Λ) 0 s) p; rwa [area0, mul_zero,←area0 (Λ:=Λ) (i:=s+1)] at h
include V Q Qc C U
omit V Q Qc C U in
private lemma lap {X Y T : Type} [TopologicalSpace Y] [TopologicalSpace T] (x : X→Y) (y : Y→T) (v : X→T) (h:IsSeparable (range x))(t:Continuous y)(p:∀ w,y (x w)=v w): IsSeparable (range v):= (h.image t).mono (by rintro _ ⟨w,rfl⟩; exact ⟨x w,Set.mem_range_self w,p w⟩)

private lemma life (S : Finset Cover) (s : ℕ) (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) (x : Swatch S) :
    money Y H V Q Qc j C (s+1) (followBox (Λ:=Λ) (l:=l) S) (nextFace Y H j S s p) (P S s x)=money Y H V Q Qc j C s S p x := by
  let T := atomField Y H j s S p x
  have he : Raise Y H Q.circuit j 0 false s (s+1) (by omega) T = atomField Y H j (s+1) (followBox (Λ:=Λ) (l:=l) S) (nextFace Y H j S s p) (P S s x) := by
    apply Subtype.ext; change stream Y H D s (s+1-s) (render S K x)=_
    rw [show s+1-s=1 from by omega]; exact transfer_is Y H Q U s S x
  exact (congrArg (L₀ (s+1)) he.symm).trans (plant_high Y H V Q Qc j false C s (s+1) (by omega) T)
lemma nextSize (S : Finset Cover) (s : ℕ) (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) :
    IsSeparable (range (money Y H V Q Qc j C s S p)) :=
  lap (P S s) (money Y H V Q Qc j C (s+1) (followBox (Λ:=Λ) (l:=l) S) (nextFace Y H j S s p)) _ (compRan (X:=Swatch S) (X':=Swatch (followBox (Λ:=Λ) (l:=l) S)) (U.compactBridge Y H S s)) (continuously Y H V Q Qc j C _ _ _) (life Y H V Q Qc j C U S s p)
lemma pipeline_separable : IsSeparable (↑(Ψ) : Set J) := by
  let S := fun s (Z : Finset Cover) (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ Z) => range (money Y H V Q Qc j C s Z p)
  have h:IsSeparable (⋃ (s:ℕ) (t : Finset Cover) (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ t), S s t p) := .iUnion fun i=> .iUnion fun t=> .iUnion fun p=> nextSize Y H V Q Qc j C U t i p
  refine h.mono (fun x (hx:x∈Ψ) =>?_)
  obtain ⟨s,y,p,a⟩:= leg_available Y H V Q Qc j false C ⟨x,hx⟩ 0
  obtain ⟨S0,t,v⟩:= ((purpose_ok ..).1 y.property).1
  obtain ⟨f,e⟩:= rendered S0 K t
  exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨S0,mem_iUnion.mpr ⟨v,f,(congrArg (L₀ s) (show atomField Y H j s S0 v f=y from Subtype.ext e)).trans a.symm⟩⟩⟩
omit V Q C Qc U in
private lemma sizeLegs (X Y : Hilbert) (S : Set (X→L[ℂ] Y)) (p : IsSeparable S): SeparableSpace S := p.separableSpace
lemma small_pipe : SeparableSpace (Ψ) := sizeLegs (L) (A) _ (pipeline_separable Y H V Q Qc j C U)
lemma smallCaps : IsSeparable (familyCaps Y H V Q Qc j false C) := by
  let f (x : J) := (π₀).comp x
  have hp: Continuous f := Continuous.clm_comp continuous_const continuous_id
  refine ((pipeline_separable Y H V Q Qc j C U).image hp).mono ?_
  rintro f' ⟨⟨s,x⟩,rfl⟩; let X := Classical.choice (anyporch Y H s j false x)
  let Hx := (L₀ s) X.fwd.val
  have hu : toTest Y H j false s X.fwd.val=moved Y H j false X.rise x:=Subtype.ext X.yes
  refine ⟨Hx,(asLeg Y H V Q Qc j false C s X.fwd.val).property,?_⟩
  change (π₀).comp ((L₀ s) X.fwd.val) = (N s) x
  rw [← compute_caps, hu,cap_shift]
lemma small_algebra : SeparableSpace (B) := by
  let L' : Hilbert := L
  have he : IsSeparable (↑(B):Set L'.Op) := starSize (X:= (L).Op) (familyCaps Y H V Q Qc j false C) (smallCaps Y H V Q Qc j C U)
  exact he.separableSpace
end YM.CF.Buffered.Afterglow.Tower.Selection
