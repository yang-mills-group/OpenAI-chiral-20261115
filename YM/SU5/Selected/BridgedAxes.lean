import YM.SU5.Selected.CommonAdjoint
import YM.SU5.Selected.Character

/-! # One phase algebra for all Axes

Doesn't require connected rotation symmetries (nor asserting the component birth is there as a
normal state on original Hilbert, nor the Euclidean-Minkowski symmetry of selected state).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 280000
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
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
variable (v : Axis) (C' : Arena Y H Q.circuit v 0 r)
local notation "R'" => Aurora Y H V Q v r C'
local notation "B'" => groundAlgebra Y H V Q Qc v r C'
local notation "N'" n:max => cap Y H V n Q Qc v r C'
local notation "M'" s:max => liftCap Y H V Q Qc v r C' s
local notation "Ω'" => seat0 Y H V Q v r C'

-- Gram for dense single-vector ranges. Vanilla types/Hilbert.
private lemma implementing (X Y : Hilbert) (I : Type) (f : I → X) (g : I → Y) (p : DenseRange f)
    (q : DenseRange g) (h : ∀ i j, inner ℂ (f i) (f j)=inner ℂ (g i) (g j)) :
    ∃ U : X ≃ₗᵢ[ℂ] Y, ∀ i, U (f i)=g i := by
  let P : _root_.YM.Kernel.Gram (fun i j => inner ℂ (f i) (f j)) :=
    ⟨X, f, p.mono Submodule.subset_span, fun _ _ => rfl⟩
  let L := Finsupp.linearCombination ℂ f
  let T := Finsupp.linearCombination ℂ g
  have hv (x y : I →₀ ℂ) : inner ℂ (L x) (L y) = inner ℂ (T x) (T y) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y p q => simp only [map_add,inner_add_left,p,q]
    | single i c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add x y p q => simp only [map_add,inner_add_right,p,q]
      | single i c => simp [L,T,h]
  obtain ⟨U,v,H0⟩ := P.by_bound g 1 zero_le_one (fun z => by
    rw [one_mul]; change ‖T z‖ ≤ ‖L z‖; rw [@norm_eq_sqrt_re_inner ℂ Y _ _ _,@norm_eq_sqrt_re_inner ℂ X _ _ _,hv]) -- check signature
  let T0 : X →L[ℂ] Y := U
  have hT : (fun i : X => ‖T0 i‖) = fun i : X => ‖i‖ := p.equalizer (Continuous.norm T0.continuous) (by fun_prop) (funext fun i => by
    change ‖T0 (f i)‖=_; rw [show T0 (f i)=g i from H0 i]; change ‖g i‖=‖f i‖; rw [@norm_eq_sqrt_re_inner ℂ Y _ _ _,@norm_eq_sqrt_re_inner ℂ X _ _ _,h])
  let E : X →ₗᵢ[ℂ] Y := ⟨T0, congrFun hT⟩
  have hx : DenseRange E := q.mono (by rintro i ⟨a,rfl⟩; exact ⟨f a,H0 a⟩)
  have hs : Surjective E:= fun y => (closure_minimal (Set.Subset.refl _)
    E.isometry.isClosedEmbedding.isClosed_range (hx y))
  refine ⟨LinearIsometryEquiv.ofSurjective E hs, fun i => ?_⟩
  exact H0 i

local notation "J" => (↑(R) ≃ₗᵢ[ℂ] ↑(R'))
local notation "φ₀" s:max => (N s.1) s.2 Ω
local notation "φ₁" s:max => (N' s.1) s.2 Ω'
local notation "αop" => (↑(R) →L[ℂ] ↑(R))
local notation "βop" => (↑(R') →L[ℂ] ↑(R'))
include V Q Qc C C'
lemma exists_groundIso : ∃ U : J, ∀ x : Lab, U (φ₀ x)=φ₁ x :=
  implementing (show Hilbert from { space := (R) }) (show Hilbert from { space := (R') }) (Lab) (fun x => φ₀ x) (fun x => φ₁ x) (cap_cyclic Y H V Q Qc j r C) (cap_cyclic Y H V Q Qc v r C') (same_inner Y H V Q Qc j r C v C')

def groundIso : J := (exists_groundIso Y H V Q Qc j r C v C').choose
local notation "G" => groundIso Y H V Q Qc j r C v C'
local notation "F" => (G).conjStarAlgEquiv
lemma pinned (x : Lab) : (G) (φ₀ x) = φ₁ x := (exists_groundIso Y H V Q Qc j r C v C').choose_spec x

lemma on_ground (x : Lab) : (F) ((N x.1) x.2) = (N' x.1) x.2 := by
  let b := (F) ((N x.1) x.2); let c := (N' x.1) x.2
  have h := cap_cyclic Y H V Q Qc v r C'
  change b=c; apply DFunLike.coe_injective
  refine h.equalizer b.continuous c.continuous (funext fun i=> h.eq_of_inner_right ℂ ?_)
  intro u; change inner ℂ (φ₁ u) (b (φ₁ i)) = inner ℂ (φ₁ u) (c (φ₁ i))
  have hx : b (φ₁ i) = (G) ((N x.1) x.2 (φ₀ i)) := by
    rw [←pinned]; unfold b; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]
  let X0 := dual Y H j r u.2
  have hs := across_three Y H V Q Qc j r C v C' (u.1,X0) x i
  change inner ℂ Ω ((N u.1) X0 ((N x.1) x.2 (φ₀ i))) = inner ℂ Ω' ((N' u.1) X0 (c (φ₁ i))) at hs
  rw [show (N u.1) X0 =_ from dual_any Y H V Q Qc j r C j u.1 u.2,
      show (N' u.1) X0 =_ from dual_any Y H V Q Qc v r C' j u.1 u.2,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right] at hs
  rw [hx]; nth_rw 1 [←pinned]
  rw [LinearIsometryEquiv.inner_map_map]; exact hs

omit V Q Qc C C'
private lemma restrictIso {X1 X2 : Type} [NormedAddCommGroup X1] [InnerProductSpace ℂ X1]
    [CompleteSpace X1] [NormedAddCommGroup X2] [InnerProductSpace ℂ X2] [CompleteSpace X2]
    {L1 : Set (X1 →L[ℂ] X1)} {L2 : Set (X2 →L[ℂ] X2)} (U : X1 ≃ₗᵢ[ℂ] X2)
    (h : Set.MapsTo U.conjStarAlgEquiv L1 L2) :
    (StarAlgebra.adjoin ℂ L1).topologicalClosure ≤ ((StarAlgebra.adjoin ℂ L2).topologicalClosure).comap
      U.conjStarAlgEquiv.toStarAlgHom := by
  refine StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le (fun x p => ?_)) ?_
  · exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ L2 (h p))
  exact isClosed_closure.preimage (StarAlgEquiv.isometry U.conjStarAlgEquiv).continuous -- type ambiguous
include V Q Qc C C'
lemma permeates : (B) ≤ (B').comap (F).toStarAlgHom := by
  apply restrictIso
  rintro _ ⟨x,rfl⟩; exact ⟨x, (on_ground Y H V Q Qc j r C v C' x).symm⟩
lemma permeatesBack : (B') ≤ (B).comap (F).symm.toStarAlgHom := by
  rw [LinearIsometryEquiv.symm_conjStarAlgEquiv]
  apply restrictIso
  rintro _ ⟨x,rfl⟩; refine ⟨x, Eq.symm ?_⟩; change (G).symm.conjStarAlgEquiv ((N' x.1) x.2) = _; rw [← LinearIsometryEquiv.symm_conjStarAlgEquiv]; exact (F).symm_apply_eq.mpr (on_ground Y H V Q Qc j r C v C' x |>.symm) -- maybe name
-- tune!
def coincide : ↑(B) ≃⋆ₐ[ℂ] ↑(B') := by
  let f := ((F).toStarAlgHom.comp (B).subtype).codRestrict (B')
    (fun x => permeates Y H V Q Qc j r C v C' x.property)
  apply StarAlgEquiv.ofBijective f
  constructor
  · intro x y p; exact Subtype.ext ((F).injective (congrArg Subtype.val p))
  intro x
  refine ⟨⟨_, permeatesBack Y H V Q Qc j r C v C' x.property⟩,?_⟩
  exact Subtype.ext ((F).apply_symm_apply x.val)

local notation "C₆" => coincide Y H V Q Qc j r C v C'
lemma literally (x : ↑(B)) : ((C₆) x).val = (F) x.val := rfl
lemma phase_hit (s : ℕ) (x : Test) : (C₆) ((M s) x)=(M' s) x := Subtype.ext (on_ground Y H V Q Qc j r C v C' (s,x))

lemma roomFix : (G) Ω = Ω' := by
  let x : Lab := ⟨0,legalOne r⟩
  have hu := pinned Y H V Q Qc j r C v C' x; change (G) ((((M 0) (legalOne r))).val Ω) = ((M' 0) (legalOne r)).val Ω' at hu
  rw [read_unit,read_unit] at hu; exact hu

lemma expectations (x : ↑(B)) : inner ℂ Ω (x.val Ω) = inner ℂ Ω' (((C₆) x).val Ω') := by
  rw [literally,←roomFix Y H V Q Qc j r C v C',LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]

def escort (χ : CapCharacter Y H V Q Qc j r C) : CapCharacter Y H V Q Qc v r C' :=
  χ.comp (C₆).symm.toStarAlgHom

lemma unchanged (χ : CapCharacter Y H V Q Qc j r C) (s : ℕ) (x : Test) :
    marked Y H V Q Qc v r C' (escort Y H V Q Qc j r C v C' χ) s x = marked Y H V Q Qc j r C χ s x := by
  unfold marked escort; rw [←phase_hit Y H V Q Qc j r C v C']; exact congrArg χ ((C₆).symm_apply_apply _)
end YM.CF.Buffered.Afterglow.Tower.Selection
