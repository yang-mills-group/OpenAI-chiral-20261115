/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.Separable
import YM.SU5.Selected.CommonGround
/-!
# Uncompressed algebras for the vacuum component comparison

Work on the full space of resolution-level fields. Include the spatial (grid)
translations as well, because the time ground alone is not known to have trivial grid
energy/momentum elsewhere. Their action does not change the plane margin, and isometries
are realized on the given space. Do **not** include projections to the time- or joint-
invariant space in this slab algebra (i.e., not built in by hand). **Separated** concatenation
(composition of SlabMark.boxOp) here combines placements to give the needed compatibility,
including with relative spacetime movement; no overlapping multiplicativity of E required.
Local lattice use of the subalgebras here is through the resolution presentations, still
using the actual state and compressed-state moment rules. This is not a Haag-Kastler algebra;
this part will afford extremal invariant-state selection on the joint hierarchy.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
section
open Set
open scoped Pointwise
-- adapted the abstract separability proofs from Work/B12 on other data
private lemma monoid_sep {X : Type*} [Monoid X] [TopologicalSpace X] [ContinuousMul X]
    {s : Set X} (h : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (Submonoid.closure s : Set X) := by
  have hp (n : ℕ) : TopologicalSpace.IsSeparable (s ^ n) := by
    induction n with
    | zero =>
      rw [pow_zero]; exact (countable_singleton (1 : X)).isSeparable
    | succ n ih =>
      rw [pow_succ, ← image_mul_prod]; exact (ih.prod h).image continuous_mul
  refine (TopologicalSpace.IsSeparable.iUnion hp).mono ?_
  intro x hx
  change x ∈ Submonoid.closure s at hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact mem_iUnion.mpr ⟨1, by simpa using hx⟩
  | one => exact mem_iUnion.mpr ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨n+m,by rw [pow_add]; exact Set.mul_mem_mul hn hm⟩

lemma star_isSeparable_alg {X : Type*} [CStarAlgebra X] {s : Set X} (h : IsSeparable s) :
    IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set X) := by
  apply IsSeparable.closure; change IsSeparable ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set X)
  rw [StarAlgebra.adjoin_eq_span, ← image_star]; exact (monoid_sep (h.union (h.image continuous_star))).span
end

namespace Spine
variable (P : Spine)(j : Axis)
local notation "K"=> P.calibration
local notation "Ω"=> P.floorVec j
local notation "π"=> P.history
local notation "V"=> P.law
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "C₀"=> P.room j
local notation "Qt"=> P.projection.clipped
local notation "A"=> P.Hil j

abbrev Op0 : Type := (P.Hil j).Op
-- use lattice shifts, repeated at finer meshes; their physical distances refer to
-- the units of the TIME mesh (fermion step at level 0). See TimeKeeper. Equivalent to
-- double this distance in gauge spacing.
def tiles : Set (P.Op0 j) := {x|∃ (s w:ℕ) (p:0<w) (f:P.Card j s w), P.Box j s w p f=x}
-- multiplicative semigroup even over all s (concatenate at any shared higher rung).
lemma tile_one (s w : ℕ) (p : 0 < w) (f : P.Card j s w) : P.Box j s w p f ∈ P.tiles j :=
  ⟨s,w,p,f,rfl⟩
lemma tiles_star_closed {x : P.Op0 j}(h : x ∈ P.tiles j) : star x ∈ P.tiles j := by
  obtain ⟨s,w,p,f,rfl⟩:=h; rw [show star (P.Box j s w p f)=P.Box j s w p (inverse Y H s j false w f) from
    respects Y H V s π Qt j false C₀ w f p]; exact P.tile_one j _ _ _ _
lemma tiles_together {x y:P.Op0 j} (h : x ∈ P.tiles j) (p : y∈ P.tiles j) : x*y ∈ P.tiles j:=by
  obtain ⟨s,w,p',f,rfl⟩:=h; obtain ⟨t,w',q,g,rfl⟩:=p; let a:=max s t; have u:s≤a:=le_max_left ..; have v:t≤a:=le_max_right ..
  unfold Box
  rw [refined_box Y H V s π Qt j false C₀ w f p' a u,refined_box Y H V t π Qt j false C₀ w' g q a v]
  exact ⟨a,_,_,_,(edit_comp Y H V a π Qt j false C₀ _ _ _ _ _ _).symm⟩

abbrev Grid := ℕ × ℤ × Trans j
abbrev crew (d : Trans j) := (ladder P.run P.large P.law P.history.circuit j 0 false (P.room j)).crew d
abbrev shiftOp (g : Grid j) : P.Op0 j:= (P.crew j g.2.2).play (notch (timeMesh P.par) g.1 g.2.1)
lemma shift_star (s : ℕ) (x : ℤ) (d : Trans j) : star (P.shiftOp j (s,x,d))=P.shiftOp j (s,-x,d):=by
  let S:=P.crew j d; let M:=timeMesh P.par; let N:=notch M s; change ContinuousLinearMap.adjoint (S.play (N x))= S.play (N (-x))
  rw [S.neg_adjoint]; have h:N x + N (-x) =0:=by unfold N; rw [← notch_add,add_neg_cancel,notch_zero]
  rw [eq_neg_of_add_eq_zero_right h]
lemma shift_plus (s : ℕ) (x y:ℤ) (d : Trans j) : P.shiftOp j (s,x,d)*P.shiftOp j (s,y,d)=P.shiftOp j (s,x+y,d):=by
  let C:=P.crew j d; let N:=notch (timeMesh P.par) s; change (C.play (N x)).comp (C.play (N y))=C.play (N (x+y))
  rw [C.piles,← notch_add (timeMesh P.par)]
lemma shift_zero (s : ℕ) (d : Trans j) : P.shiftOp j (s,0,d)=1:=by
  change (P.crew j d).play (notch (timeMesh P.par) s 0)=1; rw [notch_zero]; exact Germ.Players.play_zero _
lemma shift_unitary (g : Grid j) : P.shiftOp j g ∈ unitary (P.Op0 j) := by
  rcases g with ⟨s,n,d⟩; constructor <;> rw [P.shift_star,P.shift_plus]; · rw [neg_add_cancel,P.shift_zero]
  rw [add_neg_cancel,P.shift_zero]
lemma ground_ok (x : A) : x ∈ P.vacuum j ↔ (∀ t : ℝ≥0, advance Y H V P.history.circuit j 0 false C₀ t x=x) ∧ (∀ g: Grid j, P.shiftOp j g x=x) := by
  change x ∈ ⨅ i, Conserves Y H V i π j false C₀ ↔ _
  simp_rw [Submodule.mem_iInf,formal]
  have he(s n d): P.shiftOp j (s,n,d)=_:= on_ladder P.run P.large P.law s P.history.circuit j 0 false C₀ d n
  constructor
  · exact fun p=> ⟨(p 0).1,fun ⟨s,n,d⟩=> (he s n d).symm ▸ (p s).2 d n⟩
  exact fun v s=> ⟨v.1,fun d n=> (he s n d) ▸ v.2 (s,n,d)⟩
lemma tile_forward (g : Grid j) {x:P.Op0 j} (h:x∈ P.tiles j): ∃ y∈P.tiles j,P.shiftOp j g*x=y*P.shiftOp j g:=by
  obtain ⟨t,w,v,f,rfl⟩:= h; rcases g with ⟨s,n,d⟩; let a:=max t s; have u:t≤a:=le_max_left ..; have h:s≤a:=le_max_right ..
  let k:=castor (timeMesh P.par) s a n
  change ∃y∈ _, (P.crew j d).play _ * _=y* (P.crew j d).play _
  rw [show notch (timeMesh P.par) s n=notch (timeMesh P.par) a k from (notch_up _ s a h n).symm]
  unfold Box; rw [refined_box Y H V t π Qt j false C₀ w f v a u]
  exact ⟨_,P.tile_one j a _ _ _, SlabMark.shape_across Y H V a π Qt j false C₀ _ _ _ d k⟩
lemma tile_translated (g : Grid j) {x:P.Op0 j}(h:x∈P.tiles j):P.shiftOp j g*x * star (P.shiftOp j g)∈P.tiles j:=by
  obtain ⟨y,v,e⟩:= P.tile_forward j g h; rwa [e,mul_assoc,Unitary.mul_star_self_of_mem (P.shift_unitary j g),mul_one]

local notation "Φ" l:max=> P.shiftOp j l
local notation "W" l:max => (List.map (P.shiftOp j) l).prod
/-- Normal form: the (optional) slab, followed by all the spatial translations.
    No finiteness in the period or in the tower size. -/
abbrev idleOr := insert 1 (P.tiles j)
def normalForm : Set (P.Op0 j) := {x|∃ (f:P.Op0 j), f∈ P.idleOr j ∧ ∃ l:List (Grid j), x=f*(l.map (P.shiftOp j)).prod}
lemma monorails {f h:P.Op0 j}(x:f∈P.idleOr j)(p:h∈ P.idleOr j): f*h∈ P.idleOr j:=by
  rcases Set.mem_insert_iff.mp x with e|u; · rwa [e,one_mul]
  rcases Set.mem_insert_iff.mp p with e|v; · rw [e,mul_one]; exact Set.mem_insert_of_mem _ u
  exact Set.mem_insert_of_mem _ (P.tiles_together j u v)
lemma move_idle (w: Grid j) {x:P.Op0 j}(h:x∈P.idleOr j): ∃ y∈P.idleOr j,(Φ w)*x=y*Φ w:=by
  rcases Set.mem_insert_iff.mp h with rfl|t; · exact ⟨1, Set.mem_insert _ _,by simp⟩
  obtain ⟨y,p,v⟩:=P.tile_forward j w t; exact ⟨y,Set.mem_insert_of_mem _ p,v⟩
lemma railroad (l : List (Grid j)) {x:P.Op0 j}(h:x∈P.idleOr j): ∃ y∈P.idleOr j,(W l)*x=y*W l:=by
  induction l with
  | nil=> exact ⟨x,h,by simp⟩
  | cons i l ih=> obtain ⟨y,p,v⟩:=ih; obtain ⟨z,q,t⟩:=P.move_idle j i p; exact ⟨z,q,by simp only [List.map_cons,List.prod_cons,mul_assoc,v,← mul_assoc (Φ i) y,t]⟩

def insertions : Set (P.Op0 j) := P.idleOr j ∪ Set.range (P.shiftOp j)
local notation "Lx"=> P.insertions j
open scoped Pointwise
lemma generates : ∀ x ∈ Lx ∪ star Lx, x ∈ P.normalForm j:=by
  have he{x:P.Op0 j}(h:x∈Lx):star x∈Lx:=by
    rcases h with (rfl|hx)|⟨⟨s,z,d⟩,rfl⟩
    · rw [star_one]; exact Or.inl (Set.mem_insert ..)
    · exact Or.inl (Set.mem_insert_of_mem _ (P.tiles_star_closed j hx))
    rw [P.shift_star]; exact Or.inr ⟨_,rfl⟩
  intro x t; have ht:x∈Lx:=t.elim id (fun u=> (star_star x) ▸ he (Set.mem_star.mp u))
  rcases ht with h|⟨g,rfl⟩
  · exact ⟨x,h,[],by simp⟩
  exact ⟨1, Set.mem_insert ..,[g],by simp⟩
lemma inMonoid {u : P.Op0 j} (h : u∈ Submonoid.closure (Lx ∪ star Lx)): u∈ P.normalForm j:=by
  induction h using Submonoid.closure_induction with
  | mem u h=>exact P.generates j u h
  | one=> exact ⟨1,Set.mem_insert ..,[],by simp⟩
  | mul f g _ _ v w=>
    rcases v with ⟨f,h,p,rfl⟩; rcases w with ⟨g,t,q,rfl⟩; obtain ⟨y,Vy,v⟩:=P.railroad j p t
    exact ⟨f*y,P.monorails j h Vy,p++q,by rw [List.map_append,List.prod_append,mul_assoc,←mul_assoc (W p),v]; simp only [mul_assoc]⟩

/-- This C⋆-algebra lives in the representation actually purchased for the axis. The
    membership/faithfulness compared next will concern *all* labels here. -/
noncomputable def slabAlgebra : StarSubalgebra ℂ (P.Op0 j):= (StarAlgebra.adjoin ℂ (P.insertions j)).topologicalClosure
abbrev Slabs : Type:= ↑(P.slabAlgebra j)
instance wholeClosed : IsClosed (P.slabAlgebra j : Set (P.Op0 j)):=isClosed_closure
lemma moves_admitted(g:Grid j):P.shiftOp j g∈ P.slabAlgebra j:= StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ (Lx) (Or.inr (Set.mem_range_self g)))
lemma blocks_admitted {x:P.Op0 j}(p:x∈P.tiles j): x∈P.slabAlgebra j := StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ Lx (Or.inl (Set.mem_insert_of_mem _ p)))

variable (ρ : P.Register)
include ρ
lemma tiles_sep : TopologicalSpace.IsSeparable (P.tiles j) :=by
  refine IsSeparable.mono (s:=⋃ (s:ℕ)(w:ℕ)(p:0<w), Set.range (P.Box j s w p)) ?_ ?_
  · exact IsSeparable.iUnion (fun s=>IsSeparable.iUnion (fun w=> IsSeparable.iUnion (fun p=> P.boxes_separable j s w p ρ)))
  rintro x ⟨s,w,p,y,rfl⟩; exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨p,Set.mem_range_self _⟩⟩⟩
lemma slabs_separable : TopologicalSpace.SeparableSpace (P.Slabs j) := by
  have h : TopologicalSpace.IsSeparable Lx:= by
    unfold insertions idleOr; rw [Set.insert_eq]; exact ((Set.countable_singleton _).isSeparable.union (P.tiles_sep j ρ)).union (Set.countable_range _).isSeparable
  exact (star_isSeparable_alg (X:=P.Op0 j) h).separableSpace
omit ρ

section comp
open ContinuousLinearMap Set
local notation "R" => P.groundHil j
def compress : P.Op0 j →L[ℂ] P.GroundOp j :=
  (compL ℂ R A R (P.piZero j)).comp ((compL ℂ R A A).flip (P.inHil j))
local notation "σ"=>P.compress j
local notation "K₀" => P.compressionAlgebra j
lemma compress_apply (x : P.Op0 j) : P.compress j x=(P.piZero j).comp (x.comp (P.inHil j)) := rfl
lemma compress_tile {x : P.Op0 j} (e : x∈P.tiles j) : P.compress j x∈ P.compressionAlgebra j := by
  obtain ⟨s,w,p,f,rfl⟩:= e
  rw [P.compress_apply,← P.compresses]; exact (P.preRead j (s,P.entryTest j s f)).property
lemma compress_one : P.compress j 1=1 := by
  ext1 x; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
lemma compress_flight (l : List (Grid j)) (x : P.Op0 j) :
    P.compress j (x*(l.map (P.shiftOp j)).prod)=P.compress j x := by
  ext1 a
  suffices H' : (W l) (P.inHil j a)=P.inHil j a from congrArg (fun y=>P.piZero j (x y)) H'
  induction l with
  | nil=> rfl
  | cons i t h=> change (Φ i) ((W t) (P.inHil j a))= _; rw [h]; exact ((P.ground_ok j a.val).mp a.property).2 i
lemma apartments (x:P.Slabs j) : P.compress j x.val∈ P.compressionAlgebra j:=by
  let W₀:= StarAlgebra.adjoin ℂ Lx
  have h :(W₀:Set (P.Op0 j)) ⊆ σ ⁻¹' (K₀ : Set (P.GroundOp j)):= by
    intro y p; change y ∈ (StarAlgebra.adjoin ℂ Lx).toSubalgebra.toSubmodule at p
    rw [StarAlgebra.adjoin_eq_span] at p
    let R0:=((K₀).toSubalgebra.toSubmodule).comap (σ).toLinearMap
    have hx: Submodule.span ℂ (Submonoid.closure (Lx ∪ star Lx) : Set (P.Op0 j)) ≤ R0:=by
      rw [Submodule.span_le]; rintro f t; obtain ⟨f,v,l,rfl⟩:= (P.inMonoid j t)
      change σ (f* (W l))∈ K₀; rw [compress_flight]; rcases Set.mem_insert_iff.mp v with rfl|v
      · rw [P.compress_one]; exact one_mem _
      exact P.compress_tile j v
    exact hx p
  apply (show x.val∈ σ ⁻¹' (K₀ : Set (P.GroundOp j)) from ?_)
  exact closure_minimal h ((P.closureC j).preimage (σ).continuous) x.property
-- lean bundle: need ContinuousLinearMap to Ensemble. composition & bound; close
lemma shadow_bound (x : P.Op0 j) : ‖P.compress j x‖ ≤ ‖x‖:=by
  apply opNorm_le_bound _ (norm_nonneg _); intro a
  let u:= x (P.inHil j a)
  exact ((P.vacuum j).norm_orthogonalProjectionOnto_apply_le u).trans (x.le_opNorm ..)

def shadow : P.Slabs j →L[ℂ] P.Ensemble j :=
  (LinearMap.codRestrict (f:=(σ).toLinearMap.comp (P.slabAlgebra j).toSubalgebra.toSubmodule.subtype)
    (K₀).toSubalgebra.toSubmodule (fun x=> P.apartments j x)).mkContinuous 1 (fun x=> by rw [one_mul]; exact P.shadow_bound j x.val)
lemma shadow_val (x : P.Slabs j) : (P.shadow j x).val=P.compress j x.val := rfl
lemma shadow_one : P.shadow j 1=1:=Subtype.ext (P.compress_one j)
/-- A TRUE branch of the compression/stamp. Concatenations together with arbitrary
    unitaries for spatial grid directions use one such stamp (or none). -/
def atSide (s w : ℕ)(p : 0<w) (f : P.Card j s w) : P.Slabs j:=⟨P.Box j s w p f,P.blocks_admitted j (P.tile_one j s w p f)⟩
lemma boxes_here (s w : ℕ) (p : 0<w) (f : P.Card j s w) : P.shadow j (P.atSide j s w p f)=P.reading j s (P.entryTest j s f):=Subtype.ext (P.compresses j s w p f|>.symm)
lemma see_shadow (x : P.Slabs j) : inner ℂ (P.groundZero j) ((P.shadow j x).val (P.groundZero j)) = inner ℂ Ω (x.val Ω):=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ..
lemma all_apartments (s : ℕ) (f : P.Test) :
    ∃ b : P.Op0 j, b∈P.tiles j ∧ P.compress j b=P.compressed j s f := by
  let U:=Classical.choice (anyporch Y H s j false (P.obs f)); exact ⟨_,P.tile_one j s U.span U.pos U.fwd, (onAny Y H V s π Qt j false C₀ U).symm⟩

-- Help inference for ground Hil's topological submodule
private theorem enough (H₀ : Hilbert) : PseudoMetrizableSpace (H₀.Op) := inferInstance
include ρ in
lemma component_space_sep : TopologicalSpace.SeparableSpace (P.Ensemble j) := by
  have h : IsSeparable (Set.range (P.labelled j)) := IsSeparable.mono ((P.tiles_sep j ρ).image (P.compress j).continuous) (by
    rintro _ ⟨⟨s,i⟩,rfl⟩; exact P.all_apartments j s i)
  have ht : TopologicalSpace.IsSeparable (K₀ : Set (P.GroundOp j)) := star_isSeparable_alg (X:=(R).Op) h
  letI : PseudoMetrizableSpace (P.GroundOp j) := enough R
  exact ht.separableSpace
end comp
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.shadow
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.boxes_here
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.slabs_separable
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.component_space_sep
