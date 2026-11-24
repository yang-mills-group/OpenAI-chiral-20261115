import Quarry.Mask
import YM.SU5.Interaction.Source.Flux
import YM.CF.Buffered.Probes

/-!
 # Actual stencils of the experiment (128)

Raw and scaled. Use Swell's block variant (windmill, convolution;
see (126) theorem `inwardE` at full unmasked operands). `m` is in matter units.
Proofs of Mark grammar and support. Estimates post-regulator will need the signed
price, not inference from this grammar.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet
open Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Buffered
open StressExchange (preJ)

variable {N : Side} (p : BudgetPoint) (K : Scree.Loom N) (o : Site N)
local notation "Ω" => Single N

def topChip (X : SOp N) : Pane N → ℂ :=
  Matrix.trace ∘ hatKernel p K (offsetMask p.B o) X

def topMark (X : SOp N) : Buffered.Mark N :=
  fun v => topChip p K o X v.1 • 1

/-- Current stencil at x, with kernels arrived from the prescription at o.
Translation in the Mark formula uses the SAME pre-mask kernel. -/
def bondMark (X : SOp N) (x : Site N) : Buffered.Mark N :=
  fun v => preJ (tickA N) (hatKernel p K (offsetMask p.B x) (co_Ψ x o X) v.1)

/-- (128) before scoping out scale. All links of first Pane. -/
def wardMark (m : ℕ) (J : Axis → SOp N) (X : SOp N) : Buffered.Mark N :=
  topMark p K o X + ∑ i:Axis, (bondMark p K o (J i) (o+gapPlus i m) -
                                 bondMark p K o (J i) (o-gapPlus i m))

/- Actual scaling from the construction notes, (128)-(129) (and (130)),
   using budget point threshold. In the theorem on the course, instantiate Q and show
   p.threshold from the level. -/
def mark128 (Q : ℝ) (m : ℕ) (J : Axis → SOp N) (X : SOp N) : Buffered.Mark N :=
  ((Q / p.threshold ^ 2 : ℝ) : ℂ) • wardMark p K o m J X

/-- Support advertised for estimate: also mask inspection and W sites.
 Use at growing p.B (≫ m). Keep margin e.g. core l = 24 in Nest. -/
def port (p : BudgetPoint) (o : Site N) : Sa N := halo (6*p.B) {node o}

variable {a b d t : ℝ} {m k q : ℕ} {X : SOp N}
variable (P : Trunk (node o) X k a b d) (L : Roof N t d q K)
    (hp : p.threshold ≤ t) (hd : 0 < d) (size : k + q ≤ p.B) (ha : 0 ≤ a)
local notation "σ" x:max => offsetMask p.B x

/-- grammar (and invariance) on this height. -/
structure RealStencil {n : Side} (f : Buffered.Mark n) (S : Sa n) : Prop where
  firstPane : ∀ x y:Buffered.Fields n, x.1=y.1 → f x=f y
  foot : AtSupport false S f
  moves : covariant f

namespace RealStencil
variable {S S' : Sa N} {f g : Buffered.Mark N}
theorem promote (u : RealStencil f S) (h : S ⊆ S') : RealStencil f S' :=
  ⟨u.firstPane, u.foot.mono h, u.moves⟩
theorem plus (u : RealStencil f S) (v : RealStencil g S) : RealStencil (f+g) S :=
  ⟨fun x y p => by rw [Pi.add_apply, Pi.add_apply, u.firstPane _ _ p, v.firstPane _ _ p],
    u.foot.addM v.foot, fun i x => by rw [Pi.add_apply, Pi.add_apply, u.moves, v.moves, map_add]⟩
theorem scale (u : RealStencil f S) (z : ℂ) : RealStencil (z • f) S :=
  ⟨fun x y p => by rw [Pi.smul_apply, Pi.smul_apply, u.firstPane _ _ p],
    u.foot.smulM z, fun i x => by rw [Pi.smul_apply, Pi.smul_apply, u.moves, twist_scalar]⟩
theorem void : RealStencil (0:Buffered.Mark N) S :=
  ⟨fun _ _ _ => rfl, AtSupport.zeroM, fun _ _ => (map_zero _).symm⟩
theorem minus (u : RealStencil f S) (v : RealStencil g S) : RealStencil (f-g) S := by
  rw [sub_eq_add_neg]; exact u.plus (neg_one_smul ℂ g ▸ (v.scale (-1)))
theorem sumStencil {ι : Type*}(Y : Finset ι)(f : ι → Buffered.Mark N)(u : ∀ i∈Y, RealStencil (f i) S) :
    RealStencil (∑ i∈Y, f i) S := by
  induction Y using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact void
  | insert i Y t h => rw [sum_insert t]; exact (u i (mem_insert_self ..)).plus (h (fun _ p => u _ (mem_insert_of_mem p)))
end RealStencil

include P L hp hd size ha in
theorem topStencil : RealStencil (topMark p K o X) (inspected (σ o)) := by
  have h : halo (k+q) {node o} ⊆ σ o := Corona.halo_mono size le_rfl
  let Z := hatKernel p K (σ o) X
  have ht : Continuous (fun U:Op Ω => U.trace • (1:FC Ω)) := by
    have hv : Continuous (fun U:Op Ω => Matrix.trace U) := continuous_finsetSum _ (fun i _ => continuous_id.matrix_elem i i)
    exact hv.smul (continuous_const (y:=(1:FC Ω)))
  refine ⟨fun x y t => by simp only [topMark,t], .fromEval _
    (Girt.pole_w Z _ ht (hatKernel_borel P L hd ha))
      (fun i j v => ?_) (fun i => Reed.Fine.one.scale _), fun g i => ?_⟩
  · exact congrArg (fun U:Op Ω => Matrix.trace U • (1:FC Ω)) (hatKernel_reads P L hp hd h i j v)
  change Matrix.trace (hatKernel _ _ _ _ (Lattice.gauge g i.1)) • _=twist _ (Matrix.trace (Z i.1) • 1)
  rw [hatKernel_gauge P L hp hd h i.1 g, trace_twist, twist_scalar, map_one]

include P in
theorem markArrival (x : Site N) : Trunk (node x) (co_Ψ x o X) k a (Tenant.quota^2*b) d := by
  have h := P.pose (taxiPlus (x-o))
  rw [platforms, add_sub_cancel] at h
  exact h

include P L hp hd size ha in
theorem bondStencil (x : Site N) : RealStencil (bondMark p K o X x) (inspected (σ x)) := by
  let τ := σ x
  let I := inspected τ
  let F := co_Ψ x o X
  have h' := markArrival o P x
  let Z := hatKernel p K τ F
  have h : halo (k+q) {node x} ⊆ τ := Corona.halo_mono size le_rfl
  have hv : halo k {node x} ⊆ I := ((Corona.halo_mono (show k ≤ p.B from by omega) le_rfl : halo k {node x} ⊆ τ)).trans (within_inspect _)
  let A := tickA N
  have hk : Continuous (preJ A) := by
    unfold StressExchange.preJ
    have ht : Continuous (fun U:Op Ω => Matrix.trace (A*U)) := continuous_finsetSum _ fun i _ => ((continuous_const (y:=A)).mul continuous_id).matrix_elem i i
    refine Continuous.add (ht.smul (continuous_const (y:=(1:FC Ω)))) ((Girt.dgCT _).comp ?_)
    exact (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨fun u v t => by simp only [bondMark,t], .fromEval (fun v => preJ A (Z v))
      (Girt.pole_w _ _ hk (hatKernel_borel h' L hd ha)) (fun i j v => ?_)
      (fun i => ?_), fun g i => ?_⟩
  · exact congrArg (preJ A) (hatKernel_reads h' L hp hd h i j v)
  · have hi : ClippedAt I (Z i) := hatKernel_clips h' L hp hd h i hv
    change Reed.Fine _ _ _ (preJ (tickA N) (Z i))
    rw [touchP]; exact StressExchange.inSector _ _ _ hi
  have he : Z (Lattice.gauge g i.1) = twist (tradew N g) (Z i.1) := hatKernel_gauge h' L hp hd h i.1 g
  have ht : twist (tradew N g) A=A := Cascade.tick_g _
  change preJ A (Z _) = twist _ (preJ A (Z i.1)); change preJ A (Z (Lattice.gauge g i.1)) = _
  rw [he]; unfold StressExchange.preJ
  rw [map_add, twist_scalar, map_one, dg_cov, map_mul, map_mul, map_sub, map_one, ht,
      show A* twist (tradew N g) _ = _ from (by rw [map_mul,ht] : A* twist (tradew N g) (Z i.1) = twist (tradew N g) (A*Z i.1)), trace_twist]

theorem portClear (high : 6 ≤ p.B) (width : m ≤ p.B) (x : Site N) (g : separation o x ≤ m) :
    inspected (σ x) ⊆ port p o := by
  let h : σ x ⊆ halo (4*p.B) {node o} := offsetFit o x g (by omega)
  exact (Yaw.touchK _).trans ((Corona.halo_mono le_rfl h).trans (by
    intro i v; obtain ⟨j,w,k⟩ := halo_spec.mp v; obtain ⟨u,b,q⟩ := halo_spec.mp w
    exact halo_spec.mpr ⟨u,b,(separation_triangle u j i).trans (by omega)⟩))

include P L hp hd size ha
variable {J : Axis → SOp N} (TA : ∀ i, Trunk (node o) (J i) k a b d)
variable (high : 6 ≤ p.B) (width : m ≤ p.B)
include TA high width
lemma wardStencil : RealStencil (wardMark p K o m J X) (port p o) := by
  have V := fun x : Site N => portClear p o high width x
  refine ((topStencil p K o P L hp hd size ha).promote (V o (by rw [separation_self]; omega))).plus
    (RealStencil.sumStencil _ _ (fun i _ => ?_))
  exact ((bondStencil p K o (TA i) L hp hd size ha _).promote (V _ (stopBeam o i m).1)).minus
    ((bondStencil p K o (TA i) L hp hd size ha _).promote (V _ (stopBeam o i m).2))

lemma stencil128 (Q : ℝ) : RealStencil (mark128 p K o Q m J X) (port p o) :=
  (wardStencil p K o P L hp hd size ha TA high width).scale _
end YM.CF.Swell
