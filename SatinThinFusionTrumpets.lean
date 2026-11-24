import SatinFixedContrastNovember4
import SatinThinFusionSales
/-! # Print the prismatic order G+M sensor stencils. Exact and no growth of finite difference ORDER permitted.

Keep Lean terms on evaluation stamp s; support *stencil* records true frame at s
then include width realWidth. Extra tick for testing continuum obstruction:
ALL owned powers will actually be stepped FORWARD one more tick while staying
in a true shrinking stencil. Credit: pay earlier from the unstepped ones.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets
variable (P:Spine) (W:Bool)
local notation "K" => P.calibration
local notation "T" => timeMesh P.par
local notation "b"=> ruler P.par.block
-- slightly more precise internal support budget than translations of the initial stencil applied in any order
-- (only positive shifts by 1); temporal cost in thickness units (s grid) exact n+1.
noncomputable def tubaField (s:ℕ)(F:P.Test) : ℕ→ P.Test
 | 0=> F
 | n+1=> (duration (whenly T s 1))⁻¹ • (P.shifts 3 1 (tubaField s F n)- tubaField s F n)
def tubaStencil (S:Finset Cover): ℕ→ Finset Cover
 | 0=> S
 | n+1=> tubaStencil S n ∪ plow K 3 1 (tubaStencil S n)
lemma tubaShelter (j:Axis){q:ℕ}{S:Finset Cover}(e:Between K j (-b*q) (b*q) S)(n:ℕ): Between K j (-b*((q+n:ℕ):ℤ)) (b*((q+n:ℕ):ℤ)) (P.tubaStencil S n):=by
 induction n with
 | zero=> exact e
 | succ i h=>
   intro k t; rcases mem_union.mp t with t|t
   · exact P.stretch_between j (by omega) h k t
   rw [← Nat.add_assoc]; exact P.transport_shelter j 3 _ 1 h k t -- local target conjunction rewrite twice
lemma tubaStencil_steps {S:Finset Cover}{n m:ℕ}(h:n ≤ m): P.tubaStencil S n ⊆ P.tubaStencil S m:=
 (monotone_nat_of_le_succ (show ∀ i:ℕ, P.tubaStencil S i ⊆ P.tubaStencil S (i+1) from fun i=> by
   rw [tubaStencil]; exact subset_union_left)) h
variable (s:ℕ)
local notation "Δ"=> whenly T s 1
lemma tuba_bay (F:P.Test)(w:ℕ)(S:Finset Cover)(p:F∈bay K S true): P.tubaField s F w∈ bay K (P.tubaStencil S w) true:=by
 induction w with
 | zero=> exact p
 | succ i h=> rw [tubaField,tubaStencil]; apply Subalgebra.smul_mem; exact Subalgebra.sub_mem _ ((tallerBay _ _ _ subset_union_right) (P.shifts_support _ _ _ h)) ((tallerBay _ _ _ subset_union_left) h)
lemma tuba_real (F:P.Test)(w:ℕ)(p:F∈enclave K): P.tubaField s F w ∈ enclave K:=by
 induction w with
 | zero=> exact p
 | succ i h=> rw [tubaField]; exact Subalgebra.smul_mem _ ((enclave K).sub_mem (P.shifts_keep 3 1 h) h) _
lemma tuba_senses (F:P.Test)(w:ℕ)(S:Finset Cover)(p:F∈P.sensing S s W): P.tubaField s F w∈ P.sensing (P.tubaStencil S w) s W:=by
 induction w with
 | zero=> exact p
 | succ i h=> rw [tubaField,tubaStencil]; apply Submodule.smul_mem; exact Submodule.sub_mem _ (P.sensing_mono s W subset_union_right (P.shift_senses s W 3 1 h)) (P.sensing_mono s W subset_union_left h)
variable (D:Prism)
def lastTuba (D:Prism):ℕ:= D.support.sup (fun i=>i+1)
variable (A:P.Apron)
local notation "U"=> P.tubaStencil A.S (lastTuba D)
local notation "L"=> plow K 3 1 U
noncomputable def drumroll (F:P.Test)(p:Prism):= ∑ i∈p.support, p i • P.tubaField s F (i+1)
noncomputable def aTuba:P.Apron:=
 { s:=A.s
   F:= P.shifts 3 1 (P.drumroll A.s A.F D)
   S:= L
   u:=fun i=> A.u i + lastTuba D + 1
   pos:=fun i=>by omega
   realM:=P.shifts_keep 3 1 (Subalgebra.sum_mem _ fun i t=> Subalgebra.smul_mem _ (P.tuba_real A.s A.F _ A.realM) _)
   shelter:=fun j=> P.transport_shelter j 3 _ 1 (P.tubaShelter j (A.shelter j) (lastTuba D))
   bay:=by
     refine P.shifts_support 3 1 _ (Subalgebra.sum_mem _ ?_); intro i h; apply Subalgebra.smul_mem
     exact (tallerBay K _ true (P.tubaStencil_steps (le_sup (f:=fun i=>i+1) h))) (P.tuba_bay A.s A.F (i+1) _ A.bay) }
local notation "u"=> P.aTuba D A
lemma tuba_width (j:Axis) : (u).realWidth P j=A.realWidth P j + (lastTuba D + 1:ℕ)* P.macroStep A.s:=by
 unfold Apron.realWidth bell; simp only [aTuba]; push_cast; unfold macroStep; ring_nf; try rfl
lemma plays_sensor(p:P.Sensor A W): P.Sensor (u) W:= by
 refine P.shift_senses A.s W 3 1 (Submodule.sum_mem _ ?_); intro i h; apply Submodule.smul_mem
 exact P.sensing_mono A.s W (P.tubaStencil_steps (le_sup (f:=fun i=>i+1) h)) (P.tuba_senses W _ _ (i+1) A.S p)
variable (x:P.Spectrum0 3)
lemma tuba_zero(F:P.Test)(n:ℕ): P.singleState 3 s x (P.tubaField s F (n+1))=0:=by
 rw [tubaField,map_smul,map_sub,P.slide_single,sub_self,smul_zero]
lemma drum_zero(F:P.Test) : P.singleState 3 s x (P.drumroll s F D)=0:=by
 unfold drumroll; rw [map_sum]; exact sum_eq_zero fun i _=> by rw [map_smul,P.tuba_zero,smul_zero]
lemma trumpets_center : P.singleState 3 A.s x (u).F=0:=by change P.singleState 3 A.s x (P.shifts 3 1 _)=_; rw [P.slide_single,P.drum_zero]
lemma drum_birth_sub {F G:P.Test}(f:P.birthF 3 s F)(g:P.birthF 3 s G):P.birthF 3 s (F-G):=by
 have ht:= P.birthScaleJ 3 s (-1) g; rw [neg_one_smul] at ht; rw [sub_eq_add_neg]; exact P.birthAddJ 3 s f ht
local notation "H"=> P.ColorHil 3 x
local notation "E"=> P.physicalEnergy 3 x
lemma diff_birth {F:P.Test}(f:P.birthF 3 s F)(n:ℕ): P.birthF 3 s (P.tubaField s F n):=by
 induction n with
 | zero=> exact f
 | succ n h=> rw [tubaField]; exact P.birthScaleJ 3 s _ (P.drum_birth_sub s (P.passesLater 3 s 1 h) h)
lemma diff_view {F:P.Test}(f:P.birthF 3 s F)(n:ℕ): P.viewF 3 x s (P.diff_birth s f n)= ((mesh_diff (E) Δ)^n) (P.viewF 3 x s f):=by
 induction n with
 | zero=>rw [pow_zero]; rfl
 | succ n h=>
   let g:= P.diff_birth s f n
   let k:= P.passesLater 3 s 1 g
   let ht:= P.drum_birth_sub s k g
   rw [pow_succ']; refine (P.viewJ_scale 3 x s (duration Δ)⁻¹ ht).trans ?_
   change (duration Δ)⁻¹ • P.viewF 3 x s ht = mesh_diff (E) (Δ) _
   rw [mesh_step, P.sixWard_view_sub 3 x s k g, P.releasedLater]; change _⁻¹ • ((E).E _ (P.viewF 3 x s (P.diff_birth s f n))-P.viewF 3 x s (P.diff_birth s f n))=_; rw [h]; rfl
lemma drum_parts {F:P.Test}(f:P.birthF 3 s F):∃ h:P.birthF 3 s (P.drumroll s F D), P.viewF 3 x s h=prism_on (E) D Δ (P.viewF 3 x s f):=by
 unfold prism_on; rw [ContinuousLinearMap.sum_apply]
 refine P.birthSumJ 3 x s _ _ _ (fun i t=>?_)
 exact ⟨_, (P.viewJ_scale 3 x s (D i) (P.diff_birth s f (i+1))).trans (congrArg (D i • ·) (P.diff_view s x f (i+1)))⟩
lemma launchedPiece {F:P.Test}(f:P.birthF 3 s F) : P.birthF 3 s (P.drumroll s F D):= by
 -- x needed?
 exact (P.drum_parts s D (Classical.arbitrary (P.Spectrum0 3)) f).choose -- Spectrum instance?
lemma plays_birth (a:P.birthF 3 A.s A.F): P.birthF 3 (u).s (u).F:= P.passesLater 3 A.s 1 (P.launchedPiece A.s D a)
lemma trumpet_cost (a:P.birthF 3 A.s A.F): P.viewF 3 x A.s (P.plays_birth D A a)=(E).E (whenly T A.s 1) (prism_on (E) D (whenly T A.s 1) (P.viewF 3 x A.s a)):=by
 let f:= (P.drum_parts A.s D x a).choose
 exact (P.releasedLater 3 x A.s 1 f).trans (congrArg ((E).E _) (P.drum_parts A.s D x a).choose_spec)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.trumpet_cost
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.plays_sensor
