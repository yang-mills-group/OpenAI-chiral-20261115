import MarchC.Shirts
import Preen.Spark
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
variable {Y Z:Doorway}(p:Y.Later Z orderV 0)
include p
lemma uplist {y z:Vantage}(v:y∈Y.invites)(w:z∈Z.invites) : z-y ∈mzone :=by
 have s:=Doorway.covers p (subset_closure v) (subset_closure w); intro i; specialize s i; change 2* (0:Vantage) i < (z-y) i at s; simpa only [Pi.zero_apply,mul_zero] using s
/-- pose selection into all boxes Y.Later Z orderV 0. -/
lemma thicket (k:Vantage→ℂ)(v:slices k)(d:∃p∈mzone,k p≠0) :∃ (a b:Vantage), a∈Y.invites∧b∈Z.invites∧ k (b-a) ≠0 :=by
 obtain ⟨y,g⟩:=Y.doorNonempty; obtain ⟨z,h⟩:=Z.doorNonempty
 obtain ⟨w,a,b,r⟩:= mem_closure_iff_nhds.mp (slice_alive k v d (uplist p g h)) (fun w=> w+y∈ Z.invites) ((show Continuous (fun w:Vantage=>w+y) from continuous_id.add continuous_const).continuousAt.tendsto.eventually (Z.doorOpen.mem_nhds (show (z-y)+y∈Z.invites from by simpa using h)))
 exact ⟨y,w+y,g,a,by rwa [add_sub_cancel_right]⟩
-- auxiliary subrectangle sweep into open region.g
omit p
lemma sub_rect (D:Doorway)(w:Vantage)(p:w∈D.invites){U:Set Vantage}(h:U∈𝓝 w): ∃ K:Doorway,K.invites⊆D.invites∩U ∧ (∀i,D.lower i ≤ K.lower i ∧ K.upper i≤ D.upper i):=by
 obtain ⟨ε,t,u⟩:= Metric.mem_nhds_iff.mp (inter_mem (D.doorOpen.mem_nhds p) h)
 let L: Vantage:=fun i=>max (w i-ε) (D.lower i); let R:Vantage:=fun i=> min (w i+ε) (D.upper i)
 have hl(i:Axis): L i < w i:= max_lt (sub_lt_self _ t) ((p i (Set.mem_univ _)).1)
 have hr(i:Axis): w i < R i:= lt_min (lt_add_of_pos_right _ t) (p i (Set.mem_univ _)).2
 let K:Doorway:=⟨L,R,fun i=> (hl i).trans (hr i)⟩
 refine ⟨K,fun x v=>u ((Metric.mem_ball.mpr (dist_pi_lt_iff t|>.mpr (fun i=>?_)))), fun i=> ⟨le_max_right .., min_le_right ..⟩⟩
 rw [Real.dist_eq,abs_lt]; have hx:=v i (Set.mem_univ i); constructor
 · linarith only [le_max_left (w i-ε) (D.lower i), show L i<x i from hx.1]
 · linarith only [min_le_left (w i+ε) (D.upper i),show x i<R i from hx.2]
lemma sub_later (Y' Z':Doorway)(h:∀ i, Y'.upper i ≤ Y.upper i)(t:∀ i,Z.lower i ≤Z'.lower i)(p:Y.Later Z orderV 0): Y'.Later Z' orderV 0:=by intro i; have hp:=p i; change _+(2:ℝ)*0 < _; change Y.upper i+2*0 < Z.lower i at hp; linarith [h i,t i]
-- purchase threshold region for Rank1.E
open _root_.YM.Preen DoseTravel
lemma heat_margin{X:Hilbert}(z:X)(g:Vantage→X)(p:Continuous g)(a b:Vantage)(h:inner ℂ (paster z (g (poseMirror 3 a))) (paster z (g b)) ≠0): ∃ U∈𝓝 a,∃ V∈𝓝 b, ∀ F H:SampleDose,F.Normalized→H.Normalized→tsupport F.val⊆U→tsupport H.val⊆ V→inner ℂ (paster z (beam X (flipDose F 3) g)) (paster z (beam X H g))≠0:=by
 let Z'(q:X.space×X.space):ℂ:=inner ℂ (paster z q.1) (paster z q.2); let d:= poseMirror 3
 let q:X.space×X.space:=(g (d a),g b)
 have hZ:Continuous Z':= ((paster z).continuous.comp continuous_fst).inner ((paster z).continuous.comp continuous_snd)
 obtain ⟨δ,f,e⟩:= Metric.mem_nhds_iff.mp ((hZ.tendsto q).eventually (show {y:ℂ|y ≠ 0}∈𝓝 _ from isOpen_ne.mem_nhds h))
 let E:=δ/2; have hp:0<E:=half_pos f
 let v(y:X):=Metric.ball y E
 let U:=(fun z:Vantage=>g (d z)) ⁻¹' v q.1; let V:=g ⁻¹' v q.2
 refine ⟨U,(p.comp d.continuous).continuousAt.tendsto.eventually (Metric.ball_mem_nhds _ hp), V,p.continuousAt.tendsto.eventually (Metric.ball_mem_nhds _ hp),fun F H fA hA fB hB=>?_⟩
 have hx(B:SampleDose)(t:Vantage)(h:B.Normalized)(u:tsupport B.val⊆g ⁻¹' v (g t)):dist (beam X B g) (g t) < δ:=(dist_eq_norm ..|>.trans_le (tol t X g p B h _ (fun y h=>by rw [←dist_eq_norm]; exact (u h).le ))).trans_lt (half_lt_self f)
 refine e (show (beam X (flipDose F 3) g,beam X H g)∈ Metric.ball q δ from ?_)
 rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
 refine ⟨hx _ (d a) (flipPay F fA 3) ?_,hx _ b hA hB⟩
 intro y h; rw [flipBudget] at h; have he:=fB h
 change dist (g (d (d y))) _ < E at he; rw [show d (d y)=y from reflectPose_twice 3 y] at he
 exact he
#print axioms thicket
#print axioms heat_margin
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
