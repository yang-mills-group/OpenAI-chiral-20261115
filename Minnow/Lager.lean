import MarchC.Pardon
import AuroraB.Vita
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
variable(P:Spine)
open Ballad Cordial
open Lamour.Bridge.Celeste Designs Twah Six Ballad Cordial
open _root_.YM.Preen DoseTravel Habitat.Hemlock.AuroraB
private lemma h_block (X:Hilbert)(f:Lead.Clan→Vantage→X)(h:∀i,Continuous (f i))(δ:ℝ)(d:0<δ) (D:SampleDose)(v:Vantage)(w:D.Normalized)(U:tsupport D.val ⊆ (fun (y:Vantage) (i:Lead.Clan)=> f i y) ⁻¹' (Metric.ball (fun i=> f i v) (δ/2))):dist (fun i=>DoseTravel.beam X D (f i)) (fun i=> f i v)<δ:=by
 let Y(z:Vantage):Lead.Clan→X.space:=fun i=>f i z
 rw [dist_pi_lt_iff d]; intro i; rw [dist_eq_norm]; refine (DoseTravel.tol v X _ (h i) D w _ (fun a y=>?_)).trans_lt (half_lt_self d)
 rw [←dist_eq_norm]; exact (dist_le_pi_dist (Y a) (Y v) i).trans ((U y).le)
private lemma ball_w (X:Hilbert)(k:X)(f g:Films X)(t:ReadsSix (proto X k (f,g))):∃δ:ℝ,0<δ∧∀a b:Films X,dist a f<δ → dist b g <δ → ReadsSix (proto X k (a,b)):=by
 obtain ⟨δ,d,e⟩:= Metric.mem_nhds_iff.mp (((firing X k).continuousAt (x:=(f,g))).tendsto.eventually (show {s:CrossRead|ReadsSix s}∈𝓝 _ from readsSix_open.mem_nhds t))
 exact ⟨δ,d,fun _ _ h q=> e (Metric.mem_ball.mpr (show _<δ from (Prod.dist_eq ..).trans_lt (max_lt h q)))⟩
private lemma h_ready (X:Hilbert)(f:Lead.Clan→Vantage→X)(h:∀i,Continuous (f i))(p:Vantage)(δ:ℝ)(d:0<δ):∃U∈𝓝 p,∀ A:SampleDose,A.Normalized→tsupport A.val⊆ U → dist (fun i=>DoseTravel.beam X A (f i)) (fun i=>f i p)<δ:=
 let Y(z:Vantage):Lead.Clan→X.space:=fun i=>f i z
 have hc:Continuous Y:=continuous_pi h
 ⟨Y ⁻¹' (Metric.ball (Y p) (δ/2)), hc.continuousAt.tendsto.eventually (Metric.ball_mem_nhds _ (half_pos d)), fun A u v=> h_block X f h δ d A p u v⟩
/- smearing stable every pair layout -/
set_option maxHeartbeats 1060000 in
lemma ortho_near (X:Hilbert)(k:X)(f:Lead.Clan→Vantage→X)(h:∀i,Continuous (f i))(p q:Vantage)
 (t: ReadsSix (proto X k (fun i=> f i (poseMirror 3 p),fun i=>f i q))):∃ U∈𝓝 p,∃ V∈𝓝 q,∀ A B:SampleDose,A.Normalized→B.Normalized→tsupport A.val⊆U→tsupport B.val ⊆V→ReadsSix (zoneH X k f A B):=by
 let m:=poseMirror 3; obtain ⟨δ,d,e⟩:=ball_w X k _ _ t
 obtain ⟨U,w,z⟩:=h_ready X f h (m p) δ d; obtain ⟨V,y,g⟩:=h_ready X f h q δ d
 refine ⟨m ⁻¹' U,m.continuous.continuousAt.tendsto.eventually w,V,y,fun A B u v a b=>e _ _ (z _ (flipPay A u 3) ?_) (g B v b)⟩
 intro k h; rw [flipBudget] at h; have he:=a (show m k∈tsupport A.val from h); change m (m k) ∈ U at he; rwa [show m (m k)=k from reflectPose_twice ..] at he
#print axioms ortho_near
lemma leveled{A B:Doorway}(U:ℝ)(t:0<U)(h:A.upper 3 ≤ -U)(p:B.lower 3 ≥ U)(Z Y:SampleDose)(hZ:tsupport Z.val⊆A.invites)(hY:tsupport Y.val⊆ B.invites): (∀ y∈ tsupport (flipDose Z 3).val, U< y 3) ∧ ∀y∈ tsupport Y.val,U<y 3:=by
 constructor
 · intro y hp; have hz:poseMirror 3 y ∈ A.invites:=hZ (by rw [flipBudget] at hp; exact hp) -- ▸ orientation
   change (opposeR 3 y)∈ A.invites at hz; have he: -y 3 = opposeR 3 y 3:=by unfold opposeR mirrorΩ; simp
   have hv:=hz 3 (Set.mem_univ _)|>.2; rw [←he] at hv; linarith only [hv,h]
 intro y hy; exact p.trans_lt ((hY hy 3 (Set.mem_univ _)).1)
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
