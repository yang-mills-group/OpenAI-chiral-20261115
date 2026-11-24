import Minnow.Younger
import Minnow.Panini
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
open _root_.YM.Preen Cheer DoseTravel Prototype Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn Habitat.Hemlock
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(fu:P.Fever F C D x)(H:Rovers P F C D x)
open Ballad Cordial Six Lamour.Bridge.Celeste Designs Twah
open AuroraB
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 ξ
local notation "σ"=> P.heaven 3 ξ
local notation "θ"=>flipDose
local notation "pZ"=>poseMirror 3
noncomputable def thyme(d:ℝ)(A E:SampleDose):Matrix Lead.Clan Lead.Clan ℂ:= Matrix.of fun i j=>inner ℂ (prettyR (P:=P) x F C D (flipDose A 3) d i) (prettyR x F C D E d j)
private abbrev since(d:ℝ)(A:SampleDose):Prop:=∀ y∈tsupport A.val,1+d<y 3
private lemma seq_norm (V:Doorway)(qu:V.upper 3≤-1)(i:Vantage)(p:i∈V.invites):1< -i 3:=by linarith only [show i 3 < V.upper 3 from (p _ (Set.mem_univ _)).2,qu]
include J fu H
lemma catalog {A B:Doorway}(v:A.Later B orderV 0)(qu:A.upper 3 ≤ -1)(qt:1≤ B.lower 3):∃ d:ℝ,0<d∧∃(Y Z:Doorway),Y.Later Z orderV 0 ∧Y.invites⊆A.invites∧Z.invites⊆B.invites∧∀ U G:SampleDose,U.Normalized→G.Normalized→tsupport U.val⊆Y.invites→tsupport G.val⊆Z.invites→ since d (θ U 3) ∧ since d G ∧ ReadsSix (thyme P x F C D d U G):=by
 obtain ⟨a,b,ha,hb,hk⟩:= zone_points P x J F C D H fu v
 let u:=min (-a 3) (b 3); have hu:(1:ℝ)<u:=lt_min (seq_norm A qu a ha) (qt.trans_lt (hb 3 (Set.mem_univ _)).1)
 let d:=(u-1)/2; have hd:0<d:=half_pos (sub_pos.mpr hu)
 obtain ⟨j,h,t⟩:=(((recessVanish P F).eventually (gt_mem_nhds zero_lt_one)).and (eventually_ge_atTop F)).exists
 have he:b-a∈mzone:=uplist v ha hb
 obtain ⟨r,p,z⟩:=fu j t
 have ht:1+d< -a 3:= by unfold d; linarith only [hu,(show u ≤ -a 3 from min_le_left ..)]
 have hp:1+d<b 3:=by unfold d; linarith only [hu,(show u ≤ b 3 from min_le_right ..)]
 let l:=lister x F d j r; let K:= proto (W) (σ) ((fun i=> l i (pZ a)),fun i=>l i b)
 have hC:K= daly P x F C D (b-a):=by
    ext1 i k
    let Ab (T:(W))(Q:W):=inner ℂ (paster (σ) T) (paster (σ) Q)
    have hg:(pZ a) 3= -a 3:=clock_neg ..
    exact (congrArg₂ Ab (lister_at x F d j r i (pZ a) hd (by rw [hg]; linarith)) (lister_at x F d j r k b hd (by linarith))).trans (funding P x J F C D H j r p a b (by linarith) (by linarith) he t i k)
 have hK:ReadsSix K:= (congrArg ReadsSix hC.symm).mp hk
 obtain ⟨U,hU,D',hD,W'⟩:= ortho_near (W) (σ) l (fun i=>listerC ..) a b hK
 let ea:={k:Vantage|1+d< -k 3}; let eb:={k:Vantage|1+d<k 3}
 obtain ⟨Y,vA,wA⟩:= sub_rect A a ha (inter_mem hU (show ea∈𝓝 a from (show Continuous (fun k:Vantage=> -(k 3)) from (continuous_apply _).neg).continuousAt.tendsto.eventually (lt_mem_nhds ht)))
 obtain ⟨Z,vB,wB⟩:= sub_rect B b hb (inter_mem hD (show eb∈𝓝 b from (continuous_apply 3).continuousAt.tendsto.eventually (lt_mem_nhds hp)))
 refine ⟨d,hd,Y,Z,sub_later Y Z (fun i=>(wA i).2) (fun i=>(wB i).1) v,vA.trans Set.inter_subset_left,vB.trans Set.inter_subset_left,fun E Tz pE pT y z=>?_⟩
 let v' := W' E Tz pE pT (y.trans (vA.trans (Set.inter_subset_right.trans Set.inter_subset_left))) (z.trans (vB.trans (Set.inter_subset_right.trans Set.inter_subset_left)))
 have A₀:since d (θ E 3):=by intro t e; rw [flipBudget] at e; have he:= (vA (y (show pZ t∈tsupport E.val from e))).2.2; change _ < - ((pZ t) 3) at he; rwa [clock_neg, neg_neg] at he
 have B₀:since d Tz:=fun t e=> (vB (z e)).2.2
 refine ⟨A₀,B₀,(congrArg ReadsSix ?_).mp v'⟩ -- orientation from zone to thyme
 have hQ(X:SampleDose)(t:since d X)(i:Lead.Clan): paster (σ) (DoseTravel.beam (W) X (l i))=prettyR x F C D X d i:=by
    let v:=drawn x F C D X d j r hd p (fun z k=> (show d+tidal P F j < z 3 by linarith only [h, t z k]) -- add_lt syntax orientation results R+d<1+d, need d+R?
      ) i -- args order
    exact (congrArg (paster (σ)) v.symm).trans (show paster (σ) (prettyR (P:=P) x F C D X d i)=prettyR (P:=P) x F C D X d i from Habitat.Hemlock.AuroraB.wall_z (P.seasons 3 ξ) (σ) (P.stone_norm ..) (P.heaven_hot 3 ξ) (score i) _ _ hd (scoring i).1)
 ext1 i k; exact congrArg₂ (inner ℂ) (hQ _ A₀ i) (hQ _ B₀ k)
#print axioms catalog
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
