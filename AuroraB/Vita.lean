import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
open PledgeT MiterT DoseTravel _root_.YM.Preen
-- import Preen.Spark implicit via Channel. reprove doors
private lemma doors_f {t θ:ℝ}(ht:θ<t)(bt:1<t)(ε:ℝ)(h:0<ε):∃ (A B:Doorway),A.Later B (⟨fun _=>true,rfl⟩:Orders) 0 ∧
 (∀ y:Vantage,poseMirror 3 y∈A.invites → dist y (MiterT.forest t) ≤ ε ∧ max θ (1:ℝ)< y 3) ∧ (∀ y:Vantage,y∈ B.invites → dist y (MiterT.forest t)≤ ε ∧ max θ (1:ℝ)< y 3):= by
 let q:= min (t-max θ 1) ε / 4
 have he : max θ (1:ℝ)<t := max_lt ht bt
 have hh: 0< q:= div_pos (lt_min (sub_pos.mpr he) h) (by norm_num)
 have hθ: 4*q ≤ t-max θ 1 :=by unfold q; linarith only [min_le_left (t-max θ 1) ε ]
 have hε: 4*q ≤ε:=by unfold q; linarith only [min_le_right (t-max θ 1) ε]
 have hf{a b c d:ℝ} (p:a<b)(q:c<d)(i:Axis) : MiterT.appoint a c i < MiterT.appoint b d i:=by by_cases t:i=3 <;> simp [MiterT.appoint,t,p,q]
 let X:Doorway:= ⟨MiterT.appoint (-(t+q)) (-q), MiterT.appoint (-(t-q)) (-q/2),hf (by linarith) (by linarith)⟩
 let Y:Doorway:= ⟨MiterT.appoint (t-q) (q/2),MiterT.appoint (t+q) q,hf (by linarith) (by linarith)⟩
 have hc:t-q>max θ 1:=by linarith only [hθ,hh]
 have hz:0<t-q:=lt_trans zero_lt_one ((le_max_right θ 1).trans_lt hc)
 refine ⟨X,Y,fun i=>?_,fun y p=>?_,fun y p=>?_⟩
 · change X.upper i+2*0 <Y.lower i
   rw [mul_zero,add_zero]; exact hf (by linarith) (by linarith) i
 · have B(i):dist (y i) (MiterT.forest t i)< ε ∧ (i=3 → max θ 1< y i):=by
     have f:=p i (Set.mem_univ _)
     by_cases u:i=(3:Axis)
     · change X.lower i < opposeR 3 y i ∧ opposeR 3 y i < X.upper i at f
       simp only [X,MiterT.appoint,opposeR,mirrorΩ,u,if_pos,Real.dist_eq,abs_lt,MiterT.forest,true_imp_iff] at f ⊢
       -- inspect
       exact ⟨⟨by linarith only [f.2,hε,hh],by linarith only [f.1,hε,hh]⟩,by linarith only [f.2,hc]⟩
     change X.lower i < opposeR 3 y i ∧ opposeR 3 y i < X.upper i at f
     simp [X,MiterT.appoint,opposeR,mirrorΩ,Real.dist_eq,u,MiterT.forest,eq_comm,abs_lt] at f ⊢
     constructor <;> linarith only [f.1,f.2,hh,hε]
   exact ⟨((dist_pi_lt_iff h).2 (fun i=> (B i).1)).le,(B (3:Axis)).2 rfl⟩
 have B(i):dist (y i) (MiterT.forest t i)< ε ∧ (i=3 → max θ 1< y i):=by
     have f:=p i (Set.mem_univ _); change Y.lower i < y i ∧ y i < Y.upper i at f
     by_cases u:i=(3:Axis)
     · simp only [Y,MiterT.appoint,u,if_pos,Real.dist_eq,abs_lt,MiterT.forest,true_imp_iff] at f ⊢
       exact ⟨⟨by linarith only [f.1,hε,hh],by linarith only [f.2,hε,hh]⟩, hc.trans f.1⟩
     simp [Y,MiterT.appoint,Real.dist_eq,u,MiterT.forest,eq_comm,abs_lt] at f ⊢
     constructor <;> linarith only [f.1,f.2,hh,hε]
 exact ⟨((dist_pi_lt_iff h).2 (fun i=> (B i).1)).le,(B (3:Axis)).2 rfl⟩
section
variable (X:Hilbert)(k:X)(f:Lead.Clan→Vantage→X)(t θ:ℝ)
-- centered matrix
abbrev zoneH(F G':SampleDose): Matrix Lead.Clan Lead.Clan ℂ:= Matrix.of (fun i j=> inner ℂ (paster k (DoseTravel.beam X (flipDose F 3) (f i))) (paster k (DoseTravel.beam X G' (f j))))
private lemma viableGram(A:Lead.Clan→X.space)(h:LinearIndependent ℂ A): ReadsSix (Matrix.gram ℂ A):=by
 refine ⟨Matrix.det_gram_ne_zero_iff_linearIndependent.mpr h,fun i=>?_⟩
 exact fun e=> h.ne_zero i (inner_self_eq_zero.mp (show inner ℂ (A i) (A i)=0 from e))
abbrev proto (z:(Lead.Clan→X.space)×(Lead.Clan→X.space)):CrossRead:= Matrix.of fun i j=>inner ℂ (paster k (z.1 i)) (paster k (z.2 j))
lemma firing : Continuous (proto X k):= continuous_matrix fun i j=> ((paster k).continuous.comp ((continuous_apply i).comp continuous_fst)).inner ((paster k).continuous.comp ((continuous_apply j).comp continuous_snd))
private lemma fir (i:Vantage)(h:LinearIndependent ℂ (fun r:Lead.Clan=>paster k (f r i))):
 let M:= Lead.Clan→ X.space; let L(n):=f n i; ∃ d:ℝ,0<d ∧ ∀ x ∈ Metric.ball ((L,L):M×M) d,ReadsSix (proto X k x):= by
    intro M L; let b:=((L,L):M×M); have HE:ReadsSix (proto X k b):= viableGram X _ h
    exact Metric.mem_nhds_iff.mp (((firing X k).continuousAt (x:=b)).tendsto.eventually (show {m:CrossRead|ReadsSix m}∈𝓝 _ from readsSix_open.mem_nhds HE))
private lemma heatwave (p:Vantage)(hp:∀ i,Continuous (f i)){L0:Lead.Clan→X.space}{L:Vantage→Lead.Clan→ X.space}(h:∀ i t,L t i=f i t)(hx:L p=L0)(ε d:ℝ)(hv:0<ε)(a:0<d)(hd:∀ r:Vantage,dist r p<ε→ dist (L r) (L p)<d/2)(q:SampleDose)(hQ:q.Normalized)(g:∀r∈tsupport q.val,dist r p ≤ ε/2): dist (fun i=>DoseTravel.beam X q (f i)) L0 <d:=by
    rw [dist_pi_lt_iff a]; intro i; rw [dist_eq_norm,← hx,h]; refine (DoseTravel.tol p X _ (hp i) q hQ _ (fun j v'=>?_)).trans_lt (half_lt_self a)
    rw [← dist_eq_norm,← h,←h]; exact (dist_le_pi_dist (L j) (L p) i).trans ((hd j ((g j v').trans_lt (half_lt_self hv))).le)
abbrev Films(R:Hilbert):= Lead.Clan→R.space
private lemma vehicle (R:Hilbert)(K Z:Films R)(a d c:ℝ)(D B:Doorway)(x:Vantage)(E F:SampleDose)(n:E.Normalized)(m:F.Normalized)(r:tsupport E.val⊆ D.invites)(s:tsupport F.val⊆ B.invites)
(g:SampleDose→Films R)(hb:∀ (U:SampleDose),U.Normalized→ (∀ y∈tsupport U.val,dist y x≤ d)→ dist (g U) K<a)(h:∀ y:Vantage,poseMirror 3 y∈D.invites→dist y x≤d∧c<y 3)(v:∀ y:Vantage,y∈B.invites→dist y x≤d∧c<y 3): (g (flipDose E 3),g F) ∈ Metric.ball (K,K) a:=by
 rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
 refine ⟨hb (flipDose E 3) (flipPay E n 3) (fun z p=> (h z (r ?_)).1),hb F m (fun z p=> (v z (s p)).1)⟩
 rw [flipBudget] at p; exact p
private lemma earnsW (f':Vantage)(d:ℝ)(h:0<d)(p:∀ i,Continuous (f i)):∃ ε:ℝ,0<ε∧∀q:SampleDose,q.Normalized→(∀y∈tsupport q.val,dist y f' ≤ ε /2)→dist (fun i=> DoseTravel.beam X q (f i)) (fun i=> f i f') <d:=by
 let Y(t:Vantage):Films X:=fun i=> f i t; have he:Continuous Y:=continuous_pi p
 obtain ⟨ε,v,u⟩:= Metric.continuousAt_iff.mp (he.continuousAt (x:=f')) (d/2) (half_pos h)
 exact ⟨ε,v,heatwave X f f' p (L:=Y) (fun _ _=>rfl) rfl _ _ v h (fun i e=>u e)⟩
structure Whisper(c:ℝ):Prop where
 calls:∃ (A B':Doorway), A.Later B' orderV 0 ∧ (∀ y:Vantage,poseMirror 3 y∈A.invites→max c 1<y 3) ∧ (∀y:Vantage,y∈B'.invites→max c 1<y 3)∧
 ∀E V:SampleDose,E.Normalized→V.Normalized→tsupport E.val ⊆ A.invites→tsupport V.val ⊆B'.invites→ReadsSix (zoneH X k f E V)
private lemma backend(i:Vantage)(a d c:ℝ)(D B:Doorway)(E F:SampleDose)(n:E.Normalized)(m:F.Normalized)(r:tsupport E.val⊆ D.invites)(s:tsupport F.val⊆ B.invites)(h:∀ y:Vantage,poseMirror 3 y∈D.invites→dist y i ≤d∧c<y 3)(v:∀ y:Vantage,y∈ B.invites→dist y i ≤d∧c<y 3)(p:∀ x∈ Metric.ball (((fun n=>f n i),(fun n=>f n i)):Films X × Films X) a,ReadsSix (proto X k x))(g:∀q:SampleDose,q.Normalized→(∀y∈tsupport q.val,dist y i ≤d)→ dist (fun n=>DoseTravel.beam X q (f n)) (fun n=> f n i)<a): ReadsSix (zoneH X k f E F):=
 (p ((fun i=>DoseTravel.beam X (flipDose E 3) (f i)),(fun i=>DoseTravel.beam X F (f i))) (vehicle X (fun n=>f n i) (fun n=>f n i) a d c D B i E F n m r s (fun q n=>DoseTravel.beam X q (f n)) g h v))
lemma beatBeat {c p0:ℝ}(hc:c <p0)(hp:1 <p0) (p:∀ i,Continuous (f i))(h:LinearIndependent ℂ (fun i:Lead.Clan=>paster k (f i (MiterT.forest p0)))): Whisper X k f c:=by
 let L(i:Lead.Clan):= f i (MiterT.forest p0)
 let i:= MiterT.forest p0
 refine (fir X k f i h).elim fun δ he=> (earnsW X f i δ he.1 p).elim fun ε hv=>?_
 refine (doors_f hc hp (ε/2) (half_pos hv.1)).elim fun A H0=> H0.elim fun B heG=>?_
 refine ⟨A,B,heG.1,(fun y t=> (heG.2.1 y t).2),fun y t=> (heG.2.2 y t).2,fun E V n a r s=> backend X k f i δ (ε/2) (max c 1) A B E V n a r s heG.2.1 heG.2.2 he.2 hv.2⟩
#print axioms beatBeat
end
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
