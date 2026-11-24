import YM.SU5.Six.ReachDoors
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
open DoseTravel
open _root_.YM.Preen
/-- Choose two all-axis separated boxes, desired placements. -/
def forest(t:ℝ) : Vantage:= fun i=>if i=3 then t else 0
abbrev appoint(t:ℝ)(v:ℝ):Vantage:=fun i=>if i=3 then t else v
private lemma doors_here {t θ:ℝ}(ht:θ<t)(bt:1<t)(ε:ℝ)(h:0<ε):∃ (A B:Doorway),A.Later B (⟨fun _=>true,rfl⟩:Orders) 0 ∧
 (∀ y:Vantage,poseMirror 3 y∈A.invites → dist y (forest t) ≤ ε ∧ max θ (1:ℝ)< y 3) ∧ (∀ y:Vantage,y∈ B.invites → dist y (forest t)≤ ε ∧ max θ (1:ℝ)< y 3):= by
 let q:= min (t-max θ 1) ε / 4
 have he : max θ (1:ℝ)<t := max_lt ht bt
 have hh: 0< q:= div_pos (lt_min (sub_pos.mpr he) h) (by norm_num)
 have hθ: 4*q ≤ t-max θ 1 :=by unfold q; linarith only [min_le_left (t-max θ 1) ε ]
 have hε: 4*q ≤ε:=by unfold q; linarith only [min_le_right (t-max θ 1) ε]
 have hf{a b c d:ℝ} (p:a<b)(q:c<d)(i:Axis) : appoint a c i < appoint b d i:=by by_cases t:i=3 <;> simp [appoint,t,p,q]
 let X:Doorway:= ⟨appoint (-(t+q)) (-q), appoint (-(t-q)) (-q/2),hf (by linarith) (by linarith)⟩
 let Y:Doorway:= ⟨appoint (t-q) (q/2),appoint (t+q) q,hf (by linarith) (by linarith)⟩
 have hc:t-q>max θ 1:=by linarith only [hθ,hh]
 have hz:0<t-q:=lt_trans zero_lt_one ((le_max_right θ 1).trans_lt hc)
 refine ⟨X,Y,fun i=>?_,fun y p=>?_,fun y p=>?_⟩
 · change X.upper i+2*0 <Y.lower i
   rw [mul_zero,add_zero]; exact hf (by linarith) (by linarith) i
 · have B(i):dist (y i) (forest t i)< ε ∧ (i=3 → max θ 1< y i):=by
     have f:=p i (Set.mem_univ _)
     by_cases u:i=(3:Axis)
     · change X.lower i < opposeR 3 y i ∧ opposeR 3 y i < X.upper i at f
       simp only [X,appoint,opposeR,mirrorΩ,u,if_pos,Real.dist_eq,abs_lt,forest,true_imp_iff] at f ⊢
       -- inspect
       exact ⟨⟨by linarith only [f.2,hε,hh],by linarith only [f.1,hε,hh]⟩,by linarith only [f.2,hc]⟩
     change X.lower i < opposeR 3 y i ∧ opposeR 3 y i < X.upper i at f
     simp [X,appoint,opposeR,mirrorΩ,Real.dist_eq,u,forest,eq_comm,abs_lt] at f ⊢
     constructor <;> linarith only [f.1,f.2,hh,hε]
   exact ⟨((dist_pi_lt_iff h).2 (fun i=> (B i).1)).le,(B (3:Axis)).2 rfl⟩
 have B(i):dist (y i) (forest t i)< ε ∧ (i=3 → max θ 1< y i):=by
     have f:=p i (Set.mem_univ _); change Y.lower i < y i ∧ y i < Y.upper i at f
     by_cases u:i=(3:Axis)
     · simp only [Y,appoint,u,if_pos,Real.dist_eq,abs_lt,forest,true_imp_iff] at f ⊢
       exact ⟨⟨by linarith only [f.1,hε,hh],by linarith only [f.2,hε,hh]⟩, hc.trans f.1⟩
     simp [Y,appoint,Real.dist_eq,u,forest,eq_comm,abs_lt] at f ⊢
     constructor <;> linarith only [f.1,f.2,hh,hε]
 exact ⟨((dist_pi_lt_iff h).2 (fun i=> (B i).1)).le,(B (3:Axis)).2 rfl⟩
/-- Weighted unmasked detections. For every normalized test within those boxes. -/
structure Village(X:Hilbert)(k:X)(g:Vantage→X)(t θ:ℝ) where
 earlier: Doorway
 later: Doorway
 located : earlier.Later later (⟨fun _=>true,rfl⟩:Orders) 0
 riseLeft : (∀y:Vantage,poseMirror 3 y∈earlier.invites→max θ (1:ℝ)<y 3)
 riseRight : (∀y:Vantage,y∈later.invites→ max θ (1:ℝ)<y 3)
 pays(F G:SampleDose)(h:F.Normalized)(v:G.Normalized)(f:tsupport F.val⊆earlier.invites)(g':tsupport G.val⊆later.invites): inner ℂ (paster k (beam X (flipDose F 3) g)) (paster k (beam X G g)) ≠0
-- exact. choose. TEMPO
lemma village{X:Hilbert}(k:X){g:Vantage→X}{t θ:ℝ}(ht:θ<t)(bt:1<t)(p:Continuous g)(h:paster k (g (forest t)) ≠ 0):Nonempty (Village X k g t θ):=by
 have he: inner ℂ (paster k (g (forest t))) (paster k (g (forest t))) ≠0:=fun u=> h (inner_self_eq_zero.mp u)
 let Z(q:X.space×X.space):ℂ:=inner ℂ (paster k q.1) (paster k q.2)
 have hZ:Continuous Z:= ((paster k).continuous.comp continuous_fst).inner ((paster k).continuous.comp continuous_snd)
 obtain ⟨δ,d,e⟩:= Metric.mem_nhds_iff.mp ((hZ.tendsto ((g (forest t),g (forest t)))).eventually (show {y:ℂ|y ≠ 0}∈𝓝 _ from isOpen_ne.mem_nhds he)) -- helper isOpen_ne? 
 obtain ⟨ε,v,u⟩:= Metric.continuousAt_iff.mp (p.continuousAt (x:=forest t)) (δ/2) (half_pos d)
 obtain ⟨A,B,W,hA,hB⟩:= doors_here ht bt (ε/2) (half_pos v)
 refine ⟨A,B,W,fun y t=> (hA y t).2,fun y t=>(hB y t).2,fun F G i j r s=>?_⟩
 have b(q:SampleDose)(Q:q.Normalized)(f:∀y∈tsupport q.val,dist y (forest t)≤ ε/2): dist (beam X q g) (g (forest t))<δ:=by
   rw [dist_eq_norm]; refine (DoseTravel.tol (forest t) X _ p q Q _ (fun i h=>?_)).trans_lt (half_lt_self d)
   rw [←dist_eq_norm]; exact (u ((f i h).trans_lt (half_lt_self v))).le
 refine e (show (beam X (flipDose F 3) g,beam X G g) ∈ Metric.ball _ δ from ?_)
 rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
 refine ⟨b (flipDose F 3) (flipPay F i 3) (fun z p=> (hA z (r ?_)).1),b G j (fun z p=> (hB z (s p)).1)⟩
 rw [flipBudget] at p
 exact p
#print axioms village
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
