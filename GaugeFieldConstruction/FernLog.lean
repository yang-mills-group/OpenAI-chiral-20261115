import GaugeFieldConstruction.Sycamore
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- plen capital: anchor unweighted.White v
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance : Module ℂ Gκ:= PackH.S.toModule
namespace Lave
open Fables Trackℓ
variable (p:BudgetPoint)(h:ℝ){A:Waves}{F:Paper n}
variable (T:TrackD p (Pach (Θk n x)) h F c)(u:portable F)(V:Tuned F)(U:MetaB (Θk n x) M A (AlphaY F) p h)(b:p.power ≤ 3)(s:p.order≤6)(k:0<h)(d:Floor)
private abbrev BId(t:Genre)(Q:Paper n):= t.coinB p h • Q
include w U b s k T u
lemma AuraG (e:HomΓ Genre.gauge d A): Aurora d (Bid p h F x .gauge) .gauge A:=by
 let Q:= BId p h Genre.gauge F; let Y:=VerdK x .gauge Q
 have hp :alignG x Q 0 0=graph_g (μG (bF4 A)):=by
    ext1 ⟨⟨a,i⟩,⟨c,j⟩⟩; change test ((a,i),(c,j)) (alignG x Q 0 0)=test ((a,i),(c,j)) (graph_g (μG (bF4 A))); rw [(GaugeLeader x w T u b s k _ _ A U).1, Phys.income_g, (milkG _).2]; change (if i=j then _ else _) * _= _; split<;>simp
 have he:alignG x Q 0 1 + alignG x Q 1 0=graph_g (μD (bF5 A)):=by
    ext1 ⟨⟨a,i⟩,⟨c,j⟩⟩; change test ((a,i),(c,j)) (alignG x Q 0 1 + alignG x Q 1 0) = test ((a,i),(c,j)) (graph_g (μD (bF5 A))); rw [map_add,(GaugeLeader x w T u b s k _ _ A U).2.1,(GaugeLeader x w T u b s k _ _ A U).2.2, Phys.income_g,(milkD _).2]; -- bool. 
    let v:ℂ:= if i=j then 1/2 else 0; change v * _ + v * _= _; unfold v; split <;> simp [mul_add] -- tune
 have ha:CrestJ 6 Y 0=κgΛ (graph_g (μG (bF4 A))):= by rw [Wick_0,sigG,if_pos rfl,hp] -- tune
 have hX:= e.2; cases d
 · cases hX.1
 · have ht:bF5 A=0:=congrArg Prod.fst hX.2.2
   change CrestJ 6 Y 0=Phys.dress (SpineM A)∧ ∀ i< 0,_; rw [ha,GrainG e.1,ht,map_zero,add_zero]; exact ⟨rfl,fun _ w=>False.elim (Nat.not_lt_zero _ w)⟩
 have ht:bF4 A=0:= congrArg Prod.fst hX.2; change CrestJ 6 Y 1=Phys.dress (SpineM A)∧ ∀ i<1,_; rw [GrainG e.1,ht,map_zero,zero_add, Wick_1,sigG,sigG,sigG]; refine ⟨?_,?_⟩
 · simp only [Nat.one_ne_zero, ↓reduceIte, zero_add]; -- maybe reducing bool
   rw [← map_add,he]
 intro i v; rw [show i=0 from by omega]; change CrestJ 6 Y 0=0; rw [ha,ht,map_zero,map_zero,map_zero]
include V
-- PH book grade even. 
lemma AuraF(e:HomΓ Genre.pure d A): Aurora d (Bid p h F x .pure) .pure A:=by
 let Q:= BId p h Genre.pure F; let Y:= VerdK x .pure Q; let f:= orbitPH (AlphaY F 1); let L:= MastP x Q; have hx:= Stock x T V 1 -- binder tune
 obtain ⟨K,g,R⟩:= φState M x w f h hx; have hm:L= Marlox x f h:= nerf x p h F -- binder tune
 have hv:winJ _ _ _ _=chartF A:= U.port.symm; rw [hv] at g R K; -- change binder tune
 have h₀:CrestJ 6 Y 0=κfΛ (heelY (bV0 A)):=by rw [Wick_0,spPure,if_pos rfl]; change κfΛ (PHale x L 0 0)=_; rw [hm,K]; try rfl
 have h₁(H:bV0 A=0):CrestJ 6 Y 1=κfΛ (μPhi4 (bV1 A)):=by
    have h:=g (show _ from congrArg (fun p:P03=> p.val) H); rw [Wick_1,spPure,spPure,spPure]; simp only [↓reduceIte,Nat.one_ne_zero,zero_add]; rw [←map_add,loam]; change κfΛ (PHale x L 0 1+PHale x L 1 0)= _; rw [hm,h.1,h.2, add_comm]; try rfl
 unfold Aurora; have ht:=e.2; have he: lineup (offP A)= heelY (bV0 A)+(μPhi4 (bV1 A)+μPhi5 (bV2 A)):= lineupH ..; rw [GrainF e.1,he]; cases d
 · change CrestJ 6 Y 0=_∧ ∀ k<0, _; have hp:A.2=0:=ht.2; rw [h₀,show bV1 A=0 from congrArg (fun x:J4×J5=>x.1.2) hp,show bV2 A=0 from congrArg (fun x:J4×J5=> x.2.2.1) hp,map_zero,map_zero,add_zero,add_zero]; exact ⟨rfl,fun i p=> False.elim (Nat.not_lt_zero _ p)⟩
 · change CrestJ 6 Y 1=_ ∧ ∀ k<1, _; have hp: bV0 A=0:= ht.2.1; rw [h₁ hp, hp,show bV2 A=0 from congrArg (fun x:J5=> x.2.1) ht.2.2, map_zero,map_zero,add_zero,zero_add]; refine ⟨rfl,fun i l=>?_⟩; change CrestJ 6 Y i=0; rw [show i=0 from by omega,h₀,hp,map_zero,map_zero]
 have hp:bV0 A=0:=ht.1; have hz: bV1 A=0:=congrArg Prod.snd ht.2;
 have hs:=R (show _ from congrArg (fun q:P03=> q.val) hp) (show _ from congrArg (fun q:P14=> q.val) hz); change CrestJ 6 Y 2=κfΛ _∧ ∀ k<2, CrestJ 6 Y k=0; rw [hp,hz,map_zero,map_zero,zero_add,zero_add]; refine ⟨?_,fun i p=>?_⟩
 · rw [Wick_2,spPure,spPure,spPure,spPure,spPure,spPure]; -- use explicitly if_neg
   simp only [one_ne_zero,Nat.ofNat_pos,OfNat.ofNat_ne_zero, ↓reduceIte,zero_add]; rw [←map_add,←map_add]; change κfΛ (PHale x L 1 1+(PHale x L 0 2+ PHale x L 2 0))= _; rw [hm,hs.2.2,hs.2.1,hs.1]; rw [magΩ,add_comm, add_comm (InPowΦ true _)]; try rfl -- tune
   -- 
 have h:i=0∨i=1:= by omega
 rcases h with h|h; · rw [h,h₀,hp,map_zero,map_zero]
 rw [h,h₁ hp,hz,map_zero,map_zero]
lemma AuraX (H:Solon Genre.mixed F)(e:HomΓ Genre.mixed d A): Aurora d (Bid p h F x .mixed) .mixed A:=by
 let Q:= BId p h Genre.mixed F; let Y:=VerdK x .mixed Q; have he:=e.2; have ht:CrestJ 6 Y 0=dress (SpineM A):=by
    rw [Wick_0,sigH,GrainX e.1]; congr 1; ext1 ⟨a,q⟩; change test (a,q) (MesaP x Q 0 0 0)= test (a,q) (graph_x (task_M (bm5 A))); rw [show test (a,q) (MesaP x Q 0 0 0)= _ from MixedLead M x w p h F A U b s k T H u V a q, taskEarn] -- tune
 cases d <;> exact ⟨ht,fun i t=> False.elim (Nat.not_lt_zero i t)⟩ -- excess zero any
omit w U V b s k T u

abbrev Tag_Γ(W: Waves)(V:Genre):Payν n:=Bid p h (bushMoon M (Θk n x) p h W) x V
include w b s k
lemma auto_K(P:Waves)(V:Genre)(t:HomΓ V d P): let Q:=Tag_Γ (n:=n) M x p h P V; Aurora d Q V P∧ Q.2.2∈ Glamor (Θk n x) V ‖P‖:=by
 intro Q; let W:=bushMoon M (Θk n x) p h P; obtain ⟨T,u,H⟩:= ray_B (o:=Θk n x) M P w k b s 0; let g:=ray_V (o:=Θk n x) M P (lt_trans (by norm_num) w) k b s; have hp:Q.2.2∈ Glamor (Θk n x) V ‖P‖:= ⟨M,p,P,h,b,s,t.1,k,le_rfl,rfl⟩; have hv: MetaB (Θk n x) M P (AlphaY W) p h:= H.port
 refine ⟨?_,hp⟩; cases V
 · exact AuraF _ _ w _ _ T u g hv b s k d t
 · have hx : W=(Genre.mixed.coinB p h)⁻¹ • Q.2.2:= by
      change W=(Genre.mixed.coinB p h)⁻¹ • Genre.mixed.coinB p h • W; rw [inv_smul_smul₀ (Genre.coin_Bu Genre.mixed p k).ne'] -- tune
   exact AuraX _ _ w _ _ T u g hv b s k d (show Solon Genre.mixed W from hx.symm ▸ (Sξ _ (Glamor_S w Genre.mixed ‖P‖ Q.2.2 hp) (Genre.mixed.coinB p h)⁻¹)) t
 exact AuraG _ _ w _ _ T u hv b s k d t
end Lave
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
