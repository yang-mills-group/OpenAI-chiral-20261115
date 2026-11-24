import GaugeFieldConstruction.Apse
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
-- floor grades.existence.S.D proof by explicit lift.Section unnorm
open Calibration.Floor U1
local notation "Ut" => Calibration.Shell
lemma EffortK (A:Waves) : SpineM A=shellP A:=by unfold SpineM; simp only [LinearMap.coe_mk,AddHom.coe_mk] -- tune
lemma lives3(p:P03)(i:FlavorIndex) : symf3 p i∈ Record.space Row.B:=by
 have he:symf3 p∈LinearMap.range symf3:=⟨p,rfl⟩; rw [sch3] at he; exact he _ (Set.mem_univ _) -- tune direct pi
lemma lives4(p:P14)(i:FlavorIndex):symf4 p i∈ Record.space evalTf:=(show symf4 p∈ shelfV (Record.space evalTf) from sch4 ▸ (show _ from (show symf4 p∈LinearMap.range symf4 from ⟨_,rfl⟩))) _ (Set.mem_univ _)
lemma lives5(p:P25)(i:FlavorIndex):symf5 p i∈ Record.space evalF:=(show symf5 p∈ shelfV (Record.space evalF) from sch5 ▸ (show symf5 p∈LinearMap.range symf5 from ⟨_,rfl⟩)) _ (Set.mem_univ _)
lemma livesX(p:G15)(i:FlavorIndex):task_M p i∈ Record.space evalX:=by
 have he: task_M p∈LinearMap.range task_M:=⟨p,rfl⟩; rw [task_range] at he; exact he _ (Set.mem_univ _)
-- Approx cues.Set
abbrev metK: Floor→ ℕ | .three=> 0 | .four=>1 | .five=>2
abbrev LegL(A:Waves)(d:Floor):Prop:= MSlot (metK d) A=A
lemma leg_3(A:Waves): LegL A three ↔ A.2=0:=by
 refine ⟨fun h=>(show 0=A.2 from congrArg Prod.snd h).symm,fun e=>?_⟩; exact Prod.ext rfl (show (0:J4×J5)=A.2 from e.symm)
lemma leg_4(A:Waves): LegL A four ↔ A.2.2=0:=by
 refine ⟨fun e=>(show 0=A.2.2 from congrArg (fun i:Waves=>i.2.2) e).symm,fun h=>?_⟩; exact Prod.ext rfl (Prod.ext rfl (show (0:J5)=A.2.2 from h.symm))
lemma leg_5(A:Waves): LegL A five:=rfl -- condition decidable
local notation "Cuv" => Fragment (J Row.f)
abbrev Umatrix (d:Floor): Set Ut:= {X| X.1=0∧ X∈ LinearMap.range (shells d)}
lemma port3 (p:P03): SpineM (p,0)= (0,0,symf3 p,0):=by -- implicit prod Waves not (p,0) ok
 rw [EffortK]; unfold shellP; refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
 · change μG 0 + μD 0=0; rw [map_zero,map_zero,add_zero]
 · change symf3 p+(symf4 0 +symf5 0)= _; rw [map_zero,map_zero,add_zero, add_zero]; try rfl
 change task_M 0=0; rw [map_zero]
lemma port4(p:P03)(g:G3)(q:P14): SpineM (p,(g,q),0)= (0,μG g,symf3 p+symf4 q,0):=by
 rw [EffortK]; unfold shellP; refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
 · change μG g+ μD 0=μG g; rw [map_zero,add_zero]
 · change symf3 p+(symf4 q+symf5 0)= _; rw [map_zero, add_zero]; try rfl
 change task_M 0=0; rw [map_zero]
lemma pointsM (Q:Ut)(d:Floor): Q∈ Umatrix d↔ Q.1=0∧ Q.2.1∈SG d ∧ (∀ p,Q.2.2.1 p∈SF d)∧ ∀ p,Q.2.2.2 p ∈ SX d:=by
 refine ⟨fun ⟨p,vxk,h⟩=>⟨p,?_,?_,?_⟩,fun ⟨p,vxk,g,H⟩=>?_⟩
 · rw [←h]; exact vxk.2.1.property
 · rw [←h]; exact fun y=> (vxk.2.2.1 y).property
 · rw [←h]; exact fun y=> (vxk.2.2.2 y).property
 let a:UV d:= (Q.1,⟨_,vxk⟩, (fun y=>⟨_,g y⟩),fun y=>⟨_,H y⟩) -- parsing fun b tuple? parentheses
 exact ⟨p,a,rfl⟩
lemma harbour (d:Floor)(v:Waves)(u:LegL v d): SpineM v∈Umatrix d:=by
 rw [pointsM]; let Q:=SpineM v; obtain ⟨p,⟨q,r⟩,s,t,w⟩:= v; cases d
 · have hp:(q,r)=(0:J4) ∧ (s,t,w)=(0:J5):=Prod.mk.inj ((leg_3 _).1 u); rw [hp.2,hp.1,show ((0:J4), (0:J5))=(0:J4×J5) from rfl,port3]; exact ⟨rfl,(SG three).zero_mem,lives3 _,fun i=> (SX three).zero_mem⟩
 · rw [(show (s,t,w)=(0:J5) from (leg_4 _).1 u),port4]; exact ⟨rfl,(milkG q).1,fun i=>(SF four).add_mem ((show fThree≤SF four from le_sup_left) (lives3 p i)) ((show Record.space evalTf ≤ SF four from le_sup_right) (lives4 r i)),fun i=>(SX four).zero_mem⟩
 let F:=SF five; let a:=SF four; let b:=SF three; let f:= Record.space evalTf; let D:= Record.space evalF; rw [EffortK]
 refine ⟨rfl,(SG five).add_mem ((show SG four ≤ SG five from belowg _) (milkG q).1) ((show Record.space evalG ≤ SG five from le_sup_right) (milkD s).1),fun i=>?_,fun i=>livesX w i⟩
 change symf3 p i+(symf4 r i+symf5 t i)∈_; exact F.add_mem ((show b≤F from belowf _) (lives3 _ i)) (F.add_mem ((show f≤F from le_trans (show f≤ a from le_sup_right) (belowf _)) (lives4 _ i)) ((show D≤ F from le_sup_right) (lives5 t i)))
lemma habs3 (u:Fragment (J Row.f))(h:∀ i, u i∈ SF three):∃ p:↥P03,symf3 p=u :=by
 have he:u∈LinearMap.range symf3:=by rw [sch3]; exact fun i _=> h i
 exact he
lemma habs4(u:Fragment (J Row.f))(h:∀ i,u i∈ SF four): ∃ p:↥P03,∃ q:↥P14,u= symf3 p+symf4 q:=by
 choose x hx y hy g using (fun i=> (Submodule.mem_sup.mp (show u i∈ SF three ⊔ Record.space evalTf from h i)))
 obtain ⟨p,a⟩:=habs3 x hx; have hp:y∈LinearMap.range symf4:=by rw [sch4]; exact fun i _=>hy i
 obtain ⟨q,e⟩:=hp; refine ⟨p,q,?_⟩; rw [a,e]; ext1 i; exact (g i).symm
lemma habs5 (u:Fragment (J Row.f))(h:∀ i,u i∈ SF five):∃ p:↥P03,∃ q:↥P14,∃ z:↥P25,u=symf3 p+(symf4 q+symf5 z):=by
 choose x hx y hy g using (fun i=>(Submodule.mem_sup.mp (show u i∈ SF four ⊔ Record.space evalF from h i)))
 obtain ⟨p,s,a⟩:= habs4 x hx; have hp:y∈LinearMap.range symf5:=by rw [sch5]; exact fun i _=>hy i
 obtain ⟨t,e⟩:=hp; refine ⟨p,s,t,?_⟩; rw [← add_assoc, ← a, e]; ext1 i; exact (g i).symm
lemma portPic (u:Ut)(d:Floor)(h:u∈Umatrix d): ∃ p:Waves, LegL p d∧ SpineM p=u:=by
 rcases u with ⟨_,k,p,q⟩; obtain ⟨e,f,h,g⟩:=(pointsM _ d).1 h
 cases d
 · obtain ⟨r,a⟩:=habs3 p h; refine ⟨(r,0),rfl,?_⟩; rw [port3,a]; exact Prod.ext e.symm (Prod.ext (show 0=k from (show k=0 from f).symm) (Prod.ext rfl (funext fun i=> (show q i=0 from g i).symm)))
 · obtain ⟨r,s,h⟩:= habs4 p h; obtain ⟨a,u⟩:= (show k∈LinearMap.range μG from by rw [wonG]; exact f); refine ⟨(r,(a,s),0),rfl,?_⟩; rw [port4,u]; exact Prod.ext e.symm (Prod.ext rfl (Prod.ext h.symm (funext fun i=> (show q i=0 from g i).symm)))
 obtain ⟨r,s,t,h⟩:=habs5 p h; have hx:q∈ LinearMap.range task_M:=by rw [task_range]; exact fun j _=>g j
 obtain ⟨v,V⟩:=hx; obtain ⟨a,b,c,d,L⟩:= Submodule.mem_sup.mp (show k∈LinearMap.range μG ⊔ LinearMap.range μD from by rw [wonG,wonD]; exact f)
 obtain ⟨A,p₀⟩:=b; obtain ⟨B,p₁⟩:=d; let W:=Fikit (r,s,t) A B v; refine ⟨W,leg_5 W,Prod.ext e.symm (Prod.ext ?_ (Prod.ext h.symm V))⟩; change μG A+μD B=k; rw [p₀,p₁,L]

end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
#print axioms YM.CF.XGarden.MastTin.ArtCart.BluffV.portPic
#print axioms YM.CF.XGarden.MastTin.ArtCart.BluffV.QuenchF
