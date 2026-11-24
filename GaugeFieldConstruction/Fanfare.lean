import GaugeFieldConstruction.Fust
import GaugeFieldConstruction.Pleiad
set_option autoImplicit false
set_option maxHeartbeats 230000
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
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open TableF.Lenten.Loden Phys
abbrev Solo2(p:P14):PHPane:= (0,p,0)
abbrev Solo3 (p:P25):PHPane:= (0,0,p)
def dyan : P14→ₗ[ℂ] PHPane:= (LinearMap.inr ℂ ↥P03 (↥P14× ↥P25)).comp (LinearMap.inl ℂ ↥P14 ↥P25)
def dyar : P25→ₗ[ℂ] PHPane:= (LinearMap.inr ℂ ↥P03 (↥P14× ↥P25)).comp (LinearMap.inr ℂ ↥P14 ↥P25)
-- span mechanical.
def Hymn (p:PHPane):Prop:=∃ (b:Bool)(W:Fees b), p=dyan (taxW W)∨∃ j:FactIx,p=dyar (taxΘ j W)
def Rocker:Submodule ℂ PHPane:= Submodule.span ℂ {p| Hymn p}
def RockS_ : (CornerH→ P03)→ₗ[ℂ]PHPane:=∑ i: CornerH,(Debye i).comp (LinearMap.proj i)
lemma Rock_v (f:CornerH→P03):RockS_ f=∑ i:CornerH, Debye i (f i):=by rw [RockS_,LinearMap.sum_apply]; rfl -- tune
lemma RockG (i:CornerH)(x:P03):Debye i x∈ LinearMap.range RockS_:=by
 refine ⟨Pi.single i x,?_⟩; rw [Rock_v,sum_eq_single i]; · simp
 · intro j _ t; rw [Pi.single_eq_of_ne t,map_zero]
 simp
lemma visaP24 (p:PHPane)(q:p∈Rocker):lineup p=0:=by
 apply Submodule.span_induction (p:=fun p _=>lineup p=0) ?_ ?_ ?_ ?_ q
 · rintro x ⟨b,u,h|⟨j,h⟩⟩
   · rw [h,show dyan (taxW u)=Solo2 (taxW u) from rfl,Solo2,lineupH,map_zero,map_zero, kataP,add_zero,add_zero]
   rw [h,show dyar (taxΘ j u)=Solo3 (taxΘ j u) from rfl,Solo3,lineupH,map_zero,map_zero,kataT,add_zero,add_zero]
 · exact map_zero _
 · intro i j _ _ h v; rw [map_add,h,v,add_zero]
 intro a i _ p; rw [map_smul,p,smul_zero]
private abbrev FloorP:= Rocker ⊔ LinearMap.range RockS_
lemma Summit2 (x y:SpaceH)(A:P03): dyar (peakV (lotH x) (lotH y) A)∈FloorP:=by
 -- boltSk private if imported can't access (!) private across modules? Lean server pre masks. need public.
 by_cases p: boltSk x≤ boltSk y
 · let i: SummitH:= (⟨(x,y),p⟩ : { u:SpaceH×SpaceH// boltSk u.1 ≤ boltSk u.2}); exact (show LinearMap.range RockS_≤ FloorP from le_sup_right) (RockG (Sum.inr (Sum.inr i)) A)
 rw [peak_H]; let i: SummitH:= (⟨(y,x),le_of_lt (lt_of_not_ge p)⟩ : { u:SpaceH×SpaceH// boltSk u.1 ≤ boltSk u.2}); exact (show LinearMap.range RockS_≤ FloorP from le_sup_right) (RockG (Sum.inr (Sum.inr i)) A)
lemma charter2 (x:SpaceH)(p:FactIx)(A:P03) : dyar (peakV p (lotH x) A)∈ FloorP:=by
 obtain ⟨b,i⟩:=p; refine Fin.lastCases (i:=i) ?_ (fun i: S3=> Summit2 (b,i) x A)
 have he:∃ Y:Fees (!b),wedgeJ τ Y=A:=by
    cases b; · obtain ⟨y,h⟩:=ΓLeft A; exact ⟨y,Subtype.ext h⟩
    obtain ⟨y,h⟩:=ΓRight A; exact ⟨y,Subtype.ext h⟩
 obtain ⟨Y,g⟩:=he; have h:TipO (!b) τ=(b,Fin.last 3):=by unfold TipO; congr 1; simp -- tune
 let K(i:Axis):=dyar (peakV (lotH x) (TipO (!b) i) (wedgeJ i Y)); have hp: dyar (taxΘ (lotH x) Y)∈Rocker:=Submodule.subset_span (show Hymn _ from ⟨!b,Y,Or.inr ⟨_,rfl⟩⟩)
 have hv:∑ i:Axis,K i∈ FloorP:=by unfold K; rw [←map_sum]; exact (show Rocker≤FloorP from le_sup_left) hp
 have ht(v: S3): K v.castSucc∈ FloorP:= by unfold K; exact Summit2 x (!(!b),v) _
 rw [←g, peak_H,←h]; rw [Fin.sum_univ_castSucc] at hv; exact (FloorP.add_mem_iff_right (Submodule.sum_mem _ fun i _=>ht i)).mp hv
lemma revH (i j:FactIx)(A:P03): dyar (peakV i j A)∈ FloorP:=by
 obtain ⟨b,p⟩:=i; refine Fin.lastCases (i:=p) ?_ (fun p:S3=>?_); swap; · rw [peak_H]; exact charter2 (b,p) _ _
 have he:∃ Y: Fees (!b),wedgeJ τ Y=A:=by
    cases b; · obtain ⟨y,h⟩:=ΓLeft A; exact ⟨y,Subtype.ext h⟩
    obtain ⟨y,h⟩:=ΓRight A; exact ⟨y,Subtype.ext h⟩
 obtain ⟨Y,g⟩:=he; have hx:TipO (!b) τ=(b,Fin.last 3):=by unfold TipO; congr 1; simp
 let X(i:Axis):= dyar (peakV j (TipO (!b) i) (wedgeJ i Y)); have hv:X τ∈FloorP:=by
    have he:∑ i:Axis,X i∈FloorP:=by unfold X; rw [←map_sum]; exact (show Rocker≤FloorP from le_sup_left) (Submodule.subset_span (show Hymn _ from ⟨!b,Y,Or.inr ⟨j,rfl⟩⟩))
    rw [Fin.sum_univ_castSucc] at he; exact ((FloorP.add_mem_iff_right (Submodule.sum_mem _ fun i _=>charter2 (!(!b),i) j _))|>.mp he) -- tune math
 rw [←hx,←g,peak_H]; exact hv
lemma rev_1 (i:FactIx)(A:P03): dyan (spikeV i A)∈FloorP:=by
 obtain ⟨b,p⟩:=i; refine Fin.lastCases (i:=p) ?_ (fun p:S3=>(show LinearMap.range RockS_≤ FloorP from le_sup_right) (RockG (Sum.inr (Sum.inl (b,p))) A))
 have he:∃ Y: Fees (!b),wedgeJ τ Y=A:=by
    cases b; · obtain ⟨y,h⟩:=ΓLeft A; exact ⟨y,Subtype.ext h⟩
    obtain ⟨y,h⟩:=ΓRight A; exact ⟨y,Subtype.ext h⟩
 obtain ⟨Y,g⟩:=he; have hx:TipO (!b) τ=(b,Fin.last 3):=by unfold TipO; congr 1; simp
 let X(i:Axis):= dyan (spikeV (TipO (!b) i) (wedgeJ i Y)); have hv:X τ∈FloorP:=by
    have he:∑ i:Axis,X i∈FloorP:=by unfold X; rw [←map_sum]; exact (show Rocker≤FloorP from le_sup_left) (Submodule.subset_span (show Hymn _ from ⟨!b,Y,Or.inl rfl⟩))
    have ht(p:S3) : X p.castSucc∈ FloorP:=by unfold X; exact (show LinearMap.range RockS_≤ FloorP from le_sup_right) (RockG (Sum.inr (Sum.inl (!(!b),p))) (wedgeJ p.castSucc Y))
    rw [Fin.sum_univ_castSucc] at he; exact (FloorP.add_mem_iff_right (Submodule.sum_mem _ fun i _=> ht i)).mp he
 rw [←hx,←g]; exact hv
lemma coverΦ(p:PHPane): p∈ FloorP:=by
 rcases p with ⟨a,b,c⟩; let A:PHPane:=(a,0,0); rw [show (a,b,c)=A+(dyan b+ dyar c) from ?_]
 · refine FloorP.add_mem ((show LinearMap.range RockS_ ≤ FloorP from le_sup_right) (RockG (Sum.inl ()) a)) (FloorP.add_mem ?_ ?_)
   · rw [spikeBus b,map_sum]; exact Submodule.sum_mem FloorP fun i _=> rev_1 i _
   rw [peakBus c,map_sum]; apply Submodule.sum_mem FloorP; intro i _; rw [map_smul]; exact FloorP.smul_mem _ (revH i.1 i.2 _)
 apply Prod.ext (show a=a+(0+0) from by rw [add_zero,add_zero]); apply Prod.ext _ _; · change b= 0+(b+0); rw [add_zero,zero_add]
 change c=0+(0+c); rw [zero_add,zero_add] -- tune
lemma rustles (p:PHPane): lineup p=0 ↔ p∈ Rocker:=by
 refine ⟨fun v=> ?_, visaP24 p⟩; obtain ⟨i,b,j,⟨k,f⟩,e⟩:= Submodule.mem_sup.mp (coverΦ p); rw [←f] at e; rw [←e,map_add,visaP24 _ b,zero_add, Rock_v] at v; have hp:=WalkS_ k v; rw [←e,hp,map_zero,add_zero]; exact b
lemma kerΦ : Rocker=LinearMap.ker lineup:=by ext1 i; exact (rustles i).symm
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
