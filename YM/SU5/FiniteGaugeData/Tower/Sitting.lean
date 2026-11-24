import YM.SU5.FiniteGaugeData.Tower.Hard
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Count and qualify upper affected factors
-/
open Push.GridApprox Tree Next.SectorChange Stencil Tap Tenant
variable (S:Finset Cover)(P:Patch)(Z:KernelChoices)(p:P.Branches Z SU.group)
variable {X:Type*}(c f:Side)(h:(More f).val=(More c).val*P.L.val)
local notation "B"=> fixedStep P Z (fun _:Unit=>c) (fun _:Unit=>f) (fun _:Unit=>h) ()
variable (V:X→LinksC)
local notation "W" x:max=>Satin.graft S f (V x)
local notation "D"=>Push.GridApprox.reach P

def sensitive(P:Patch)(Z:KernelChoices)(S:Finset Cover)(c f:Side)(h:(More f).val=(More c).val*P.L.val):Finset (Seat c) := (univ:Finset (Seat c)).filter (fun i=> ∃ t∈ S, wrap (More f) t ∈ window ((StepData.ratio (fixedStep P Z (fun _:Unit=>c) (fun _:Unit=>f) (fun _:Unit=>h) ())).embed i) (Push.GridApprox.reach P)) -- tune
local notation "πS"=> sensitive P Z S c f h
lemma witness(i:Seat c): i∈πS↔ ∃(t:Cover)(v:t∈ S)(d:Cover)(w:d∈ Lattice.box D), (B).ratio.embed i= wrap (More f) t-wrap (More f) d:=by
 unfold sensitive; rw [mem_filter]; change (_∧_)↔_
 constructor
 · rintro ⟨_,t,b,y,r,hy⟩; refine ⟨t,b,y,r,?_⟩; dsimp at hy; rw [←hy]; abel
 rintro ⟨t,z,y,b,hy⟩; refine ⟨mem_univ _,t,z,y,b,?_⟩; dsimp; rw [hy]; abel
lemma sensitive_count: (πS).card ≤ S.card * (Lattice.box D).card:=by
 let a:= (Lattice.box D)
 choose t T v V g using (fun i:↥(πS)=> (witness S P Z c f h i.val).1 i.property)
 let p(i:↥(πS)) : ↥S × ↥a:= (⟨t i,T i⟩, ⟨v i,V i⟩)
 have hp: Injective p:=by
    intro i j e; have ht : t i=t j := congrArg (fun x=> (x:↥S × ↥a).1.val) e; have hv : v i=v j:=congrArg (fun x=> (x:↥S × ↥a).2.val) e
    have he : ((B).ratio).embed i.val=((B).ratio).embed j.val:=by rw [g i,g j,ht,hv]
    exact Subtype.ext ((B).ratio.embed_injective he)
 have he:=Fintype.card_le_of_injective p hp; simpa using he

def hitEdges(S:Finset (Seat c)):= univ.filter fun i:Edge (Seat c)=>i.1∈ S ∨ i.1+step i.2∈ S
lemma hit_count (S:Finset (Seat c)): (hitEdges c S).card ≤ S.card * Fintype.card Axis * 2:=by
 let a:Finset (Edge (Seat c)):= S ×ˢ univ
 let d(e:Edge (Seat c)):Edge (Seat c):=(e.1-step e.2,e.2)
 have he: hitEdges c S ⊆ a ∪ a.image d:=by
    rintro ⟨x,k⟩ p; rcases (mem_filter.mp p).2 with h|h
    · exact mem_union_left _ (mem_product.mpr ⟨h,mem_univ _⟩)
    refine mem_union_right _ (mem_image.mpr ⟨(x+step k,k),mem_product.mpr ⟨h,mem_univ _⟩,?_⟩)
    unfold d; simp
 calc
  (hitEdges c S).card ≤ (a∪a.image d).card:=card_le_card he
  _ ≤ a.card+(a.image d).card:= card_union_le ..
  _ ≤ a.card+a.card:= Nat.add_le_add_left card_image_le _
  _= _:= by unfold a; rw [card_product,card_univ]; omega

local notation "πE"=>hitEdges c (πS)
include p
lemma outland(x y:X){t:Seat c}(v:t∉ πS): Agrees (window ((B).ratio.embed t) D) (W x) (W y):=by
 rintro ⟨i,k⟩ u _
 unfold Satin.graft; dsimp only; split; swap; · rfl
 next g=> obtain ⟨⟨b,d⟩,e⟩:=g; exact (v (mem_filter.mpr ⟨mem_univ _,b,d,(show _ from by change wrap (More f) b=i at e; rw [e]; exact u)⟩)).elim
lemma affected_site(x y:X){t:Seat c}(v:t∉ πS)(j:P.FrameTag): perSite B (W x) t j=perSite B (W y) t j:=
 (site_dep B p t (outland S P Z p c f h V x y v) j).2
lemma affected_link(x y:X){e:Edge (Seat c)}(v:e∉ πE)(u:(B).SitesChoice)(k:SU.E)(β:ℝ): perLink B β (W x) u e k=perLink B β (W y) u e k:=by
 have ht(q: e.1∈πS ∨ e.1+step e.2∈πS): False:= v (mem_filter.mpr ⟨mem_univ _,q⟩)
 unfold perLink; rw [connector_dep B p e u u rfl rfl (outland S P Z p c f h V x y (fun p=>ht (Or.inl p))) (outland S P Z p c f h V x y (fun p=> ht (Or.inr p)))]
lemma link_lower (U:Config SU.group (More f))(t:(B).SitesChoice)(e:Edge (Seat c))(k:SU.E)(β:ℝ): 0 ≤ perLink B β U t e k:=by
 unfold perLink; refine sum_nonneg fun i _=>mul_nonneg ?_ ?_
 · unfold Patch.predictorMass; split; positivity; exact P.weight_nonneg _
 unfold noiseLink StepData.penaltyWeight; have ht:= @StepData.penaltyZ_pos (More c) (More f) B SU.group β; exact mul_nonneg (inv_pos_of_pos ht).le (Real.exp_pos _).le
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.sensitive_count
#print axioms YM.CF.Buffered.Afterglow.Tower.affected_link
