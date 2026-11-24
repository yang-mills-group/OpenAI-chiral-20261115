import Velour.Wadding.Pleats
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

private lemma assort {R S : Type*}[Ring R][Algebra ℂ R][Ring S][Algebra ℂ S]
   {I J:Type*}[Inhabited J] (L:List I)
   (K:I→Finset J)(a:I→J→R)(b:I→J→S)(w:I→J→ℂ)
   (f:R→ₗ[ℂ]ℂ)(g:S→ₗ[ℂ]ℂ)(u:L.Nodup)
   (h:∀p:I→J,(∀i∈L,p i∈K i)→
    f (L.map fun i=>a i (p i)).prod=g (L.map fun i=>b i (p i)).prod):
 f (L.map fun i=>∑ k∈K i,w i k • a i k).prod=
 g (L.map fun i=>∑ k∈K i,w i k • b i k).prod:=by
 classical
 induction L generalizing f g with
 | nil=> exact h (fun _=>default) (by simp)
 | cons i L ih=>
   obtain ⟨t,d⟩:=List.nodup_cons.mp u
   simp only [List.map_cons,List.prod_cons, Finset.sum_mul, smul_mul_assoc,map_sum,map_smul]
   refine Finset.sum_congr rfl fun k e=> congrArg (fun z:ℂ=> w i k • z) ?_
   refine ih (f.comp (LinearMap.mul ℂ R (a i k))) (g.comp (LinearMap.mul ℂ S (b i k))) d fun p r=>?_
   change f (a i k * _)=g (b i k * _)


   let q j:= if j=i then k else p j
   have hi:q i=k:=if_pos rfl
   have hj:∀j∈L,q j=p j:=fun j z=>if_neg (fun y:j=i=>t (y ▸ z))
   have B:=h q (fun j c=>by
      rcases List.mem_cons.mp c with rfl|v
      · rwa [hi]
      rw [hj j v]; exact r j v)
   rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,hi,
       show L.map (fun j=>a j (q j))=L.map (fun j=>a j (p j)) from
         List.map_congr_left fun j v=>congrArg (a j) (hj j v),
       show L.map (fun j=>b j (q j))=L.map (fun j=>b j (p j)) from
         List.map_congr_left fun j v=>congrArg (b j) (hj j v)] at B
   exact B

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "E₀"=> (Σ₀).E
local notation "E₁"=> (Σ₁).E
local notation "ϕ"=> P.enter j x
local notation "ρ"=> P.wealth j x
local notation "W"=> P.cartage j x
local notation "Ξ"=> P.truck j x


local notation "ω"=> P.colorZero j x
variable {I:Type}(L:List I)(l r:I→ℝ)

structure EuOrder :Prop where
 parts: ∀i∈L,l i<r i
 order:L.Pairwise fun a b=>r a≤l b
 seams: ∀a b u v, L=u++a::b::v → r a=l b

lemma EuOrder.once (h:EuOrder L l r):L.Nodup:=by
  revert h; induction L with
  | nil=>intro; exact List.nodup_nil
  | cons i L ih=>
    intro h
    obtain ⟨t,u⟩:=List.pairwise_cons.mp h.order
    exact List.nodup_cons.mpr
      ⟨fun y=>not_lt_of_ge (t i y) (h.parts i List.mem_cons_self),
       ih ⟨fun j v=>h.parts j (List.mem_cons_of_mem _ v),u,
        fun a b v w t=>h.seams a b (i::v) w (by rw [t]; rfl)⟩⟩

variable (F:I→SampleDose)(T:I→P.Apron)(t:ℕ)
def PinsStrict (i:I) :Prop:= ∀y∈tsupport (F i).val, 
   let w:=(T i).realWidth P j
   l i<y j-w ∧ y j+w<r i

theorem eu_literal (p:EuOrder L l r)
 (y:∀i∈L,P.PinsStrict j l r F T i)
 (s:∀i∈L,(T i).s≤t):
 P.singleState j t x (L.map fun i=>P.prepared t (T i) (F i)).prod=
 inner ℂ ω ((L.map fun i=>P.pleat j x (l i) (r i) (F i) t (T i)).prod ω):=by
 let a:= ((innerSL ℂ ω).comp
      (ContinuousLinearMap.apply ℂ (ℋ).space ω : (ℋ).Op→L[ℂ](ℋ).space)).toLinearMap
 letI: Inhabited Cover:= ⟨0⟩
 refine assort L (fun i=> P.usedGrid t (F i))
     (fun i k=> P.issuing t (T i) k) (fun i k=> P.raze j x (T i) (l i) (r i) (P.vtile t k))
     (fun i k=>P.activation t (F i) k) _ a (p.once L l r) fun q b=>?_
 let v(i:I):=P.vtile t (q i)
 let z:= P.laysM ∘ v
 have g:∀i∈L,l i<P.porchY j T z i ∧ P.resignY j T z i<r i:=
     fun i c=>y i c (P.meshPose t (q i)) ((P.usedPose t (F i) _).mp (b i c))
 refine (P.turn_purchase j x T q t L ?_ s).symm.trans (P.pill_preview j x T L v l r g p.seams)


 exact p.order.imp_of_mem fun {i k} hi hk t=> (g i hi).2.trans ((lt_of_le_of_lt t (g k hk).1))

variable (a:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 a j
local notation "Ω"=> P.heaven j ξ
local notation "B"=> P.Bobbin j ξ

lemma eu_buttons (Q:I→B)
 (p:EuOrder L l r)
 (J:P.Ellis 3 a)
 (d:I→ℝ≥0)(u:∀i∈L,0< d i ∧ Corners j (l i) (r i) (F i) (d i))
 (σ:I→ℕ→ℕ)(m:ℕ→ℕ)(v:Tendsto m atTop atTop)
 (w:∀i∈L,Tendsto (σ i) atTop atTop)
 (g:∀ᶠ n in atTop,∀i∈L,((Q i).spool (σ i n)).s≤ m n):
 Tendsto (fun n=>P.singleState j (m n) ξ (L.map fun i=>
     P.prepared (m n) ((Q i).spool (σ i n)) (F i)).prod) atTop
    (𝓝 (inner ℂ Ω ((L.map fun i=>P.bobbinEu j ξ (l i) (r i) (F i) (d i) (Q i)).prod Ω))):=by
 let f n i:= (Q i).spool (σ i n)
 have c i (s:i∈L):= (Q i).eu_purchase a j J (u i s).1 (u i s).2 (w i s) v
 have t:=Spreads.prod_runs L c Ω


 rw [← (P.enter j ξ).inner_map_map]
 refine (tendsto_const_nhds.inner t).congr' ?_
 have s:∀ᶠ n in atTop,∀i∈L.toFinset,P.PinsStrict j l r F (f n) i:=by
    classical
    refine L.toFinset.eventually_all.mpr fun i v=>?_
    have b:=List.mem_toFinset.mp v
    have e:=((Q i).thin j).comp (w i b)
    filter_upwards [e.eventually (gt_mem_nhds (show (0:ℝ)<d i from (u i b).1))] with z e y hy
    change (f z i).realWidth P j< (d i:ℝ) at e
    obtain ⟨a',b'⟩:=(u i b).2 y hy
    change l i<y j-(f z i).realWidth P j∧ y j+(f z i).realWidth P j<r i
    constructor <;> linarith only [e,a',b']
 filter_upwards [s,g] with i q r'
 exact (P.eu_literal j ξ L l r F (f i) (m i) p
     (fun _ h=>q _ (List.mem_toFinset.mpr h)) r').symm

#print axioms eu_buttons
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

