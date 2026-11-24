import Gingham.Topper
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration YM.Velour
variable (P:Spine) (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=> P.advocate 3 x a
local notation "G"=> P.ManyF a ξ
local notation "S"=> P.seasons a ξ
local notation "Ω"=> P.heaven a ξ
local notation "T"=> (S).E
local notation "V"=> P.cartage a ξ


-- expansion helper copied from Velour/Wadding/Tapes
private lemma assort2 {R R₂ : Type*}[Ring R][Algebra ℂ R][Ring R₂][Algebra ℂ R₂]
   {I J:Type*}[Inhabited J] (L:List I)
   (K:I→Finset J)(a:I→J→R)(b:I→J→R₂)(w:I→J→ℂ)
   (f:R→ₗ[ℂ]ℂ)(g:R₂→ₗ[ℂ]ℂ)(u:L.Nodup)
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
   refine ih (f.comp (LinearMap.mul ℂ R (a i k))) (g.comp (LinearMap.mul ℂ R₂ (b i k))) d fun p r=>?_
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



private lemma scaleList {E I:Type*}[Ring E][Algebra ℂ E]
    (L:List I)(c:I→ℂ)(b:I→E): (L.map (fun i=> c i • b i)).prod =
    (L.map c).prod • (L.map b).prod:= by
  induction L with
  | nil=> exact (one_smul ℂ _).symm
  | cons i l h=>
    simp only [List.map_cons,List.prod_cons,h, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
    rw [mul_comm _ (c i)]

lemma measured_slot (B:P.Swatch)(l r:ℝ)(d:ℝ≥0)(y:Vantage)(k:ℕ)
    (h:(B.fieldA k).allowance P a≤d)
    (u:(d:ℝ)≤y a-l)(v:(d:ℝ)≤r-y a):
    B.scoop P x a l r y k =
    P.cloaked a ξ d l r (B.Wstage x a d d k) y := by
  rw [B.precision P x a l r y k d h u v,P.cane_time]
  have he (s:ℝ)(m:0≤ s) : s.toNNReal-d=(s-d).toNNReal:= by
    rw [NNReal.sub_def, Real.coe_toNNReal s m]
  rw [he _ (d.prop.trans u),he _ (d.prop.trans v),cloaked,pad_val]

abbrev tile_read (B:P.Swatch) (F:SampleDose) (k n:ℕ):P.Test :=
  B.rate k • P.prepared n (B.fieldA k) F

variable {I:Type}(L:List I)(f g : I→ℝ)(d:I→ℝ≥0)
variable (F:I→SampleDose)(A:I→P.Swatch)

local notation "birth" σ:max=> fun i=> (A i).fieldA (σ i)
local notation "between" => P.meshPose


abbrev grid_read (σ:I→ℕ)(n:ℕ)(i:I): (G).Op :=
  silkgrid P x a (d i) (f i) (g i) (F i)
     ((A i).Wstage x a (d i) (d i) (σ i)) n

theorem appointed_grids (J:P.Ellis 3 x)(p:EuOrder L f g)
    (room:∀i∈L,Corners a (f i) (g i) (F i) (d i))
    (σ:I→ℕ)(n:ℕ)
    (w:∀i∈L,((A i).fieldA (σ i)).allowance P a<d i)
    (turn:∀p:I→Vantage,(∀i∈L,p i∈tsupport (F i).val) → P.Plenum (birth σ) L p)
    (t:∀i∈L,((A i).fieldA (σ i)).s≤n) :
    P.singleState 3 n x (L.map (fun i=>tile_read P (A i) (F i) (σ i) n)).prod =
    inner ℂ Ω ((L.map (grid_read P x a f g d F A σ n)).prod Ω):=by
  let e:= ((innerSL ℂ Ω).comp
      (ContinuousLinearMap.apply ℂ (G).space Ω : (G).Op→L[ℂ](G).space)).toLinearMap
  letI: Inhabited Cover:= ⟨0⟩
  let c (i:I):= (A i).rate (σ i)
  let b (i:I)(k:Cover):= c i • P.issuing n ((A i).fieldA (σ i)) k
  have he(i:I) : tile_read P (A i) (F i) (σ i) n =
    ∑ k∈P.usedGrid n (F i),P.activation n (F i) k • b i k := by
    rw [tile_read,prepared,Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _=>smul_comm _ _ _
  let B(i:I)(y:Vantage):= P.cloaked a ξ (d i) (f i) (g i)
     ((A i).Wstage x a (d i) (d i) (σ i)) y
  simp_rw [he]
  refine assort2 L (fun i=> P.usedGrid n (F i))
      b (fun i k=> B i (between n k))
      (fun i k=>P.activation n (F i) k) _ e (p.once L f g) fun q k=>?_
  let y : I→Vantage := between n ∘ q
  have ht : ∀i∈L,y i∈tsupport (F i).val := fun i v=> (P.usedPose ..).mp (k i v)
  have ch : P.WClassic a L A f g y σ := by
    refine ⟨fun i v=>?_,p.seams⟩
    let u:=y i a
    let β:ℝ:=((A i).fieldA (σ i)).realWidth P a
    change f i < u-β ∧ u+β < g i
    have hh : β < (d i:ℝ) := by unfold β; rw [Apron.width_real]; exact w i v
    obtain ⟨s,t⟩ : (d i:ℝ)≤ u-f i ∧ (d i:ℝ)≤g i-u := room i v _ (ht i v)
    constructor <;> linarith only [s,t,hh]
  have cr : P.Turnstile a (birth σ) L y :=
     p.order.imp_of_mem fun {i k} u v h =>
       (ch.1 i u).2.trans ((lt_of_le_of_lt h (ch.1 k v).1))
  show P.singleState 3 n x (L.map fun i=> c i • P.issuing n ((A i).fieldA (σ i)) (q i)).prod =
    e (L.map fun i=>B i (y i)).prod
  rw [scaleList]
  refine ((P.full_visit_exact x a L A J σ q n cr (turn _ ht) t).trans
    (P.raw_classical x a L A f g y σ ch).symm).trans ?_
  show e (L.map fun i=> (A i).scoop P x a (f i) (g i) (y i) (σ i)).prod = _
  refine congrArg (fun l:List (G).Op=>e l.prod) (List.map_congr_left fun i v=>?_)
  obtain ⟨h,h'⟩:= room i v _ (ht i v)
  exact measured_slot P x a (A i) _ _ (d i) _ _ (w i v).le h h'


/-- Uniform clearance across Eu ordered support. The permutation in each
axis need not be uniform (useful with general envelopes). -/
def Umbrella (ε:ℝ):Prop :=
  ∀ (p:I→Vantage), (∀i∈L,p i∈tsupport (F i).val) →
    ∀ j:Axis, ∃ K:List I, L.Perm K ∧ K.Pairwise (fun u v=>p u j+ε<p v j)

lemma continues (u:∀i,(A i).WPermit x a) {ε:ℝ}(h:0<ε)
    (ok:Umbrella L F ε)
    (room:∀i∈L,0<d i)
    {σ:ℕ→I→ℕ}(t:∀i∈L,Tendsto (fun n=>σ n i) atTop atTop):
 ∀ᶠ n in atTop,
    (∀i∈L,((A i).fieldA (σ n i)).allowance P a<d i) ∧
    ∀p:I→Vantage, (∀i∈L,p i∈tsupport (F i).val) → P.Plenum (birth (σ n)) L p:=by

  have thin :
      ∀ᶠ n in atTop, ∀i∈L.toFinset,
      ((A i).fieldA (σ n i)).allowance P a<d i ∧
      ∀j:Axis, ((A i).fieldA (σ n i)).realWidth P j<ε/2:= by
    refine L.toFinset.eventually_all.mpr fun i v=>?_
    have b:=List.mem_toFinset.mp v
    have r(j:Axis): Tendsto (fun n=> ((A i).fieldA (σ n i)).allowance P j) atTop (𝓝 0) :=
      ((u i).thin j).comp (t i b)
    refine ((r a).eventually (gt_mem_nhds (room i b))).and (eventually_all.mpr fun j=>?_)
    filter_upwards [(NNReal.tendsto_coe.mpr (r j)).eventually (gt_mem_nhds (half_pos h))] with _ h
    rwa [Apron.width_real]
  filter_upwards [thin] with n hn
  have t(i:I)(v:i∈L):=hn i (List.mem_toFinset.mpr v)
  refine ⟨fun i v=>(t i v).1, fun p hy=> ⟨fun j=> ?_⟩⟩
  obtain ⟨K,perm,e⟩:=ok p hy j
  refine ⟨K,perm,e.imp_of_mem fun {i k} b b' q=>?_⟩
  change p i j+((A i).fieldA (σ n i)).realWidth P j <
       p k j-((A k).fieldA (σ n k)).realWidth P j
  linarith only [q,(t i (perm.mem_iff.mpr b)).2 j, (t k (perm.mem_iff.mpr b')).2 j]


variable (u:∀i,(A i).WPermit x a)

abbrev silhouette (i:I): (G).Op :=
   P.flounce a ξ (d i) (f i) (g i) ((u i).atHeat (d i)) (F i)
   
lemma grid_reaped {σ:ℕ→I→ℕ}{m:ℕ→ℕ}(z:Tendsto m atTop atTop)
    (t:∀i∈L,Tendsto (fun n=>σ n i) atTop atTop)
    (room:∀i∈L,0<d i):
    Tendsto (fun n=>(L.map (grid_read P x a f g d F A (σ n) (m n))).prod Ω) atTop
        (𝓝 ((L.map (silhouette P x a f g d F A u)).prod Ω)):=by
  induction L with
  | nil=> exact tendsto_const_nhds
  | cons i L ih=>
    have p:= ((u i).arriving _ (room i List.mem_cons_self))
    have c:= flight_variants G p (t i List.mem_cons_self)
    exact silkgrid_follows P x a (d i) (f i) (g i) (F i) _ _ c z
       (ih (fun j k=>t j (List.Mem.tail _ k)) (fun j k=>room j (List.Mem.tail _ k)))


/-- The late-width phrase. Common elected refinements `m n` affording the
entire grid; tests and their support clearances fixed, Width **not** replaced
by mesh size. Positive d's counted inside wall cuts. -/
theorem mirrorball (J:P.Ellis 3 x)(p:EuOrder L f g)
    (room:∀i∈L,0<d i ∧ Corners a (f i) (g i) (F i) (d i))
    {ε:ℝ}(h:0<ε)(w:Umbrella L F ε)
    {σ:ℕ→I→ℕ}(t:∀i∈L,Tendsto (fun n=>σ n i) atTop atTop)
    {m:ℕ→ℕ}(z:Tendsto m atTop atTop)
    (s:∀ᶠ n in atTop,∀i∈L, ((A i).fieldA (σ n i)).s ≤ m n):
    Tendsto (fun n=> P.singleState 3 (m n) x (L.map (fun i=>
      tile_read P (A i) (F i) (σ n i) (m n))).prod) atTop
        (𝓝 (inner ℂ Ω ((L.map (silhouette P x a f g d F A u)).prod Ω))):=by
  have b(i:I)(c:i∈L):=(room i c).1
  refine (tendsto_const_nhds.inner (grid_reaped P x a L f g d F A u z t b)).congr' ?_
  filter_upwards [continues P x a L d F A u h w b t,s] with n hn v
  exact (appointed_grids P x a L f g d F A J p (fun i c=>(room i c).2) _ _ hn.1 hn.2 v).symm
end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

