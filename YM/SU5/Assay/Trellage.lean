import YM.SU5.Assay.RawSlot
import YM.SU5.Assay.Gallery
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Even the whole grid family for raw-normal widths is an
 operator-valued distribution (real LF tests strictly purchasing lags
 for the candidate pole). Early widths clipping as in `RawSlot`;
 not asserting calendar authority off-slice / on clipped.
-/
open TopologicalSpace
-- grid additivity (in a free module)
variable (t:ℕ){M:Type*}[AddCommMonoid M][Module ℂ M]
def dispenser (F:SampleDose)(f:Cover→M):M:= ∑i∈P.usedGrid t F,P.activation t F i • f i
lemma dispenser_box (F:SampleDose)(f:Cover→M){L:Finset Cover} (p:P.usedGrid t F ⊆ L):
 P.dispenser t F f=∑i∈L,P.activation t F i • f i:=by
 refine sum_subset p fun i _ v=>?_
 rw [P.usedPose] at v; simp only [activation,image_eq_zero_of_notMem_tsupport v,mul_zero,Complex.ofReal_zero,zero_smul]
variable {F G L:SampleDose}
lemma dispenser_add (f:Cover→M)(u v:ℝ)(e:∀y,L.val y=u*F.val y+v*G.val y):
 P.dispenser t L f=(u:ℂ) • P.dispenser t F f+(v:ℂ) • P.dispenser t G f:=by
 let z:=P.usedGrid t L∪ (P.usedGrid t F∪P.usedGrid t G)
 rw [P.dispenser_box t L f (show _ ⊆ z from Finset.subset_union_left),
   P.dispenser_box t F f (show _ ⊆ z from Finset.subset_union_left.trans Finset.subset_union_right),
   P.dispenser_box t G f (show _ ⊆ z from Finset.subset_union_right.trans Finset.subset_union_right),
   smul_sum,smul_sum,←sum_add_distrib]
 refine Finset.sum_congr rfl fun i _=>?_;rw [smul_smul,smul_smul,←add_smul]
 congr 1; unfold activation; rw [e]; push_cast;ring

local notation "σ"=>P.rawSlot j x
local notation "β"=>P.rawBase j x
local notation "ξ" => P.laid j x
lemma slot_linear (D:P.Apron)(a b u v:ℝ)(e:∀y,L.val y=u*F.val y+v*G.val y):
 σ t D a b L=u • σ t D a b F+v • σ t D a b G:=by
 rw [P.rawSlot_raze,P.rawSlot_raze,P.rawSlot_raze,←Complex.coe_smul u,←Complex.coe_smul v]
 exact P.dispenser_add t (fun i=>P.raze j x D a b (P.vtile t i)) u v e
variable {P j x}{I:Type*}{D:I→P.Apron}{Z:Row}{a b:ℝ}
lemma raw_shelf (p:∀ Q:Compacts Vantage,(Q:Set Vantage)⊆Z→ ∃C:ℝ,0≤C∧∀s,∀y∈Q,‖ξ (β (D s)) a b y‖≤C):
 SeedBook Z (fun i:I×ℕ =>σ i.2 (D i.1) a b):=by
 refine ⟨fun i f g l u v h=>P.slot_linear (F:=extract f) (G:=extract g) (L:=extract l) _ _ _ _ _ _ _ _ h,?_⟩
 intro Q u; obtain ⟨C,n,v⟩:=p Q u; obtain ⟨c,z,t⟩:=P.grain_price Q
 refine ⟨C*c,mul_nonneg n z,fun i F q M m r=>?_⟩
 refine (P.sampler_cost _ _ _ F _ (fun _ t=>v i.1 _ (q t))).trans ?_
 rw [mul_assoc,mul_comm C]; exact mul_le_mul_of_nonneg_right (t _ q _ m r _) n
-- exact LF even at fixed widths
lemma prior_shelf (a b:ℝ)(D:P.Apron)(Z:Row): SeedBook Z (fun i:Unit×ℕ=>σ i.2 D a b):=
 raw_shelf (D:=fun _:Unit=>D) (fun _ _=>⟨_,norm_nonneg _,fun _ _ _=>P.rawBase_pay ..⟩)

variable {Q:ℕ→P.Apron}{g:ℕ→P.VMark}{p:Vantage}{T:P.RawLag j x}
namespace RawNormal
variable (a b)
lemma shelf (h:P.RawNormal j x Q g p T):SeedBook (litRow j a b 0) (fun i:ℕ×ℕ=>σ i.2 (Q i.1) a b):=by
 refine raw_shelf ?_; intro K' v
 obtain ⟨r,y,t⟩:=gainRow K' v
 obtain ⟨C,n,e⟩:=(BSOT.fromNorm (h.showAt r y r y)).ceiling
 suffices ∃m:ℝ,0≤ m∧∀s:ℕ, ∀i:{y:Vantage//y∈ K'},‖ξ (β (Q s)) a b i‖≤ m from
  let ⟨m,n,z⟩:=this; ⟨_,n,fun s y t=>z s ⟨_,t⟩⟩
 refine little_book (fun s=>⟨_,fun i=>P.rawBase_pay ..⟩) ⟨C,?_⟩
 filter_upwards [e,h.fades.one y j] with s u n; intro i
 have z:=(Credits.pay₂ (P.align_credits j x (Q s) (g s)) n (t i.2).1.le (t i.2).2.le).trans u
 unfold align at z; rw [P.charter_cost] at z; exact z
local notation "κ"=>P.coffee j x
lemma mobile (h:P.RawNormal j x Q g p T)(r:P.Gridded j x)
 {l:Filter I}{s t:I→ℕ}{f:I→Crop (litRow j a b 0)}{u:Crop (litRow j a b 0)}
 (e:Tendsto f l (𝓝 u))(z:Tendsto s l atTop)(k:Tendsto t l atTop):
 P.Rehearses j x (fun i=>σ (t i) (Q (s i)) a b (extract (f i))) l (κ (P.respool j x p T) a b (extract u)):=
 (h.grid r (extract_walled u) z k).squeeze' ((h.shelf a b).vary e (fun i=>(s i,t i))) (Eventually.of_forall fun _=>le_rfl)
end RawNormal
-- at fixed widths
lemma prior_mobile (a b:ℝ)(r:P.Gridded j x)(A:P.Apron)
 {l:Filter I}{t:I→ℕ}{f:I→Crop Z}{u:Crop Z} (e:Tendsto f l (𝓝 u))(k:Tendsto t l atTop):
 P.Rehearses j x (fun i=>σ (t i) A a b (extract (f i))) l
 (P.coffee j x (P.base j x A) a b (extract u)):=
 ((P.grid_base j x r A a b (extract u)).visit k).squeeze'
     ((prior_shelf (x:=x) a b A Z).vary e (fun i=>((),t i))) (Eventually.of_forall fun _=>le_rfl)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
