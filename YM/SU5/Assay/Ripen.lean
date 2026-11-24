import YM.SU5.Assay.Walled
import Mathlib.Analysis.Distribution.TestFunction
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
open TopologicalSpace
open scoped Distributions BoundedContinuousFunction
abbrev Row := TopologicalSpace.Opens Vantage
def litRow (j:Axis)(a b d:ℝ):Row:= ⟨{y:Vantage | d<y j-a∧d<b-y j},
 (isOpen_lt continuous_const ((continuous_apply j).sub continuous_const)).inter
 (isOpen_lt continuous_const (continuous_const.sub (continuous_apply j)))⟩
variable {j:Axis}{a b d:ℝ}{Z:Row}
abbrev Crop (Z:Row):=𝓓(Z,ℝ)
def extract (f:Crop Z): SampleDose:=⟨f,f.contDiff,f.hasCompactSupport⟩
def germinate {F: SampleDose} (h:tsupport F.val⊆ Z): Crop Z:=⟨F.val,F.smooth,F.budget,h⟩
lemma plant_ok {F:SampleDose} (h:tsupport F.val⊆ Z):extract (germinate h)=F:=rfl
lemma Walled.row {F:SampleDose} (h:Walled j F a b d):tsupport F.val⊆litRow j a b d:=fun _=>h _
lemma extract_walled (f:Crop (litRow j a b d)):Walled j (extract f) a b d:=fun _ t=> f.tsupport_subset t
lemma gainRow (K:Compacts Vantage)(h:(K:Set Vantage)⊆litRow j a b d):∃u>d,(K:Set Vantage)⊆litRow j a b u:=by
 rcases (K:Set Vantage).eq_empty_or_nonempty with v|v
 · exact ⟨_,lt_add_one d,by rw [v];exact empty_subset _⟩
 let f(i:Vantage):=min (i j-a) (b-i j)
 have t:Continuous f:= ((continuous_apply j).sub continuous_const).min (continuous_const.sub (continuous_apply j))
 obtain ⟨i,g,p⟩:= K.isCompact.exists_isMinOn v t.continuousOn
 obtain ⟨u,v,y⟩:=exists_between (show d<f i from lt_min (h g).1 (h g).2)
 exact ⟨u,v,fun k q=> lt_min_iff.mp (y.trans_le (p q))⟩
/-!
 LF pricing for real smears. Topology is the usual mathlib LF on `Crop`
 (all samples with supports clearing the open row). Price an entire discrete
 book at once in the **uniform norm**, used to vary input tests.
-/
variable {X I:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{r:I→SampleDose→X}
structure SeedBook (Z:Row)(r:I→SampleDose→X) : Prop where
 seeds : ∀ i (f g l:Crop Z) u v,(∀y,l y=u*f y+v*g y) →
    r i (extract l)=u•r i (extract f)+v•r i (extract g)
 cash : ∀ (K:Compacts Vantage), (K:Set Vantage)⊆Z → ∃C:ℝ,0≤C∧∀i (F:SampleDose), tsupport F.val ⊆ K →
   ∀M:ℝ, 0≤M→(∀y,‖F.val y‖≤M) → ‖r i F‖≤C*M
namespace SeedBook
variable (h:SeedBook Z r)
include h
local notation "D"=>Crop Z
local notation "ℂb" => Vantage →ᵇ ℝ
lemma flat (f:D) :∃C:ℝ,∀i,‖r i (extract f)‖≤C:=by
 let F:ℂb:=f
 obtain ⟨c,_,p⟩:=h.cash (⟨tsupport f,f.hasCompactSupport⟩) f.tsupport_subset
 exact ⟨_,fun i=>p i (extract f) Subset.rfl _ (norm_nonneg F) (F.norm_coe_le_norm)⟩
variable [TopologicalSpace I][DiscreteTopology I]
def shelf (f:D):I →ᵇ X :=
 BoundedContinuousFunction.ofNormedAddCommGroup (fun i=>r i (extract f)) continuous_of_discreteTopology
   _ (h.flat f).choose_spec
def desk:D→ₗ[ℝ] I →ᵇ X where
 toFun:=h.shelf
 map_add':=by
   intro f g; ext1 i
   convert h.seeds i f g (f+g) 1 1 (fun y=>by simp) using 1
   · rfl
   simp only [one_smul];rfl
 map_smul':=by
   intro c f; ext1 i
   convert h.seeds i f f (c•f) c 0 (fun y=>by simp) using 1
   · rfl
   simp only [zero_smul,add_zero];rfl
open TestFunction
lemma smooth : Continuous h.desk:=by
 rw [TestFunction.continuous_iff_continuous_comp]
 intro K u
 let L:=𝓓^{⊤}_{K}(Vantage,ℝ) -- notation
 let m:= h.desk.comp (ofSupportedInCLM ℝ (F:=ℝ) (n:=⊤) u).toLinearMap
 change Continuous m
 apply continuous_of_continuousAt_zero m
 rw [ContinuousAt,map_zero,tendsto_iff_norm_sub_tendsto_zero]
 simp only [sub_zero]
 obtain ⟨c,n,p⟩:=h.cash K u
 let φ:L →L[ℝ] ℂb:=ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ
 have t : Tendsto (fun f:L=> c*‖φ f‖) (𝓝 0) (𝓝 0):=by
   have t:=((show Continuous (fun f:L=> c*‖φ f‖) from continuous_const.mul φ.continuous.norm).tendsto 0); simp only [map_zero,norm_zero,mul_zero] at t; exact t
 refine squeeze_zero (fun f=>norm_nonneg _) ?_ t
 intro f
 refine (BoundedContinuousFunction.norm_le (mul_nonneg n (norm_nonneg _))).mpr fun i=>?_ 
 exact p i (extract (ofSupportedIn (F:=ℝ) (n:=⊤) u f)) f.tsupport_subset _ (norm_nonneg (φ f)) (φ f).norm_coe_le_norm

def admit : D→L[ℝ] I →ᵇ X:= ⟨h.desk,h.smooth⟩
lemma accepted (f:D)(i:I):h.admit f i=r i (extract f):=rfl
def per (i:I):D→L[ℝ] X :=(BoundedContinuousFunction.evalCLM ℝ i) ∘L h.admit
lemma each (f:D)(i:I):h.per i f=r i (extract f):=rfl
-- Can now vary tests regardless of index
lemma vary {J:Type*}{l:Filter J}{f:J→Crop Z}{F:Crop Z} (t:Tendsto f l (𝓝 F))(i:J→I):
 Tendsto (fun j=>‖r (i j) (extract (f j))-r (i j) (extract F)‖) l (𝓝 0):=
 squeeze_zero (fun _=>norm_nonneg _) (fun j=>(h.admit (f j)-h.admit F).norm_coe_le_norm (i j))
    (tendsto_iff_norm_sub_tendsto_zero.mp ((h.admit.continuous.tendsto _).comp t))
end SeedBook
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
