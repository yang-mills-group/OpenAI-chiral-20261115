import YM.SU5.Assay.SlotTurn
import YM.SU5.Assay.RawTransfer
import YM.SU5.Assay.Tapers
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
/-!
 Finite quadrature price comparison with owner. Strengthens point
 comparison by preserving `Tapers`, that is, comparisons in literal
 raw-slot operator norm, even before width or grid limits, whose costs
 absorb fixed exponential partner penalties in width index. Constants
 depend on test F; no claim of uniformity over test families. Here Bool
 for reversing a label (true reverses) is unrelated to chiral sectors.
-/
def walk (m:Bool)(D:P.Apron):P.Apron:=if m then D.kiss P j else D
lemma walk_width (m:Bool)(D:P.Apron)(i:Axis): (P.walk j m D).realWidth P i=D.realWidth P i:=by cases m <;> rfl
local notation "ι"=>P.walk j
local notation "μ"=>P.laid j x
local notation "σ"=>P.rawSlot j x
local notation "β"=>P.rawBase j x
lemma grid_budget (F:SampleDose):∃C:ℝ,0≤C ∧ ∀t,P.gridMass F t≤C:=by
 obtain ⟨C,h⟩:=(P.gridMass_limit F).bddAbove_range
 exact ⟨_,le_max_left 0 C,fun t=>le_trans (h (mem_range_self t)) (le_max_right 0 C)⟩
lemma walk_point (m:Bool)(A:P.Glaze)(s:ℕ)(a b:ℝ)(y:Vantage): ‖μ (β (ι m (A.apron s))) a b y‖≤‖A.tile j s‖:=by
 unfold laid; cases m
 · exact Glaze.rawBase_tile_pay ..
 show ‖β ((A.apron s).kiss ..) _ _‖≤_
 rw [P.rawBase_kiss,rawOther,norm_star]
 exact Glaze.rawBase_tile_pay ..
lemma walk_slot (m:Bool)(A:P.Glaze)(s t:ℕ)(F:SampleDose)(a b:ℝ):
 ‖σ t (ι m (A.apron s)) a b F‖≤P.gridMass F t*‖A.tile j s‖:=
 P.sampler_cost j x t F _ (fun y _=>P.walk_point j x m A s a b y)
variable {P j x}{F:SampleDose}{a b:ℝ}
namespace Reel
variable {Z:Ballad.Lead.Clan}(r:P.Reel j Z)(A:P.Glaze)(s t k:ℕ)
local notation "ζ"=>r.twist A k
local notation "ρ"=>r.dusk A k
lemma slot_delta (m:Bool)(h:Walled j F a b (((ζ).apron s).realWidth P j)):
 ‖σ t (ι m ((ζ).apron s)) a b F-σ t (ι m (A.apron s)) a b F‖≤P.gridMass F t*‖(ρ).tile j s‖:=by
 apply P.sampler_diff
 intro y v;obtain ⟨u,t⟩:=h y v; cases m
 · exact r.twist_due x A s k u.le t.le
 simp only [walk,↓reduceIte,laid,P.rawBase_kiss,rawOther,←star_sub,norm_star]
 exact r.twist_due x A s k t.le u.le
end Reel
open Glaze in
lemma rolling_slot {A:ℕ→P.Glaze}(F:SampleDose)(h:Glaze.Grows j A):
 ∃d, Inflates d∧∀a b s t m x,‖P.rawSlot j x t (ι m (serial A s)) a b F‖≤d s:=by
 obtain ⟨C,u,i⟩:=P.grid_budget F
 refine ⟨_,Inflates.product (Inflates.constant u) (Glaze.expands h),fun a b s t m x=>?_⟩
 exact (P.walk_slot ..).trans (mul_le_mul_of_nonneg_right (i t) (norm_nonneg _))
open Glaze in
lemma Reel.negligible {Z:Ballad.Lead.Clan}(r:P.Reel j Z){A:ℕ→P.Glaze}(F:SampleDose)(h:Glaze.Grows j A):
 ∃d, Tapers d∧∀{a b s} t m x,Walled j F a b ((serial (r.wrapMix A) s).realWidth P j)→
    ‖P.rawSlot j x t (ι m (serial (r.wrapMix A) s)) a b F-P.rawSlot j x t (ι m (serial A s)) a b F‖≤d s:=by
 obtain ⟨C,u,i⟩:=P.grid_budget F
 refine ⟨_,Tapers.product (Reel.faded r h) (Inflates.constant u),?_⟩
 intro a b s t m x w; rw [mul_comm]
 exact (slot_delta r (A s) s t (ply s) m w).trans (mul_le_mul_of_nonneg_right (i t) (norm_nonneg _))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
