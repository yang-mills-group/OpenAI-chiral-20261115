import YM.SU5.Assay.Gridded
import YM.SU5.Assay.RawNormal
import YM.SU5.Assay.Coffee
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
 Uniform comparison against a raw pole aligned in the pre-projection space,
 sampled at any refining grids (no growth constraint). Here `a b` walls,
 real and fixed. `d` may be arbitrary function → 0; need upper bound
 on norm error over SUPPORT only. Aligner independent of grids.
-/
local notation "σ"=>P.sampler j x
local notation "β"=>P.rawBase j x
local notation "μ"=>P.base j x
local notation "κ"=>P.stirred j x
local notation "q"=>P.coffee j x
local notation "φ"=>P.charter j x
local notation "L"=>P.locate j x
local notation "Ξ₀"=>P.respool j x
variable {P j x}{I:Type*}{l:Filter I}{d:I→ℝ}{g:I→P.VMark}{p:Vantage}{s t:I→ℕ}
lemma freeze_pose (r:P.Gridded j x){F:SampleDose}{u:Vantage→X}{v:I→Vantage→X}{C:ℝ}(m:0≤C)
  (h:AtPan F.val u)(w:PanC F.val u C)
  (n:Tendsto t l atTop)(z:Tendsto (P.laysM ∘ g) l (𝓝 p))(a:Tendsto d l (𝓝 0))
  (e:∀ᶠi in l,∀y∈tsupport F.val, ‖φ (g i) (v i y)-u y‖≤d i):
 P.Rehearses j x (fun i=> σ (t i) F (v i)) l (L (-p) (κ F u)):=by
 let f(i:I)(y:Vantage):= φ (g i) (v i y)
 have b:P.Rehearses j x (fun i=>σ (t i) F (f i)) l (κ F u):=
    sampler_transfers (P.sampler_rehearses j x F u r h w m) n a e
 refine (charter_rehearses (f:=fun i=>-g i) z.neg b).congr' ?_
 exact Eventually.of_forall fun i=>sampler_unwind (t:=t i) (F:=F) (v i) (g i)

variable (P j x)
-- Posing a raw pole across indicated span (without transverse addressing)
abbrev laid (T:P.RawLag j x)(a b:ℝ)(y:Vantage):X:=T (y j-a) (b-y j)
local notation "τ"=>P.laid j x
lemma laid_base (D:P.Apron)(a b:ℝ):P.stirring j x (τ (β D) a b)=P.slot j x (μ D) a b:=by
 funext y; simp only [stirring,laid,P.reprise_rawBase,slot,flown]
lemma laid_cont (D:P.Apron)(a b:ℝ)(F:SampleDose):AtPan F.val (τ (β D) a b):=by
 intro y i; have u:= (continuous_apply j).tendsto y
 exact P.rawBase_slide j x D (u.sub_const a) (tendsto_const_nhds.sub u)
lemma laid_cost (D:P.Apron)(a b:ℝ)(F:SampleDose):PanC F.val (τ (β D) a b) ‖D.engine P j x‖:=fun _ _=> P.rawBase_pay ..
variable {P j x}{F:SampleDose}{T:P.RawLag j x}{a b u:ℝ}
lemma Walled.laid (h:Walled j F a b u)(c:(U).Credits u T):
 AtPan F.val (τ T a b) ∧∃C:ℝ,0≤C∧PanC F.val (τ T a b) C:=by
 obtain ⟨d,t,v⟩:=h.more
 refine ⟨fun y k=>?_,_,norm_nonneg (T d d),fun y k=> Credits.pay₂ c t (v _ k).1.le (v _ k).2.le⟩
 have f:= (continuous_apply j).tendsto y
 exact Credits.slide c (h _ k).1 (h _ k).2 (f.sub_const a) (tendsto_const_nhds.sub f)
lemma respool_laid (h:Walled j F a b u)(m:(U).Credits u T)(v:(S).Credits u (Ξ₀ p T)):
 L (-p) (κ F (τ T a b))=q (Ξ₀ p T) a b F:=by
 obtain ⟨c,C,k,w⟩:=Walled.laid h m
 refine P.located_cup j x (-p) ?_ (P.stirring_ink j x c w) (h.brew v).booth
 intro y t
 unfold slot flown respool stirring laid
 rw [P.locate_sum,P.locate_sum,add_comm]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
