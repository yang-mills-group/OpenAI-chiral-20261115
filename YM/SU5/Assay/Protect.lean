import SatinFixedContrastNovember4
import YM.SU5.Assay.Movements
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
open Aria Set OS.Semigroup Ballad Six
variable (P:Spine)(R:P.Register)(x:P.Spectrum0 3)
local notation "Zs"=>Ballad.Lead.Clan
local notation "κ"=>P.coffee 3 x
local notation "σ"=>P.rawSlot 3 x
local notation "β"=>P.base 3 x
local notation "Ω"=>P.heaven 3 x
local notation "O"=>(P.ManyF 3 x).Op
local notation "⟪" T "⟫"=> inner ℂ Ω ((T:O) Ω)
local notation "L"=>P.LagOp 3 x
variable (A : Lead.Clan → ℕ→P.Apron)(l:Lead.Clan→ℕ→P.Folio)(T:Lead.Clan→P.LagOp 3 x)
variable (B : Lead.Clan → ℕ→P.Apron)(m:Lead.Clan→ℕ→P.Folio)(U:Lead.Clan→P.LagOp 3 x)
-- PRE argument order for future
open DoseTravel TopologicalSpace
variable {P R x A B l m T U}{D N:Doorway}{s n:ℕ}{o:Orders}
variable {F G:SampleDose}{f g:ℕ→SampleDose}{i j t:ℕ→ℕ}
variable (p:P.Assay R x s n D N o F G A B l m T U)
local notation "a"=> D.lower 3
local notation "b"=> D.turnCut N
local notation "c"=> N.upper 3
local notation "R1"=>litRow 3 a b 0
local notation "R2"=>litRow 3 b c 0
/-!
 Robust receipt. Every nearby **suitable** choice works -- before old and
 new pose refinements & releases. Both host levels (old, new) may coincide
 or be priced independently. Used to test strength of readings, not by
 changing the chosen smears during convergence. `Assay` per se doesn't
 assert RawNormal data; request `LightRig`, e.g. from `RawNormal.shelf`.
-/
namespace Assay
local notation "γ"=>P.seatGrid R x
local notation "V"=>P.seatStage x (a) (b) (c)
local notation "ξ"=>P.seatPair x (a) (b) (c)
local notation "Old"=>P.arrayReading x s n (b)
local notation "New" Q:max W:max =>ξ Q W T U
local notation "prior"=>P.arrayFine x s n
local notation "test" Q:max W:max=> P.Assay R x s n D N o Q W A B l m T U
local notation "trial" Q:max W:max=>P.Audit R x A l T B m U Q W s n D N
include p
lemma protects (J:P.Ellis 3 x)(Y:P.LightRig x A)(X:P.LightRig x B) {Cost Gain:Set CrossRead}
 (y:Cost∈𝓝 (Old F G)) (z:Gain∈𝓝 (New F G)):
 ∃ e>0,∃ k≥s,∀F' G',D.Suitable F'→N.Suitable G'→AltNear e F F'→AltNear e G G'→
   (test F' G') ∧ Old F' G' ∈ Cost ∧ (∀ t≥k,prior t F' G' ∈ Cost)∧∀ i≥k,∀j≥k,(trial F' G') Gain i j:=by
 -- prove pointwise packet of data
 let Body (F' G':SampleDose)(w i j t:ℕ):Prop:= (test F' G') ∧ Old F' G'∈Cost ∧ prior w F' G'∈Cost ∧
    P.Motive s n A B i j ∧ (New F' G')∈ Gain ∧ (V F' G' A B i j)∈Gain ∧ γ F' G' A B i j t∈Gain
 suffices h:∃ e>0,∃k:ℕ,∀F' G',D.Suitable F'→N.Suitable G'→AltNear e F F'→AltNear e G G'→
    ∀ w≥k,∀ i≥k,∀j≥k,∀t≥max i j, Body F' G' w i j t by
   obtain ⟨e,n,k,w⟩:=h
   refine ⟨e,n,max k s, le_max_right ..,fun f g u v h q=>?_⟩
   have t:=w f g u v h q
   have r:=fun x (p:k≤x) => t x p k le_rfl k le_rfl _ le_rfl
   refine ⟨(r _ le_rfl).1,(r _ le_rfl).2.1,fun w h=>(r w (le_of_max_le_left h)).2.2.1,?_⟩
   rintro i u j v
   have a':=fun y h=> (t _ le_rfl i (le_of_max_le_left u) j (le_of_max_le_left v) y h).2.2.2
   obtain ⟨motive,term,stage,_⟩:=a' _ le_rfl
   exact (r _ le_rfl).1.paints motive term stage (fun t q=>(a' t q).2.2.2)
 by_contra h
 let e(n:ℕ):=(1/2:ℝ)^n
 push Not at h
 have el:=fun k=>h _ (show 0<e k from pow_pos (by norm_num) _) k
 choose f g f' g' f₀ g₀ w ŵ i î j ĵ t C bad using el
 have v:Tendsto e atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 have hf:D.Rival F f:=⟨f',⟨p.old.fixed1,p.old.oil⟩,fun _ u=>(v.eventually (gt_mem_nhds u)).mono fun k t i=>(f₀ k i).trans t⟩
 have hg:N.Rival G g:=⟨g',⟨p.old.fixed2,p.old.water⟩,fun _ u=>(v.eventually (gt_mem_nhds u)).mono fun k t i=>(g₀ k i).trans t⟩
 have hw:Tendsto w atTop atTop:=tendsto_atTop_mono ŵ tendsto_id
 have hi:Tendsto i atTop atTop:=tendsto_atTop_mono î tendsto_id
 have hj:Tendsto j atTop atTop:=tendsto_atTop_mono ĵ tendsto_id
 suffices h:∀ᶠ k in atTop, Body (f k) (g k) (w k) (i k) (j k) (t k) from
   let ⟨k,m⟩:=h.exists; bad k m
 filter_upwards [p.alter J hf hg y,(p.alterFine J hf hg hw).eventually y,p.qualifies hi hj,
    (p.roam hf hg).eventually z,(p.clasp hf hg hi hj).eventually z,(p.gather hf hg hi hj J Y X C).eventually z]
   with k a' b' c' d' e' f'
 exact ⟨a'.2,a'.1,b',c',d',e',f'⟩
end Assay
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
