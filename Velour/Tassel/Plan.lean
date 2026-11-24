import Velour.Tassel.Glow
import SatinThinFusionSales
set_option autoImplicit false

set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set

open Py.Rate.LocalLimit.Papal (Weaver household meanF)
variable (P:Spine)(Z:Lead.Clan)(n:ℕ)
local notation "e₃"=> YM.basis (3:Axis)
local notation "ℓ"=> P.calibration.ℓ

variable {R:P.Register}{U:Supplier}{e v:ℝ}{c r:ℕ→ℕ}
local notation "τ"=> P.macroStep
local notation "t"=> bell (timeMesh P.par)
def SilkVelour (c r:ℕ→ℕ):Prop :=
 ∀i:ℕ, ∃b:ℕ, t (c i) b ≤ τ i ∧ P.FlickTone (r i) b (c i) (τ i)

lemma strictCadence {W:ℕ→ℕ→Prop} (p:∀ i,∀ᶠ j:ℕ in atTop,W i j):∃ n:ℕ→ℕ,StrictMono n ∧ ∀ i,W i (n i):=by
 choose h u using fun i=> eventually_atTop.1 (p i)
 let g:ℕ→ℕ := Nat.rec (h 0) (fun i v=>max (h (i+1)) (v+1))
 exact ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (h (i+1)) (g i+1)),fun i=> u i (g i) (by cases i; exact le_refl _; exact le_max_left ..)⟩


lemma silkSpan (b:ℤ): Tendsto (fun s=>t s b) atTop (𝓝 0):=by
 have h: Tendsto τ atTop (𝓝 0):= P.macroStep_zero
 have q:=h.const_mul (b:ℝ)
 rw [mul_zero] at q; exact q
/-- Re-launch with room for all P requirements, for any strict
cut schedule passing a pointwise threshold. -/
lemma silkOuting (paid:uniform P R U e v)(g:P.NightCop)(z:ℕ→ℕ):
 ∃r:ℕ→ℕ,z≤r ∧ ∃f:ℕ→ℕ,∀c:ℕ→ℕ,StrictMono c→ f≤c→ Launch P c r ∧ P.SilkVelour c r ∧
    (∀ᵐ x ∂ P.pillars 3, readyUV P c r x keyV):=by
 choose t₁ ht using fun i=> eventually_atTop.1 (P.feather paid g (P.macroStep_pos i))
 obtain ⟨r,q,l,L⟩:= Prototype.outing paid keyV keyV_positive (fun i=>max (z i) (t₁ i))
 have h(i:ℕ):∀ᶠ s:ℕ in atTop,∃b:ℕ,t s b≤τ i ∧ P.FlickTone (r i) b s (τ i):=by
    obtain ⟨b,p⟩:=(ht i (r i) ((le_max_right ..).trans (q i))).exists
    filter_upwards [p,(P.silkSpan b).eventually (ge_mem_nhds (P.macroStep_pos i))] with s p e
    exact ⟨b,e,p⟩


 choose d p using fun i=> eventually_atTop.1 (h i)
 refine ⟨r,fun i=>(le_max_left ..).trans (q i),fun i=>max (d i) (l i),fun c a b=>?_⟩
 obtain ⟨x,_,y⟩:= L c a (fun i=>(le_max_right ..).trans (b i))
 exact ⟨x,fun i=>p i _ ((le_max_left ..).trans (b i)),y⟩
/-- Add the schedule to clock_consumption. `Launch` and `readyUV`
are the only schedule-dependencies of `Experiment`. -/
lemma relaunch {c₀ r₀:ℕ→ℕ}
 (paid:uniform P R U e v)(g:P.NightCop)(z:ℕ→ℕ)
 (sold:∀ᵐ x ∂P.pillars 3,∃ J:P.Ellis 3 x, Experiment P R c₀ r₀ x J):
 ∃c r:ℕ→ℕ,z≤r ∧ P.SilkVelour c r ∧ ∀ᵐ x ∂P.pillars 3,∃ J:P.Ellis 3 x, Experiment P R c r x J:=by
 obtain ⟨r,w,d,h⟩:=P.silkOuting paid g z
 obtain ⟨c,v₁,V⟩:=strictCadence (fun i=>eventually_ge_atTop (d i))
 obtain ⟨a,b,s⟩:=h c v₁ V
 refine ⟨c,r,w,b,(sold.and s).mono fun x hx=>?_⟩
 obtain ⟨⟨J,p⟩,w⟩:=hx
 exact ⟨J,a,w,p.ground,p.realPos,p.top⟩

section
variable (c r:ℕ→ℕ)
variable (Y:ℕ→ P.Apron)
variable (x:P.Spectrum0 3)
local notation "a" => P.advocate 3 x 3
local notation "e1" i:max=> (Y i).engine P 3 a
def SoftBuy (i j:ℕ): Prop :=
 ∃ (b:ℕ) (ρ:ℝ), t (c j) b≤ (Y i).realWidth P 3 ∧
 P.FlickTone (r j) b (c j) ρ ∧ ‖(Y i).engine P 3 (P.advocate 3 x 3)‖ * ρ ≤ τ i
def VelvetHandle (n:ℕ→ℕ): Prop :=
 ∀i:ℕ,P.SoftBuy c r Y x i (n i)
lemma SoftSupported (i:ℕ)(g:P.SilkVelour c r):
 ∀ᶠ j:ℕ in atTop,P.SoftBuy c r Y x i j:=by
 have f:=P.macroStep_zero
 have h:Tendsto (fun j:ℕ=>‖e1 i‖ * τ j) atTop (𝓝 0):= by simpa only [mul_zero] using f.const_mul ‖e1 i‖
 filter_upwards [f.eventually (ge_mem_nhds ((Y i).real_width_pos P 3)),
      h.eventually (ge_mem_nhds (P.macroStep_pos i))] with j p t'
 obtain ⟨b,w,s'⟩:= g j
 exact ⟨b, τ j, w.trans p,s',t'⟩
end

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets
variable (P:Spine)(Z:Lead.Clan)(x:P.Spectrum0 3)
local notation "K" => P.calibration
local notation "T" => timeMesh P.par
local notation "ξ"=> P.advocate 3 x 3
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ξ"=> P.wealth 3 ξ
local notation "R"=> P.seasons 3 ξ
local notation "ζ" i:max=> (purePrice i:ℂ)
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "E"=> (S).E
local notation "L"=> Lead.Clan
local notation "V!"=> (∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (c r:ℕ→ℕ)(Y:ℕ→ P.Apron) (n:ℕ→ℕ)
local notation "Q" k:max j:max=> P.stitchApron k (Y j) (c (n j)) (r (n j))
local notation "w" i:max=> (Y i).realWidth P 3
local notation "e" i:max=> (Y i).engine P 3 ξ
variable {K':P.Register}{J:P.Ellis 3 x}(B:P.Experiment K' c r x J)
include B in
lemma velour_sales (gS:P.SilkVelour c r) :∃ n:ℕ→ℕ, P.HandleWith x c r Y n ∧ P.VelvetHandle c r Y x n:= by
 let A (i j:ℕ)(k:L): H:= (e i) (E ((w i).toNNReal) (P.shard x k (c j) (r j)))
 let T' (i:ℕ)(k:L): H:= ζ k • (e i) ω
 let W(i j:ℕ):= ∀ k:L,‖A i j k-T' i k‖ ≤ P.macroStep i
 have hp(i:ℕ):∀ᶠ j:ℕ in atTop, W i j:= by
    apply eventually_all.mpr; intro k
    let v:=(w i).toNNReal; have hv:0<v:= Real.toNNReal_pos.mpr ((Y i).real_width_pos P 3)
    have he: Tendsto (fun j:ℕ=> A i j k) atTop (𝓝 (T' i k)):=by
       have he:Tendsto (fun j=> A i j k) atTop (𝓝 ((e i) (ζ k • ω))):=((e i).continuous.tendsto _).comp (thin_front_shard_tendsto k B (fun _=>v) (thin_compare_dew B hv _ (Eventually.of_forall fun _=>le_refl v)))
       rw [map_smul] at he; exact he
    exact ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually (ge_mem_nhds (P.macroStep_pos i)))
 obtain ⟨n,g,q⟩:= strictCadence (fun i=> (B.launch.smaller.tendsto_atTop.eventually (eventually_ge_atTop (Y i).s)).and ((B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and ((hp i).and (P.SoftSupported c r Y x i gS))))
 exact ⟨n,⟨g,fun i=> (q i).1, fun i=>(q i).2.1, fun i=>(q i).2.2.1⟩,fun i=>(q i).2.2.2⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

