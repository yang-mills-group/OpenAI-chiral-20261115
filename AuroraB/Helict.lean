import AuroraB.Liquidity
import AuroraB.Ramus
import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
open _root_.Yoland Py.Rate.Pitching.Focus PledgeT MiterT Aloft DoseTravel Calico
open _root_.YM.Preen
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "Θ" s:max z:max=>offer_update P d C D s B z
local notation "aZ" s:max t:max i:max A:max=> schema B i d C D s t (score i) A
local notation "ϕ"=>P.reflectTest 3
local notation "μ" t:max=>P.singleState 3 t x
local notation "Fz" s:max i:max A:max=> works B i d C D s (score i) A
local notation "vY" i:max A:max=> beauty d C D (x:=x) (score i) A
variable (V G':SampleDose)
local notation "L"=> flipDose V 3
/-- pricing.P compositions -/
noncomputable abbrev wet (s t:ℕ)(X:P.Test →ₗ[ℂ] ℂ): CrossRead:= Matrix.of fun Z W:Lead.Clan=> X (ϕ (aZ s t Z (L))*aZ s t W G')
noncomputable abbrev grime (s:ℕ) :CrossRead:= Matrix.of (fun i j:Lead.Clan=>inner ℂ (Fz s i (L)) (Fz s j G'))
noncomputable abbrev forge :CrossRead:= Matrix.of (fun i j:Lead.Clan=>inner ℂ (vY i (L)) (vY j G'))
local notation "τ"=>P.calibration
variable (X:ℕ→P.Test→ₗ[ℂ]ℂ)(p:∀t,Comparison P.calibration (P.singleState 3 t x) (X t))
local notation "𝒳" t:max=> X t
#check @wet
#check @grime
local notation "Χ" s:max t:max v:max=> wet B d C D V G' s t v
structure Cash (s t:ℕ):Prop where
 split(i j:Lead.Clan): X t (ϕ (aZ s t i (L))*aZ s t j G')=0
 zeroLeft(i:Lead.Clan): X t (ϕ (aZ s t i (L)))=0
 zeroRight(i:Lead.Clan): X t (aZ s t i G')=0
abbrev wide (s t:ℕ):Prop:= s ≤ t∧ ∀i:Lead.Clan, Θ s i ≤ t
lemma looms (s:ℕ):∀ᶠ t:ℕ in atTop,wide B d C D s t := (eventually_ge_atTop _).and (eventually_all.mpr fun _=>eventually_ge_atTop _)
-- Reading.Transcribed. Centered with comparator already.
variable (j:ℕ)(h:PA (P:=P) d j (flipDose V 3))(v:PA (P:=P) d j G')
include h v
lemma wide_hosp(A:SampleDose)(h:PA (P:=P) d j A):@hosp A:=fun t p=> lt_of_le_of_lt ((show (1:ℝ)≤ (core:ℝ)+1 from le_add_of_nonneg_left (by positivity)).trans (le_max_left ..)) (h t p) -- need omit v h
-- aggregated upper. comparator.S.Is.Matoms.
include p
lemma coinHeart (s t:ℕ)(w:wide B d C D s t)(q:4*Hemlock.radius P d s ≤1): Cash B d C D V G' X s t:=by
 let a:=wide_hosp d V G' j h v (L) h -- C & D parameters? omit
 have g:=wide_hosp d V G' j h v G' v
 let b(i k:Lead.Clan):=avoids B i d C D k (L) G' s t X p a g q (w.2 _) (w.2 _) (score i) (score k)
 exact ⟨fun i j=>(b i j).1, fun i=>(b i i).2.2, fun i=>(b i i).2.1⟩
omit p
structure Thalo(s:ℕ): Prop where
 joint : Tendsto (fun t=>Χ s t (μ t)) atTop (𝓝 (grime B d C D V G' s))
 leaf(i:Lead.Clan) : Tendsto (fun t=> (μ t) (ϕ (aZ s t i (L)))) atTop (𝓝 (inner ℂ (Fz s i (L)) (Ω)))
 flow(i:Lead.Clan) : Tendsto (fun t=> (μ t) (aZ s t i G')) atTop (𝓝 (inner ℂ (Ω) (Fz s i G')))
lemma dataT(s:ℕ)(q:tidal P d s <1):Thalo B d C D V G' s:=by
 have p:=wide_hosp (P:=P) d V G' j h v G' v; have f:=wide_hosp (P:=P) d V G' j h v (L) h
 constructor
 · refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> ?_; exact fine_time B i d C D s (score i) (L) G' q j (score j) f p -- check argument order
 · intro i; have ht:= (fine_h B i d C D s (score i) (L) q f).star
   simp_rw [← P.opposed_single] at ht; rw [show star (inner ℂ (Ω) (Fz s i (L)))=inner ℂ (Fz s i (L)) (Ω) from inner_conj_symm _ _] at ht; exact ht
 exact fun i=>fine_h B i d C D s (score i) G' q p
variable(M:Morn P.par.K)(hM:∀i:ℕ,d ≤ i → Accordance P M d i (C i) (D i))(hq:RobeRoad P d C D x)
omit h v in
lemma vital(Y:SampleDose)(q:Y.Normalized)(r:PA (P:=P) d j Y)(i:Lead.Clan) (M:Morn P.par.K)(hM:∀i:ℕ,d ≤ i → Accordance P M d i (C i) (D i))(hq:RobeRoad P d C D x) : Tendsto (fun s=>Fz s i Y) atTop (𝓝 (vY i Y)):= precious B i d C D M hM hq _ Y q (fun k t=> lt_of_le_of_lt ((add_le_add_left (show (score i:ℝ) ≤ core from (by exact_mod_cast (scoring i).2)) _).trans (le_max_left ..)) (r k t))
include hM hq
lemma width_current (h0:V.Normalized)(h1:G'.Normalized): Tendsto (fun s=>grime B d C D V G' s) atTop (𝓝 (forge (P:=P) d C D (x:=x) V G')) ∧ (∀i,Tendsto (fun s=>inner ℂ (Fz s i (L)) (Ω)) atTop (𝓝 0))∧ ∀i,Tendsto (fun s=>inner ℂ (Ω) (Fz s i G')) atTop (𝓝 0):=by
 have hf(i:Lead.Clan):= vital B d C D j (L) (flipPay V h0 3) h i M hM hq
 have hg(i:Lead.Clan):= vital B d C D j G' h1 v i M hM hq
 refine ⟨?_,?_,?_⟩
 · refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> ?_; exact (hf i).inner (hg j)
 · intro i; exact bye₁ (R:=H) (Ω) false _ _ (hf i) (pretty_mean x d C D (score i) (scoring i).1 (L)).2
 intro i; exact bye₁ (R:=H) (Ω) true _ _ (hg i) (pretty_mean x d C D (score i) (scoring i).1 G').2
where bye₁{R:Hilbert}(x:R)(b:Bool)(f:ℕ→R)(y:R)(h:Tendsto f atTop (𝓝 y))(p:inner ℂ x y=0): Tendsto (fun s=> if b then inner ℂ x (f s) else inner ℂ (f s) x) atTop (𝓝 0):=by
        have he:inner ℂ y x=0:=by rw [← inner_conj_symm (𝕜:=ℂ) y x,p,map_zero]
        cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> first|simpa only [p] using (tendsto_const_nhds (x:=x)).inner (𝕜:=ℂ) h|simpa only [he] using h.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=x))
#print axioms coinHeart
#check @fine_time
#check @pretty_mean
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
