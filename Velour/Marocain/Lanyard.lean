
import Velour.Wadding.Violet
import Velour.Marocain.Trooping
import Velour.Marocain.Overhang
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
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour

variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "ℋ"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ℰ"=> P.seasons 3 ξ
local notation "C"=> Lead.Clan
variable {R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}{A:ℕ→P.Apron}{n:ℕ→ℕ}{w:C→Prism}
    {V: ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)}
    {g h : ℕ} {X : P.HandleWith x c r A n}
variable {realY : C → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)}{Z:C→C→Boundary.Distn E4}
local notation "𝓕₄"=> M4Furnish P K c r x R i₀ F U A n w V g h X realY Z
local notation "𝓑"=> P.Bobbin 3 ξ
local notation "D"=> (ℰ).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "θ"=> P.detects 3 ξ
local notation "Q"=> P.bobQuote 3 ξ
local notation "γ"=> P.ThinVelour x A c r n w
local notation "Λ"=> P.profilesZ x V w

namespace M4Furnish



def bloom (B J:𝓑):Fin 2→𝓑:=fun i=>if i=0 then B.windBack else J

theorem in_step (u:𝓕₄)(e:γ)(a b:C)(χ f:Test4):
 inner ℂ (Ω).val
    (P.troop 3 ξ (bloom (u.violet e a) (u.violet e b)) 0 0 (leaflet χ f) Ω).val=
 (∫z,χ z) * Z a b f:=by
 let p:=bloom (u.violet e a) (u.violet e b)
 obtain ⟨v,r⟩:= Filter.exists_seq_tendsto (𝓝[>] (0:ℝ))
 let d(i:ℕ):=(v i/2).toNNReal
 let l(i:ℕ): Fin 2 →ℝ≥0:=fun _=>d i
 have t:Tendsto l atTop (𝓝 0):=
   tendsto_pi_nhds.mpr fun _=>by
     have h:=((r.mono_right nhdsWithin_le_nhds).div_const 2)
     rw [zero_div] at h
     change Tendsto (fun i=>(v i/2).toNNReal) _ (𝓝 (0:ℝ≥0))
     simpa only [Real.toNNReal_zero,Function.comp_def] using (continuous_real_toNNReal.tendsto _).comp h
 have y:∀ᶠ i in atTop, openAir (l i):=(r.eventually self_mem_nhdsWithin).mono
   fun _ h _=> Real.toNNReal_pos.mpr (half_pos h)
 have w:=((P.march_second 3 ξ p t t (tendsto_const_nhds (x:=leaflet χ f))).at_one Ω).plain



 refine tendsto_nhds_unique (Filter.Tendsto.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=(Ω).val)) w)
     (Filter.Tendsto.congr' ?_ ((tendsto_const_nhds (x:=∫z,χ z)).mul ((u.real_line e a b f).comp r)))
 filter_upwards [y] with i yp
 dsimp only
 rw [P.troop_price 3 ξ p yp yp, banner_raised,
   (ℰ).reads_leaflet _ (P.crown_vac 3 ξ u.emperor) χ f]
 simp only [fleet,l,insulate_same]
 change _=
   (∫z,χ z) * ∫y,f y* inner ℂ
     (star (Q (u.violet e a).windBack (d i)) (Ω).val) ((ℰ).unit.translation y (Q (u.violet e b) (d i) (Ω).val))
 simp_rw [←Bobbin.backward _ (show 0<d i from yp 0),star_star]
 rfl
#print axioms in_step
