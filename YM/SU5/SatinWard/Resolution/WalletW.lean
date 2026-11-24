import YM.SU5.SatinWard.Resolution.Alcove
import YM.SU5.SatinWard.Resolution.Fez
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open MezzoBill
namespace Dovetail

/-! Same regulator convergence including external-lag powers before claiming WP. want uniform-li bound in v for both.T.Ages.Future. This module first finances reflection at stages used. -/
variable {v m:ℕ}(q:Cover)(p:ResidualPermit q)(M:P.par.R.L.val%16=1)(z:Soul)(i:Axis)(x:P.Spectrum0 i)(mu:Axis)
local notation "σ" v:max=> P.macroStep v
local notation "ℛ"=> P.locate i x
local notation "π"=> P.reprise i x
local notation "ℜ"=> P.charter i x
local notation "fee" i:max => home P q i
variable {s f0:ℕ}{Z:ℕ→ℕ}{C H A d c dσ:ℝ}{η:Type}[Fintype η](ρ:Piano P f0 C H A η Z) (q₂:payable P v 2)
local notation "q'"=> flipline i q
local notation "p'" => makesColor q p i
local notation "JV" u:max=> JpriceApp P q M p u mu v
local notation "Ju" u:max=> JpriceApp P (flipline i q) M (makesColor q p i) u mu v
local notation "K$"=> soloV P v q₂ q p pseV
local notation "K'"=> soloV P v q₂ (flipline i q) (makesColor q p i) pseV
local notation "φ♠"=> (↑(colorPay i mu):ℂ)
local notation "Uw"=> (kinWidth P:ℝ)*P.macroStep v
local notation "Uf"=> (choirWidth P:ℝ)*P.macroStep v
local notation "δ₀" v:max=> moonClock P v
variable (p₁:f0 ≤ v)(pHw:Tendsto Z atTop atTop)(W:HeartClock P f0 H A d c dσ P.jump128 M Z η)(e:Melodic P η A f0 Z)(K:P.NightCop)[Nonempty η]{l r:ℝ}
local notation "hℓ"=> home P q v
local notation "PS"=> pricedPSE P M i x p ρ
local notation "Px"=> pricedPSE P M i x (makesColor q p i) ρ
local notation "Tμ" v:max => psScale P ρ v
local notation "Cℓ" F:max => annoFace P i x v (home P q v) F
local notation "Ζℓ" F:max => annoFace P i x v (home P (flipline i q) v) F
local notation "v★" s:max=> trueKey P pHw e K s

/- A local property before purchasing further Lag.Compromise: for Fixed positive lower l and ANY larger
 lags, on ALL x/any such projections but also ANY corresponding pose room for that axis. Available for
 choosing the testing points/smears on this calibration once. In particular used in integrating over x.
 Doesn't yet assert polynomial growth in the lag. -/
abbrev Flyers (A:P.Apron) (X:(P.ManyF i x).Op)(a:ℝ):Prop:= ‖X‖ ≤ a
local notation "Tκ" v:max=> (↑(psScale P ρ v):ℂ)
local notation "Θκ" x:max=> pricedPSE P M i x p ρ
-- estimate use norm raw.cost base at some level, all widths, not v-dependent estimator later. keep for any fixed s.P. later temper.
noncomputable abbrev acreOf (j:Axis)(A:P.Apron):ℝ:= ‖P.meanBox j A.s (A.u j+A.u j) (P.shifts j ((A.u j:ℕ):ℤ) A.F)‖
lemma anno_rank (N:P.Apron)(v:ℕ)(q:Vantage)(l r:ℝ): ‖annoFace P i x v q N l r‖ ≤ acreOf P i N:=by unfold annoFace; rw [P.locate_cost]; exact P.base_cost ..
-- uniform all n near claim. use metric stamp
local notation "g" v:max=> polishQ P v
local notation "Fξ" x:max=> heyC P q p i x ρ
variable (ht7:f0 ≤ s)
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ColorHil i x).Op:=opRn (P.ColorHil i x)
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ManyF i x).Op:=opRn (P.ManyF i x)
include pHw K ρ ht7
lemma vintage_le : ∀ᶠ v:ℕ in atTop,∀ (x:P.Spectrum0 i)(q: Cover)(p:ResidualPermit q)(l r:ℝ),moonClock P s≤ l→ moonClock P s≤ r→
 ‖heyC P q p i x ρ v l r-pricedPSE P M i x p ρ l r‖≤1:=by
 filter_upwards [tabulatedEra P ρ ht7, eventually_gt_atTop s] with v e he x q p l r hl hr; let t':=sprintCost P.par.R.L; let o:=ht7.trans he.le; let f:=freshF P i (-home P q f0) x; let U:=complect P M i x p ρ v l r; let f':=pricedPSE P M i x p ρ; let G:= rawPSE P M i x p ρ; let V1:=polishQ P v
 rw [show heyC P q p i x ρ v l r=f U from ?_]; swap; · rw [hey_info P q p i x ρ (ρ.date.stock _ o).2 o]; unfold U; rw [cast_chime P M i x p ρ o]; unfold f; rw [freshCutt,P.reprise_smul,P.locate_smul,pricing_p P M i x p ρ v pseV o]
 let w:=8 * ageBudget P η A C H s * (t'^(v-s))⁻¹; let x' :=w* |psScale P ρ v|; have hV:1≤V1:=e.1.trans e.2.1; change ‖f U-f (G l r)‖≤_; rw [←map_sub, show f (U-G l r)= P.locate i x (-home P q f0) (P.reprise i x (U-G l r)) from rfl,P.locate_cost]; apply (P.reprise_pay ..).trans; have h:= (brush P pHw M K i x p ρ ht7 hl hr he).2; rw [dist_eq_norm] at h
 have hK:‖U-G l r‖≤ x':= h.trans_eq (by unfold x' w t'; ring) -- quant.
 refine hK.trans (le_trans (le_mul_of_one_le_left ((norm_nonneg _).trans hK) hV) ?_); let w':=e.2.2.2.1; change V1*x'≤_; refine le_trans (?_:_≤ (g v)*(2*|psScale P ρ v| *(4*ageBudget P η A C H s*(t'^(v-s))⁻¹))) w'; unfold V1 x' w; apply le_of_eq; ring -- maybe `x'` depends t' unfold order.
lemma limit_guardP: ∃ E:ℝ,0<E∧∀ (x:P.Spectrum0 i)(l r:ℝ),moonClock P s ≤ l→ moonClock P s≤ r→ ‖pricedPSE P M i x p ρ l r‖≤E:=by
 obtain ⟨v,e,pAu⟩:= ((vintage_le P M i ρ pHw K ht7).and (eventually_ge_atTop f0)).exists
 let A:= soloV P v (ρ.date.stock _ pAu).2 q p pseV; let Y:ℝ:= ‖Tκ v‖* acreOf P i A; have hy:0≤Y:=mul_nonneg (norm_nonneg _) (norm_nonneg _); refine ⟨Y+1,by positivity,fun x l r hl hr=>?_⟩
 let F:= heyC P q p i x ρ v l r; let t:= pricedPSE P M i x p ρ l r; have hF:‖F‖≤Y:=by unfold F; rw [hey_info P q p i x ρ (ρ.date.stock _ pAu).2 pAu,norm_smul]; exact mul_le_mul_of_nonneg_left (anno_rank ..) (norm_nonneg _)
 exact (show ‖t‖≤ Y+1 from (Eq.trans_le (congrArg norm (show t=F-(F-t) from by abel)) ((norm_sub_le ..).trans (add_le_add hF (e x q p l r hl hr)))))
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
