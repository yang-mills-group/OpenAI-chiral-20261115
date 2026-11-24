import YM.SU5.SatinWard.Resolution.Dovetail
import YM.SU5.SatinWard.Resolution.ColorVoice
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
lemma Hmu_width:(JpriceApp P q M p z mu v).realWidth P i=(kinWidth P:ℝ)*P.macroStep v:= real_cloak .. -- syntax
lemma maiden_rise : ‖PS l r‖≤ ‖rawPSE P M i x p ρ l r‖:=by unfold pricedPSE; rw [P.locate_cost]; apply P.reprise_pay
variable (hl:moonClock P v ≤l)(hr:moonClock P v≤r)
local notation "P₀"=> home P q v i
include ρ hl hr p₁
include p in
lemma autumn : Uw+P₀ ≤ l ∧ Uw-P₀ ≤r:=by
 have hw:= windMoney P ρ p₁; have ht:=abs_le.mp (home_room P p v i); constructor<;> linarith only [hw,ht,hl,hr] -- order
lemma fresh_stamp : star ((Cℓ (JV z)) l r)=φ♠ • ((Ζℓ (Ju z)) r l):=by
 have w:= autumn P q p i ρ p₁ hl hr; exact recolor (v:=v) P q i x (JV z) (Ju z) (Uw) rfl rfl (Hmu_width ..) (Hmu_width ..) (φ♠) (spunM ..) l r w.1 w.2
lemma title_stampG : star ((Cℓ (K$)) l r)= (Ζℓ (K')) r l:=by
 have hu(k:Axis):= glowM P q p (v:=v) k q₂; have he:= windowLaw P ρ p₁; have ht:= abs_le.mp (home_room P p v i); have hx := recolor (v:=v) P q i x (K$) (K') (Uf) rfl rfl (solo_width ..) (solo_width ..) 1 (show P.reflectTest i (K$).F=(1:ℂ) • _ from (by rw [one_smul,hu])) l r (by linarith only [ht,he,hl]) (by linarith only [ht,he,hr]); rwa [one_smul] at hx
omit hl hr p₁
-- avoid Groom valuation apart. Define clipped sequences for showing.Mark.Sub.With. At pts call KFor, at all including small.X.Of.Pos.
local notation "GU"=> priceX P pHw e mu
local notation "ΚΟ" i:max=> (↑(psScale P ρ i):ℂ)
noncomputable def heyC (v:ℕ)(l r:ℝ): (P.ManyF i x).Op:= if h:f0 ≤ v then (↑(psScale P ρ v):ℂ) • annoFace P i x v (home P q v) (soloV P v (ρ.date.stock v h).2 q p pseV) l r else 0
lemma hey_info (p₁:f0≤v): heyC P q p i x ρ v l r=(ΚΟ v) • (Cℓ (K$)) l r:= dif_pos p₁ -- uses M? no
include K pHw
variable (hl₀:0<l)(hr₀:0<r)
include p hl₀ hr₀
lemma hey_budget : Tendsto (fun n=> heyC P q p i x ρ n l r) atTop (𝓝 (PS l r)):=by
 let φ:=freshF P i (-(home P q f0)) x; let F:=rawPSE P M i x p ρ; have ht:= ((φ.continuous.tendsto (F l r)).comp (psePresence P pHw M K i x p ρ hl₀ hr₀)); refine ht.congr' (?_)
 filter_upwards [eventually_ge_atTop f0] with n hn; change φ (complect P M i x p ρ n l r)=_; rw [hey_info P q p i x ρ (ρ.date.stock _ hn).2 hn,cast_chime P M i x p ρ hn]; unfold φ; rw [freshCutt,P.reprise_smul,P.locate_smul,pricing_p P M i x p ρ n pseV hn]
lemma priceDuty_PSE : star (PS l r)= Px r l:=by
 have h:=hey_budget P q p M i x ρ pHw K hl₀ hr₀;
 apply tendsto_nhds_unique (h.star); let u:=hey_budget P (flipline i q) (makesColor q p i) M i x ρ pHw K hr₀ hl₀; refine u.congr' ?_; filter_upwards [(small_clock P ρ).eventually (gt_mem_nhds hl₀),(small_clock P ρ).eventually (gt_mem_nhds hr₀),eventually_ge_atTop f0] with n L R v; let t:= (ρ.date.stock n v).2; rw [hey_info P q p i x ρ t v, star_smul, Complex.star_def,Complex.conj_ofReal,title_stampG P q p i x ρ t v (le_of_lt L) (le_of_lt R),hey_info P (flipline i q) (makesColor q p i) i x ρ t v] -- star notation star ((fun...)...) actual star applies func? h.star uses fun directly; reduce.
include W e
omit ρ -- need ρ? in theorem J energy choose W.tally. color θ.J warrant H differentiability
lemma priceDuty_J : star (GU q M K p i x z l r)= φ♠ • GU (flipline i q) M K (makesColor q p i) i x z r l:=by
 let F:= (GU q M K p i x z); have h:= powerColor P pHw e mu q M K p i x z W hl₀ hr₀; let tx:= powerColor P pHw e mu _ M K (makesColor q p i) i x z W hr₀ hl₀; apply tendsto_nhds_unique h.star; refine (tx.const_smul (φ♠)).congr' ?_; filter_upwards [(small_clock P W.tally).eventually (gt_mem_nhds hl₀),(small_clock P W.tally).eventually (gt_mem_nhds hr₀),eventually_ge_atTop f0] with n L R v; exact (fresh_stamp P q p M ((v★ n) z) i x mu W.tally v (le_of_lt L) (le_of_lt R)).symm -- $smul comp star.ST
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
