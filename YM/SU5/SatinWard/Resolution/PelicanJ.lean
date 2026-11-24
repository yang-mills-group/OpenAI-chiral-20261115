import YM.SU5.SatinWard.Resolution.LaputaGate
import YM.SU5.SatinWard.Resolution.ArcHorn
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


local notation "Tκ" v:max=> (↑(psScale P ρ v):ℂ)
local notation "Θκ" x:max=> pricedPSE P M i x p ρ
-- estimate use norm raw.cost base at some level, all widths, not v-dependent estimator later. keep for any fixed s.P. later temper.
-- uniform all n near claim. use metric stamp
local notation "Fξ" x:max=> heyC P q p i x ρ
variable (ht7:f0 ≤ s)
local instance (priority:=high) iPelicanJColorHil(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ColorHil i x).Op:=opRn (P.ColorHil i x)
local instance (priority:=high) iPelicanJManyF(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ManyF i x).Op:=opRn (P.ManyF i x)
local notation "ℓ" v:max=> moonClock P v
local notation "p☾" => sprintCost P.par.R.L
local notation "F☾"=>complect P M i x p ρ
local notation "ζ" v:max=> (↑(Tμ v):ℂ)
open _root_.YM.SatinRegistration.LimeWave
open Imperial Lighthouse
open _root_.YM.SatinWFixed Andesite Carton
local notation "P★"=> P.seasons i x
local notation "v0"=> P.advocate 3 t₃ 3 -- fix t undecl
local notation "Jℓ"=> priceX P pHw e
local notation "H☆" i:max x:max ρ:max => Gaian P q p M i x ρ pHw e K -- may need fix order
local notation "F◇" i:max x:max ρ:max => milky P q p M i x ρ pHw e K
local notation "ℓζει" => moonClock P
variable (x₃:P.Spectrum0 3)
local notation "χ₃"=> P.advocate 3 x₃ 3
local notation "V₀"=> P.heaven 3 χ₃
local notation "S'"=> P.seasons 3 χ₃
local notation "𝔤" => Gaian P q p M 3 χ₃ W.tally pHw e K
local notation "𝔬" => milky P q p M 3 χ₃ W.tally pHw e K
local notation "B"=> galaxy P q p M pHw W e K x₃
open _root_.YM.Boundary Probe _root_.YM.SatinRegistration
local notation "Qν" => pricedPSE P M 3 χ₃ p W.tally
local notation "κμ" z:max => priceX P pHw e mu q M K p 3 χ₃ z
include W pHw e K p
lemma shineSun (s:ℝ≥0)(u:0<s)(k:Molars): (B).bar s (herald k 1)=(𝔤) k s s:=by
 rw [show (B).bar s (herald k 1)=(1:ℂ) • (𝔤) k s s from ?_,one_smul]; exact at_herald 𝔤 k s u _
lemma shineK (s:ℝ≥0)(u:0<s): (B).bar s omegaCorner= Qν s s:= shineSun P q p M pHw W e K x₃ _ u none
lemma shineJ (s:ℝ≥0)(u:0<s): (B).bar s (choral mu z)= (κμ z) s s:=by
 unfold choral; rw [map_sum]; simp_rw [map_smul]; let h:= contoBill P pHw e mu q M K p 3 χ₃ W (show (0:ℝ)<s from u) (show (0:ℝ)<s from u)
 have hP (k:Wage3): (↑(z k):ℂ) • (B).bar s (trueCorner mu k)= h (z k • ShapeLab.leg k):=by rw [show (B).bar s (trueCorner mu k)= h (ShapeLab.leg k) from shineSun P q p M pHw W e K x₃ _ u (some (mu,k)), Complex.coe_smul,map_smul]
 simp_rw[hP]; rw [←map_sum, show ∑ k: Wage3,z k • ShapeLab.leg k=z from ?_]; · rfl
 funext i; rw [Finset.sum_apply,sum_eq_single i] <;> simp_all [ShapeLab.leg] -- tune
local notation "D"=> radial (P.seasons 3 χ₃)
local notation "T"=> bands (P.seasons 3 χ₃)
lemma signatureK : (B).operator omegaCorner= field S' _ (Post.soundQ (face_K P q p M 3 χ₃ W.tally pHw K)) (Post.payQ (face_K P q p M 3 χ₃ W.tally pHw K)):= brochure _ _ omegaCorner (face_K P q p M 3 χ₃ W.tally pHw K) (shineK P q p M pHw W e K x₃)
lemma signatureJ : (B).operator (choral mu z)= field S' _ (Post.soundQ (face_J P q p M z 3 χ₃ mu pHw W e K)) (Post.payQ (face_J P q p M z 3 χ₃ mu pHw W e K)):= brochure _ _ _ (face_J P q p M z 3 χ₃ mu pHw W e K) (shineJ P q p M z mu pHw W e K x₃) -- arg order x₃ after
lemma approachW {X:ℕ→ radial S'} {x:radial S'}(L:MarkWords Dialect)(pX:(bands S').Approaches atTop X x): (bands S').Approaches atTop (fun i=> (L.map (letterW («ℓ»:=moonClock P) S' 𝔬 i)).prod (X i)) ((B).realWork L x):= wordsOf S' 𝔤 𝔬 (posts P q p M 3 χ₃ W.tally pHw W e K) V₀ _ _ _ pX L
#print axioms approachW
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
