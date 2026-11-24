import ForceSatinCP4
import YM.SU5.SatinWard.Resolution.Celsius
import YM.SU5.SatinWard.Resolution.Beryllium
import Velour.Crepe.Wiggle
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
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
namespace SlopeCharge
variable (P:Spine){j:Axis}{o:VelourBoard.Cell}{w s:ℕ} (H:0<w){σ:ℕ→ℕ}(Z:Tendsto σ atTop atTop) (g:P.NightCop)
local notation "K'" => P.calibration
local notation "Y₀" => P.run
local notation "N₀" => P.par.R.L
local notation "H₁" => P.large
local notation "tθ" => hat P.par.R.L P.par.x s
variable {m:ℕ}{θ:ℝ}(rate:ℝ) {S:Finset Cover} {U:ℕ→Buffered.Family P.calibration}
 (T:P.Test)(Q:BQueue S U (T.val)) (p:VelourBoard.Parcel P.calibration w o 0 S)
variable {K:P.Register} {b C:ℝ}{t:ℕ→ℝ}{r:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
 (h:CouncilGrant P K b C t σ r β)
variable (m)
include Z
variable {T}
include g h
omit Z
lemma banking (a:0<rate)(v:rate≤1):∀ᶠ s:ℕ in atTop,∀ (σ:ℕ→ℕ), Tendsto σ atTop atTop →∀ (S:Finset Cover)(F:ℕ→Buffered.Family P.calibration)(T:P.Test)(f:ℕ→ℂ)(z:ℂ)(o:VelourBoard.Cell)(w:ℕ),
   Costed P T f F S z s m rate σ → Dapper K' o w (hat N₀ P.par.x s) → 0<w → VelourBoard.Parcel K' w o 0 S →
   ∀ (j:Axis)(y:P.Spectrum0 j), ‖P.singleState j s y T-z‖ ≤ wane (hat N₀ P.par.x s):=by
 let D':= h.purse.born ; let C':= D'.mail
 filter_upwards [ink_warm Y₀ b C m rate H₁ D'.shearPos C' a v,h.purse.tilt,h.channels,(LocalLimit.turnover P.par).eventually (Papal.roar m b),(LocalLimit.turnover P.par).eventually_gt_atTop 0] with s e u t r p σ Y' S F T f z o w B z1 z2 z3 j y
 let t':=hat N₀ P.par.x s; let A:=forceDose t'; let G':=P.singleState j s y T-z; let J:=integralTill t'; have he:0<A:=Real.rpow_pos_of_pos p _; have hδ: 0<J:=Real.rpow_pos_of_pos p _
 obtain ⟨Z,u',v'⟩:= secant he G'; let G:= fun k=> Papal.SkyTax.caramel (f k) Z (F k); let tY:=texture P T B.primitive B.slope Z
 let V:P.Test:=1+ Z • (T+(-z) • 1)
 have g':∀ᶠ k:ℕ in atTop, InkTag P.run m rate s (ΦWork P (σ k)) (ζWork P (σ k)) H₁ S (G k):=by filter_upwards [B.inks,Y'.eventually (P.history.finance s)] with i a uo; exact e _ _ uo.enters uo.depth (u _ _ uo.depth uo.enters) (t _ _ uo.enters) _ _ _ a Z u'
 have hz: ‖1+Z*G'‖ ≤ Real.exp (2*J):=by
    have hx:P.singleState j s y V=1+Z*G':=by unfold V G';rw [map_add,map_smul,map_add,map_smul,smul_eq_mul,smul_eq_mul,P.single_state,P.reading_unit,map_one,mul_one]; rfl
    rw [← hx,P.single_state]; exact (NonUnitalStarAlgHom.norm_apply_le ..).trans (dusting P z2 Y' g rate V tY z3 g' z1 j) -- argument elaboration
 rw [v',←Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)] at hz
 have hy: 6*J≤1:=r.2.2.2.1
 have hh: |Real.exp (2*J)-1| ≤ 2*(2*J):=by simpa only [abs_of_nonneg (show 0≤ 2*J by positivity)] using Real.abs_exp_sub_one_le (x:=2*J) (by rw [abs_of_nonneg (show 0≤2*J by positivity)]; linarith)
 apply le_of_mul_le_mul_left _ he; change A*‖G'‖≤A*wane t'; linarith only [hz,hδ,(abs_le.mp hh).2,show 12*J≤ A * wane t' from r.2.2.2.2]
end SlopeCharge
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
