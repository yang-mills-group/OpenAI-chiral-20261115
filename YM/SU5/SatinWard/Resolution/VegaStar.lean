import YM.SU5.SatinWard.Resolution.NeedleY
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
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
open SatinWard
open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
namespace Polaris
variable (pv:skit)(ℓ:ℝ)(i:Axis) (x:P.Spectrum0 i) (A B:P.LagOp i x)
local notation "Θ"=> P.seasons i x
local notation "Ω"=> P.heaven i x
local notation "HI"=> P.ManyF i x
local notation "OpW"=> (P.ManyF i x).Op
local notation "ℛ"=> P.locate i x
local notation "h♢" p:max => Harbor P i x A B p ℓ
local notation "c◇" p:max => Cruise P i x A B p ℓ
local notation "Up" b:max v:max=> P.locate i x ((b: skit) v)
local notation "GapX" p:max=> ((p:skit) true i-p false i-2*ℓ)
variable (q:(P.seasons i x).Credits 0 A)(d:(P.seasons i x).Credits 0 B) (a:0<ℓ)(f:straight i ℓ pv)
-- paid at SAME l left position, Probe=y0 shifted A. `Instant
-- B` Height input tμ independent. center to cortex.e.F. give needed $
-- Transport even at act.T.Cor$.
noncomputable abbrev orbit (l r:ℝ)(p':Vantage) := ℛ p' (A (l+p' i) (r-p' i))
noncomputable abbrev sung(p:skit)(e:Vantage):skit:=fun i=> cond i (p true) (p false+e)
variable (p': Vantage) (u:|p' i|< ℓ) (h:straight i ℓ (sung pv p'))
local notation "Out" v:max=> scepter P i x (pv true) v v B
local notation "Voy"=> sung pv p'
local notation "Pin" t:max=> orbit P i x A t t p'
-- virial.C. avoid N representation bracket gate signature. choose one.Side.Seam linear for Ward formula.
private lemma openFoot {G:Hilbert}{i:Axis}(S:OS.Semigroup G i)(v:G)(t:Immutable S v)(A B:G.Op)(l r w:ℝ)(u:0≤ w)(e:0 ≤ r): Marble.hotPair S v w (S.sand A l r) B= Marble.hotPair S v (r+w) A B:= by
 have h:=Marble.outsidePair S v w t l r 0 0 A B e le_rfl u; simpa only [add_zero,OS.Semigroup.sand,S.wax_zero,one_mul,mul_one] using h
private lemma footShip (x:P.Spectrum0 i)(pv:skit)(p':Vantage): straight i ℓ pv→ straight i ℓ (sung pv p')→ 0 ≤ GapX pv ∧ 0 ≤ pv true i-(pv false i+p' i)-2*ℓ:=by intro a b; exact ⟨sub_nonneg.mpr a.le,sub_nonneg.mpr b.le⟩
include q f a h u
theorem toval : c◇ (sung pv p') = hotPair (P.seasons i x) (P.heaven i x) (GapX pv) ((Up pv false) (orbit P i x A ℓ ℓ p')) (Out ℓ):=by
 unfold Cruise; let Q:= (sung pv p'); let l:=ℓ+p' i; let r:=ℓ-p' i; let S:=min (min l r) ℓ; let x₀:= GapX pv; let x₁:= pv true i-(pv false i+p' i)-2*ℓ
 have hx:= abs_lt.mp u; have hl:0<l:=by linarith only [hx.1]
 have hr:0<r:=by linarith only [hx.2]
 have hs:0<S:=lt_min (lt_min hl hr) a; have hℓ:S≤ℓ:= min_le_right ..; have sl:S≤l:=(min_le_left ..).trans (min_le_left l r); have sr:S≤r:=(min_le_left ..).trans (min_le_right l r)
 let z:=pv false+p'; let C:=ℛ z (A S S); have hP: (Up pv false) (Pin ℓ)= (Θ).sand C (l-S) (r-S):=by change ℛ (pv false) (ℛ p' (A l r))=_; rw [P.locate_sum, q hs hs sl sr,P.locate_sand]
 change Marble.hotPair (Θ) Ω x₁ (ℛ z (A ℓ ℓ)) (Out ℓ)=_; rw [q hs hs hℓ hℓ,P.locate_sand, hP]; let e:=footShip P ℓ i x pv p' f h; rw [openFoot (Θ) Ω (imMemo ..) C _ _ _ x₁ e.2 (sub_nonneg.mpr hℓ), openFoot (Θ) Ω (imMemo ..) C _ _ _ x₀ e.1 (sub_nonneg.mpr sr),show ℓ-S+x₁= r-S+x₀ from by unfold x₀ x₁ r; abel] -- rw q may rewrite hidden PN? adjust.
-- marginal formula for same displacement PARTNER.K invisible via Ward. Keep whisper. no glade. Use CP.Me.Contract unit. Not assuming vacuum x.Q.
omit f h
lemma potVal : Marble.whisper Ω (orbit P i x A ℓ ℓ p')= Marble.whisper Ω (A ℓ ℓ):=by unfold orbit; rw [show Marble.whisper Ω (ℛ p' (A (ℓ+p' i) (ℓ-p' i)))= Marble.whisper Ω (A (ℓ +p' i) (ℓ-p' i)) from P.cart_wash ..]; have p:= abs_lt.mp u; exact proud P ℓ i x A q _ _ (by linarith only [p]) (by linarith only [p]) a
omit q a u
noncomputable abbrev siren : (P.ManyF i x).Op→ₗ[ℂ]ℂ:=by
 let F:=(fun X:(P.ManyF i x).Op=> hotPair (Θ) Ω (GapX pv) (ℛ (pv false) X) (Out ℓ))
 exact { toFun := F, map_add' u v:=by unfold F hotPair Marble.whisper; rw [P.locate_add, add_mul,add_mul,ContinuousLinearMap.add_apply]; rw [inner_add_right], map_smul' c A:=by unfold F hotPair Marble.whisper; rw [P.locate_smul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]; exact inner_smul_right .. }
lemma sirenB (V:(P.ManyF i x).Op): (siren P pv ℓ i x B) V=hotPair (Θ) Ω (GapX pv) ((Up pv false) V) (Out ℓ):= rfl
lemma waveΩ (V:(P.ManyF i x).Op): ‖siren P pv ℓ i x B V‖ ≤ ‖V‖*‖B ℓ ℓ‖:=by
 change ‖Cruise P i x (fun _ _=> V) B pv ℓ‖ ≤ _; exact v_norm P pv ℓ i x _ B
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
