import YM.SU5.SatinWard.Resolution.Array
import Velour.Crepe.Aperture
import YM.SU5.SatinWard.Resolution.Belfry
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
local notation "R"=> Option Tilted.Ramp
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "K"=> P.run
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
local notation "Q" => P.calibration.ℓ
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "N" => Z∘F
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
-- COLOR mark earned on all boot positions, still untaxed pad clearance. upper bare bound at s=v.
local notation "A✲" i:max=> P.reachLeaf s i w
variable (k:P.NightCop) (j:Axis) (x:P.Spectrum0 j)
omit WX W pZ h
variable (m:Coords Wage4)(a0:payable P v 2)
noncomputable abbrev doorV : P.Physical j:= P.door j v (P.reachLeaf s v w) (P.reach_w v e.vivid) (cardWave P none p e a0 j m) (arcStencil P none p e a0 j (Set.mem_range_self m))
noncomputable abbrev mineV : (P.ColorHil j x).Op:= P.colorSpace j x (doorV P p e j m a0)
lemma mineValue (Z: (P.ColorHil j x).Op) : P.ThreadOp j x v (P.reachLeaf s v w) (τEnd P v (P.clockPlate s v p) m a0) Z ↔ Z=mineV P p e j x m a0:=by
 have h : P.ThreadOp j x v (P.reachLeaf s v w) (τEnd P v (P.clockPlate s v p) m a0) (mineV P p e j x m a0):= ⟨cardWave P none p e a0 j m,P.reach_w v e.vivid, _,rfl,rfl⟩; exact ⟨fun p=> p.unique h,fun p=> p.symm ▸ h⟩

variable (u:f0 ≤ g) (Q₀:Almanac P (g+1) w p)
local notation "v₀"=>g+1
include k pZ W WX u Q₀
lemma gotShape (p':payable P (g+1) 2) : ‖frameWave P none p Q₀ p' j (plusE b)‖ ≤ Real.exp 1:=by
 let Q':= P.reachLeaf (g+1) (g+1) w; let s:=g+1; let M':=(alloy P s s p); let S:= cardWave P none p Q₀ p' j (plusE b); have e': P.clockPlate (g+1) (g+1) p = nodeC p:=by simp [clockPlate]
 let x:= cast_credit P none p (g+1) (g+1) p' (plusE b)
 apply Presidential.boardPrice K V P.law (g+1) P.projection j Q' (fun _=> atlas P none (g+1) (g+1) p (plusE b)) M' (Z∘F) (pZ.comp WX.visits.tendsto_atTop) _ (Real.exp_pos 1) (P.reach_w _ Q₀.vivid) 0 k (P.fitsOrigin (fun i=>atlasPav P p Q₀ i (g+1))) rfl _ _ S x
 unfold Settle; filter_upwards [ WX.earned, (pZ.comp WX.visits.tendsto_atTop).eventually (P.history.finance (g+1))] with i H e u p₁ p₂ w' -- u list
 let K':=j▶ i; let k':=k▶ i; let B:=glowMark K K' (g+1) (glazeKey b); let o:=P.rootAt (g+1) K' p
 let A:SeatsPriced 0 P.run (g+1) K' k' (g+1) B 1:= H.entry b
 let A':=swingGlows (i:=K') (g:=g+1) K (if b then 1 else 0) (if b then 0 else 1); let ht:= gapLayer K 0 A A' V w 0 o le_rfl zero_lt_one (?_) Q₀.budget (atlas P none (g+1) (g+1) p (plusE b)) (?_) u p₁ p₂ (?_)
 · simpa only [owedP,mul_zero,zero_add,mul_one] using! ht
 · have hp:f0 ≤ g:=‹_›; rw [show (RootBook P.run K' k' (g+1)).p.B=P.thresholdF (g+1) from congrArg BudgetPoint.B (Papal.prices_plot P.run _ K' k' e.enters).1]; exact ⟨_,Q₀.stand,(node_of ..).symm⟩
 · unfold atlas keynote; rw [e',multiplier_p]; exact bumpRoot P _ _ _ _ _ (node_of ..)
 · simpa only [Q',reachLeaf,Pi.zero_apply,mul_zero] using! w'
lemma entryCost (p':payable P (g+1) 2) : ‖frameWave P none p Q₀ p' j pseV‖ ≤ 2*Real.exp 1 := by
 rw [pseV,frame_totals]; exact (norm_add_le ..).trans ((add_le_add (gotShape P p pZ W WX true k j u Q₀ p') (gotShape P p pZ W WX false k j u Q₀ p')).trans_eq (two_mul ..).symm)
lemma capEntry (p':payable P (g+1) 2): ‖mineV P p Q₀ j x pseV p'‖ ≤ 2*Real.exp 1 :=(NonUnitalStarAlgHom.norm_apply_le (P.colorSpace j x) _).trans (entryCost P p pZ W WX k j u Q₀ p')
 
omit Q₀ u
omit k WX pZ W in
private lemma pullsNorm {A:Type*}[CStarAlgebra A]{Z:Hilbert} (F:A →⋆ₐ[ℂ] Z.Op)(a b:A)(z:ℂ): ‖z • F a-F b‖ ≤ ‖z • a-b‖ := by rw [←map_smul,←map_sub]; exact NonUnitalStarAlgHom.norm_apply_le F _
include h
lemma winning (l:s<g)(hr:f0 ≤ s): let p₁:payable P g 2 := (W.stock _ (hr.trans l.le)).2; let p₂:payable P (g+1) 2:=(W.stock _ (hr.trans (h.trans (Nat.le_succ _)))).2
 ‖(↑(portGain Wq):ℂ) • mineV P p e j x pseV p₂ - mineV P p e j x pseV p₁‖≤ 4*ageBudget P η A C H s*(sprintCost P.par.R.L ^ (g-s))⁻¹:= by
 intro p₁ p₂; let a:= P.colorSpace j x; let Z:= (↑(portGain Wq):ℂ); let f:=doorV P p e j pseV p₁; let g:=doorV P p e j pseV p₂; change ‖Z • a g-a f‖ ≤ _; refine (pullsNorm (A:=P.Physical j) (Z:=P.ColorHil j x) a g f Z).trans ?_; change ‖Z • frameWave P none p e p₂ j pseV-frameWave P none p e p₁ j pseV‖ ≤ _; unfold Z; rw [Complex.coe_smul]; exact tallyFrame P p e h pZ W WX k hr j l
#print axioms winning
#print axioms capEntry
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
