import YM.SU5.Registration.Rise.FarAnchor
import YM.SU5.Registration.Rise.LatestSlots
import YM.SU5.Registration.Rise.AbsoluteTilt
import YM.SU5.Registration.Rise.PadTransfer
import SatinThinBank
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
open Worth Pays CF.BProof

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)

/-! # Compare the OPERATOR on any character (including the elected one). Money
spent at an earlier resolution, stamp comes from much finer and price is on
that ACTUAL basePlay (or any reflected pivot). Keep both ends. -/
variable (y x:P.Spectrum0 3)(g h:ℕ)
local notation "ξ"=> P.advocate 3 x j
local notation "E"=> (P.physicalEnergy j ξ).E
local notation "M" s:max j:max=> whenly (timeMesh P.par) s j
local notation "ω" => P.colorZero j ξ
local notation "H₀" f:max t:max=> P.visitOne t (P.clockPlate f t X)
local notation "P₀" f:max t:max=> P.centeredQ y t (P.clockPlate f t X)
variable (w:ℕ) (p:Plans j X f P)(c0:twiceT X j≤w)
local notation "ℓ!" f:max t:max => Z f t w
local notation "D" f:max=>6*tiltBase P.par A f
section cents
variable (hw:0<w)
local notation "ζ" t:max=> (H₀ f t)
local notation "d!" t:max=> (P.bought_frame j X w p c0 t).charges ξ (P.calendarZ t f w hw)
local notation "b!" t:max=> (P.bedCase j X y w p c0 t).charges ξ (P.calendarZ t f w hw)
local notation "w!" => M f w
-- Center once (y), then **all prices** any x. Uses actual `singleState` at center & genuine enrollment, not a guess that centering retains uniform analyt. Bound center constant by same paid Box via character y. Wages apply to whole word's common space operators (using P.seasons later for projected price). Source adaptation from `StowAt.lean`.
local notation "Y₁" => P.advocate 3 y j
local notation "Ω'" => P.colorZero j Y₁
local notation "b₀" t:max=> (P.bought_frame j X w p c0 t).charges (P.advocate 3 y j) (P.calendarZ t f w hw)
include hw
lemma detent_spent (t:f≤v) : b! v=(d! v)-inner ℂ Ω' ((b₀ v) Ω') • E w!:=by
 let f₀:=P.bought_frame j X w p c0 v; let A'(α:ℂ):= (InCase.units P j v (ℓ! f v)).scale α; let y₀:=P.singleState 3 v y (ζ v); let V:= P.calendarZ v f w hw
 change (f₀.except (A' y₀)).charges ξ V=_
 rw [f₀.charges_except ξ (A' y₀)]; unfold A'; rw [InCase.charges_scale (InCase.units P j v _) ξ y₀ V, InCase.charges_units]; rw [show M v (Z f v w)=w! from matchR (timeMesh P.par) f v w t, P.costa]
omit hw in
private lemma peel_alt {H' B:Hilbert}(T C':H'.Op)(R:B.Op)(ε:ℝ)(F:B)(p:‖T‖≤ε)(v:‖C'‖≤1)(e:‖R‖ ≤ ε)(w:‖F‖=1) : ‖T-inner ℂ F (R F) • C'‖≤ 2*ε:=by
 have h:‖inner ℂ F (R F)‖ ≤ ε:=by
    have u:=(R.le_opNorm F); rw [w,mul_one] at u; exact (norm_inner_le_norm ..).trans ((congrArg (· * _ ) w).trans_le ((one_mul _).trans_le (u.trans e)))
 exact (norm_sub_le ..).trans (le_trans (add_le_add p (((norm_smul ..).le).trans ((mul_le_of_le_one_right (norm_nonneg _) v).trans h))) (two_mul _).ge) -- pipe misuse
omit hw in
private lemma peel_minus {H' B:Hilbert}(T U:H'.Op)(V V':B.Op)(F:B)(G:H'.Op)(z:ℂ): z • (T-inner ℂ F (V F) • G) - (U-inner ℂ F (V' F) • G)=(z • T-U)-inner ℂ F ((z • V-V') F) • G:=by rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,inner_sub_right,inner_smul_right,sub_smul,←smul_smul,smul_sub]; abel
omit hw in
private lemma peel_pair {H' B:Hilbert}(T U V U':H'.Op)(C₀ C₁:B.Op)(R:H'.Op)(b:B)(z:ℂ)(ε:ℝ)(h:‖z • V-U'‖ ≤ ε)(e:‖z • C₀-C₁‖ ≤ ε)(v:T=V-inner ℂ b (C₀ b) • R)(t:U=U'-inner ℂ b (C₁ b) • R)(x:‖R‖≤1)(u:‖b‖=1): ‖z • T-U‖≤2*ε:= by
 rw [v,t,peel_minus]
 exact peel_alt _ _ _ _ _ h x e u
variable {b:ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ}(q:lender A C f r v δ b κ P)
variable (Y₀:P.ColumnBill w f)(F₀:P.NightCop)
include q Y₀ F₀
lemma gap_detent (t:f≤r)(e:r≤v) : ‖(b:ℂ) • b! v - b! r‖ ≤ 2*(6*tiltBase P.par A f/zoomM P.par.R.L^(r-f)):= by
 exact peel_pair (b! v) (b! r) _ _ _ _ _ _ _ _ (P.passage_clock j X w p hw c0 q Y₀ F₀ t e ξ) (P.passage_clock j X w p hw c0 q Y₀ F₀ t e Y₁) (P.detent_spent j X y x w p c0 hw (t.trans e)) (P.detent_spent j X y x w p c0 hw t) ((P.physicalEnergy j ξ).shrinks _) (P.norms_color ..)

omit q
lemma raw_detent (u:treasury A C P f r r) : ‖b! r‖ ≤ 4*(3*tiltBase P.par A f*fareMin (L) (r-f)):= by
 rw [P.detent_spent j X y x w p c0 hw u.price.le]
 exact (peel_alt _ _ _ _ _ (P.absolute_clock j X w p hw c0 u Y₀ F₀ ξ) ((P.physicalEnergy j ξ).shrinks _) (P.absolute_clock j X w p hw c0 u Y₀ F₀ Y₁) (P.norms_color ..)).trans_eq (by ring)
end cents
-- pin quote on actual pivot: heat budget & spend. Lamp address for later.
local notation "μ'" s:max=> P.macroStep s
variable (l:List Axis)
local notation "O"=>P.rowClock j g f l
local notation "N'" s:max=> (P.basePlay y g s).pivot P l
local notation "X'"=>P.rootSpace g f l
local notation "Π" s:max=> P.clockPlate f s X'
local notation "Ζ" s:max=> pivotQ (P.granule (P.megaK g s)) l
local notation "Θ" => P.rent_honors j g f l
local notation "z₀" v:max=> P.calendarZ v f O (by exact Nat.succ_pos _)
local notation "κ'"=> P.laysM
theorem footprint_paid (p:Cover)(t:ℝ≥0)(a:P.StampHere j (N' v) v (Z f v O) p)(e:Π v=(Ζ v)+P.sidesPerTick • p)(u:M f O≤t)(v0:f≤v):
 P.stageH j ξ (N' v) t t=P.charter j ξ (-(P.vtile v p)) (E (t-(M v ((p j).toNat))) * (P.bedCase j (P.rootSpace g f l) y (P.rowClock j g f l) Θ (Nat.le_add_right _ 1) v).charges ξ (P.calendarZ v f O (by unfold rowClock; omega)) * E (t+(M v ((p j).toNat))-(M f O))) :=by
 rw [← show M v (Z f v O)= M f O from matchR (timeMesh P.par) f v O v0] at u ⊢; exact a.cashed P j ξ (N' v) v (Z f v O) p (P.stamp_plate y g l p e).symm _ _ _ u
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms footprint_paid
#print axioms gap_detent
#print axioms raw_detent
#check @footprint_paid
