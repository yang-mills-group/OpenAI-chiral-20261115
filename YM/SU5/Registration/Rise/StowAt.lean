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
local notation "F" s:max=>hat P.par.R.L P.par.x s
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
variable (x:P.Spectrum0 3)(g h:ℕ)
local notation "ξ"=> P.advocate 3 x j
local notation "U"=> P.ColorHil j ξ
local notation "E"=> (P.physicalEnergy j ξ).E
local notation "M" s:max j:max=> whenly (timeMesh P.par) s j
local notation "ω" => P.colorZero j ξ
local notation "H₀" f:max t:max=> P.visitOne t (P.clockPlate f t X)
local notation "P₀" f:max t:max=> P.centeredQ x t (P.clockPlate f t X)
variable (w:ℕ) (p:Plans j X f P)(c0:twiceT X j≤w)
local notation "ℓ!" f:max t:max => Z f t w
local notation "D" f:max=>6*tiltBase P.par A f
include p c0
lemma bedCase (v:ℕ) : P.InCase j v (Z f v w) (P.centeredQ x v (P.clockPlate f v X)):= InCase.except (P.bought_frame j X w p c0 v) ((InCase.units P j v _).scale _)
omit p c0 in
lemma costa {Z':P.Test}(p:P.InCase j v w Z')(u:0<w): inner ℂ ω (p.charges ξ u ω)=P.singleState 3 v x Z':=by
 let σ:= p.card; let h':= p.colorC; have e:P.voxTest j v σ.val=Z':=p.entry; let h'':= (show P.voxTest j v σ.val∈ enclave P.calibration from e.symm ▸ h')
 unfold InCase.charges; rw [p.cases_eq_door u σ e,P.attended,P.view_scalar,e]; exact P.single_agrees ..
section cents
variable (hw:0<w)
local notation "ζ" t:max=> (H₀ f t)
local notation "d!" t:max=> (P.bought_frame j X w p c0 t).charges ξ (P.calendarZ t f w hw)
local notation "b!" t:max=> (P.bedCase j X x w p c0 t).charges ξ (P.calendarZ t f w hw)
local notation "w!" => M f w
noncomputable def shave (t:ℝ≥0)(Y':(U).Op): (U).Op := Y'- inner ℂ ω (Y' ω) • (P.physicalEnergy j ξ).E t -- remove name Y' notation
include hw
lemma bed_spent (t:f≤v) : b! v=P.shave j x w! (d! v):=by
 let f₀:=P.bought_frame j X w p c0 v; let A'(y:ℂ):= (InCase.units P j v (ℓ! f v)).scale y; let y:=P.singleState 3 v x (ζ v); let V:= P.calendarZ v f w hw
 change (f₀.except (A' y)).charges ξ V=_
 rw [f₀.charges_except ξ (A' y)]; unfold A'; rw [InCase.charges_scale (InCase.units P j v _) ξ y V, InCase.charges_units]; unfold shave; rw [show M v (Z f v w)=w! from matchR (timeMesh P.par) f v w t, P.costa]
omit p c0 hw in
private lemma clean_cost' (H':Hilbert)(T R:(H').Op)(y:H')(h:‖R‖≤1)(hy:‖y‖=1) : ‖T-inner ℂ y (T y) • R‖ ≤ 2*‖T‖:= by
 refine (norm_sub_le ..).trans ?_; rw [norm_smul,two_mul]; apply add_le_add le_rfl; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) h); apply (norm_inner_le_norm ..).trans; rw [hy,one_mul]; exact (T.le_opNorm y).trans_eq (by rw [hy,mul_one]) -- annotation needed?
omit p c0 hw in
private lemma shave_toward (H':Hilbert)(A B C:(H').Op)(x:H')(z:ℂ) : (z • A-B) - inner ℂ x ((z • A-B) x) • C=z • (A-inner ℂ x (A x) • C) - (B-inner ℂ x (B x) • C):=by rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,inner_sub_right,inner_smul_right,sub_smul,←smul_smul,smul_sub]; abel
omit p c0 hw in
lemma shave_cost(t:ℝ≥0)(A:(P.ColorHil j (P.advocate 3 x j)).Op): ‖P.shave j x t A‖ ≤ 2*‖A‖:= clean_cost' U _ _ ω ((P.physicalEnergy j ξ).shrinks _) (P.norms_color ..)
variable {b:ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ}(q:lender A C f r v δ b κ P)
variable (Y₀:P.ColumnBill w f)(F₀:P.NightCop)
include q Y₀ F₀
lemma gap_center (t:f≤r)(e:r≤v) : ‖(b:ℂ) • b! v - b! r‖ ≤ 2*(6*tiltBase P.par A f/zoomM P.par.R.L^(r-f)):= by
 let x₁:= d! v; let x₀:= d! r; let Z':=(b:ℂ) • x₁-x₀; have ht:=P.shave_cost j x w! Z'; rw [show (b! v)= _ from P.bed_spent j X x w p c0 hw (t.trans e),show (b! r)= _ from P.bed_spent j X x w p c0 hw t]; rw [show ((b:ℂ) • P.shave j x w! (d! v)-P.shave j x w! (d! r))=P.shave j x w! Z' from (shave_toward U x₁ x₀ _ _ _).symm]; exact ht.trans (mul_le_mul_of_nonneg_left (P.passage_clock j X w p hw c0 q Y₀ F₀ t e ξ) zero_le_two) -- operand? ht shave definition? need explicit implicit f r
omit q
lemma raw_center (u:treasury A C P f r r) : ‖b! r‖ ≤ 4*(3*tiltBase P.par A f*fareMin (L) (r-f)):= by
 let Z':= d! r; rw [P.bed_spent j X x w p c0 hw u.price.le] -- ambiguous positivity order
 exact (P.shave_cost j x w! Z').trans ((mul_le_mul_of_nonneg_left (P.absolute_clock j X w p hw c0 u Y₀ F₀ ξ) zero_le_two).trans_eq (by ring)) -- c0 order? 
end cents
omit p c0
-- pin quote on actual pivot: heat budget & spend. Lamp address for later.
local notation "μ'" s:max=> P.macroStep s
variable (l:List Axis)
local notation "O"=>P.rowClock j g f l
local notation "N'" s:max=> (P.basePlay x g s).pivot P l
local notation "X'"=>P.rootSpace g f l
local notation "Π" s:max=> P.clockPlate f s X'
local notation "Ζ" s:max=> pivotQ (P.granule (P.megaK g s)) l
local notation "Θ" => P.rent_honors j g f l
local notation "z₀" v:max=> P.calendarZ v f O (by exact Nat.succ_pos _)
local notation "κ'"=> P.laysM
lemma stamp_plate (p:Cover)(e:Π v=(Ζ v)+P.sidesPerTick • p): P.chartAll p ((N' v).full P v)=P.centeredQ x v (Π v):= by
 let A':=P.basePlay x g v; let T':= N' v -- shadow notation rename
 have ht: (N' v).s=v:= A'.pivot_s P l; unfold Apron.full; rw [ht,Nat.sub_self,P.baseP_F,show P.conveying v 0 (P.centeredQ x v (Ζ v))=P.centeredQ x v (Ζ v) from rfl, P.chart_center,e] -- rw ht problematic pin A'.s proof reduction
-- Combine handed launch price and stamp_here from geometry. Formula includes projection via `stageG`, later.
theorem stowed (p:Cover)(t:ℝ≥0)(a:P.StampHere j (N' v) v (Z f v O) p)(e:Π v=(Ζ v)+P.sidesPerTick • p)(u:M f O≤t)(v0:f≤v):
 P.stageH j ξ (N' v) t t=P.charter j ξ (-(P.vtile v p)) (E (t-(M v ((p j).toNat))) * (P.bedCase j (P.rootSpace g f l) x (P.rowClock j g f l) Θ (Nat.le_add_right _ 1) v).charges ξ (P.calendarZ v f O (by unfold rowClock; omega)) * E (t+(M v ((p j).toNat))-(M f O))) :=by
 rw [← show M v (Z f v O)= M f O from matchR (timeMesh P.par) f v O v0] at u ⊢; exact a.cashed P j ξ (N' v) v (Z f v O) p (P.stamp_plate x g l p e).symm _ _ _ u
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.stowed
#print axioms Spine.gap_center
#print axioms Spine.raw_center
