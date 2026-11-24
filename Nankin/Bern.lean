import Nankin.Folio
import Nankin.AuraP
import SatinFoam
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
open VacuumSelection.Spine Py.Dyad Keeping
variable (P:VacuumSelection.Spine)(u:P.Roster)(M:Py.Rate.Pitching.Focus.Morn P.par.K)(Aα:ℝ)(H:P.Foam u M Aα)
local notation "Y"=> P.run
local notation "π" i:max => P.period (P.projection.rows i)
local notation "ζ" i:max => P.cutoff (P.projection.columns i)
local notation "K"=>P.calibration
local notation "Lx"=>P.par.R.L
-- price at P mean unselected. alongside.
def Accordance(P:VacuumSelection.Spine)(M:Py.Rate.Pitching.Focus.Morn P.par.K)(F s:ℕ)(C D:ℕ→ℝ):Prop:=Bills F (s+1) s P.par.R.L C D ∧∀ j,F ≤ j→ j ≤ s→∀ (a:Axis)(o:Cover)(b: Bool)(n:ℕ),
 let t:=amount P j; (P.calibration.ℓ:ℤ)+t ≤ nodeC o a → nodeC o a ≤ n→ let T:=invoice P s j o b C D
 ‖P.E (s+1) (mirror P.calibration a 0 T*T)‖≤wafer P M j (amount P j) n
include H
set_option maxHeartbeats 850000 in
theorem tapeE:∀ᶠ F:ℕ in atTop,∀ s:ℕ,F ≤ s→ ∃ C D, Accordance P M F s C D:=by
 have tp:=P.law.pick.grow_i.comp P.history.growsA
 filter_upwards [folle P u _ _ H] with F p s h; obtain ⟨c,d,a,C,D,T,W,l,g,z⟩:=p _ h
 refine ⟨C,D,W,fun j t e i o b n=>?_⟩
 let d₀:=amount P j
 intro x' y' h₀ B --
 obtain ⟨Z,U,z1,z2⟩:=cover_deck P e o b T (C:=C) (c:=c) (fun k h=>l k (t.trans h)) (d:=d) (D:=D) (fun k h=>g k (t.trans h))
 have hz: BQueue (reflectedBox i 0 U ∪ U) (fun i'=> mirror K i 0 (Z i') *Z i') (mirror P.calibration i 0 B * B):= (z1.revolve i 0).multiply z1
 have hc:=((hot_deck P.run P.large P.law (s+1) P.history _ _ hz).norm).comp T.tendsto_atTop
 apply le_of_tendsto hc
 let pc:= (Papal.count_grows P.run j).eventually_ge_atTop (2*(n+d₀)+addgap P.calibration)
 have pT:=refinery P s (bands (orbitB Lx o (s-j)) 22) (ridge P s j o) (lining_test ..)
 filter_upwards [T.tendsto_atTop.eventually z,T.tendsto_atTop.eventually (tp.tendsto_atTop.eventually pc),T.tendsto_atTop.eventually pT] with r t' h' p'
 let m0:=π (a r); let k0:=ζ (a r); let R:= stageA P m0 k0
 let X:Family K:= tokenA P (s:=s) (j:=j) b (c (a r)) (d (a r)) • ridge P (s+1) j o + tokenB P (s:=s) (j:=j) b • block P.run P.large s m0 k0 (bands (orbitB Lx o (s-j)) 22) (ridge P s j o)
 have hw:=pilgrim P s j m0 k0 e t'.uv (c (a r)) (d (a r)) o b p' -- arg order? #check
 change ‖hot P.run P.large (s+1) m0 k0 (mirror K i 0 (Z (a r))*Z (a r))‖≤_
 rw [show Z (a r)=X from z2 r, hot_pay P (s+1) m0 k0 t'.kick, (distribute_arith P.run P.large (s+1) m0 (mirror K i 0 X) X 0).2.1,(distribute_arith P.run P.large (s+1) m0 X 1 0).2.2.2.2 i 0, show distribute P.run P.large (s+1) m0 X=_ from hw.symm]
 exact t'.tag j n t e i o b y' h₀ h'
#check pilgrim
#print axioms tapeE
end Calico
end YM.CF.Buffered.Afterglow.Tower
