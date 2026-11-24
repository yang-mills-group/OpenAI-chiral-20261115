import Nankin.Auric
import Nankin.Cluster
import Nankin.ProdLim
import Nankin.Beige
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
open VacuumSelection.Spine Py.Dyad Keeping YM.CF.Compass
variable(P:VacuumSelection.Spine){s j:ℕ}(e:j≤ s)(o:Cover)(b:Bool)
local notation "Y"=> P.run
local notation "π" i:max => P.period (P.projection.rows i)
local notation "ζ" i:max => P.cutoff (P.projection.columns i)
local notation "K"=>P.calibration
local notation "Lx"=>P.par.R.L
abbrev tokenA(C D:ℕ→ℝ):=shareT Lx C D s (s+1) j (denom b)
abbrev tokenB:=shareS Lx s j (denom b)
-- name includes implicit s j? yes section variable not in type if def. check. avoid
variable {a:ℕ→ℕ}{c d:ℕ→ℕ→ℝ}{C D:ℕ→ℝ}
    (T:StrictMono a)(σ:∀ k,j ≤ k → k< s+1→Tendsto (fun i=>c (a i) k) atTop (𝓝 (C k)))(x:∀ k,j≤ k → k<s→ Tendsto (fun i=>d (a i) k) atTop (𝓝 (D k)))
local notation "αT"=>tokenA P (s:=s) (j:=j) b C D
local notation "βT"=>tokenB P (s:=s) (j:=j) b
noncomputable abbrev invoice (P:VacuumSelection.Spine)(s j:ℕ)(o:Cover)(b:Bool)(C D:ℕ→ℝ):Family (P.calibration):=tokenA P (s:=s) (j:=j) b C D • ridge P (s+1) j o + tokenB P (s:=s) (j:=j) b • P.refineTest s (ridge P s j o)
include e T σ x
lemma cover_deck: ∃ (B:ℕ→Family (tent P.run P.large))(w:Finset Cover),BQueue w B (invoice P s j o b C D) ∧ ∀i, B (a i)=tokenA P (s:=s) (j:=j) b (c (a i)) (d (a i)) • ridge P (s+1) j o + βT • block P.run P.large s (π (a i)) (ζ (a i)) (bands (orbitB Lx o (s-j)) 22) (ridge P s j o):=by
 let k(i:ℕ):=tokenA P (s:=s) (j:=j) b (c i) (d i)
 have h:Tendsto (k∘ a) atTop (𝓝 αT):=by
    have hz(y:ℕ)(p:j ≤ y)(u:y≤ s+1): Tendsto (fun i=>hGain (c (a i)) (s+1) y) atTop (𝓝 (hGain C (s+1) y)):= gains (s+1) y (fun z h=> σ z (p.trans h)) u
    have hr:= revenues Lx s j (x:=fun i=>c (a i)) (y:=fun i=>d (a i)) (fun i h t=>σ i h (t.trans (Nat.lt_succ_self _))) x e
    have H:= Complex.continuous_ofReal
    cases b
    · exact H.continuousAt.tendsto.comp (hz j le_rfl (e.trans (Nat.le_succ s))) -- dependent case k notation
    exact H.continuousAt.tendsto.comp ((hz s e (Nat.le_succ s)).mul (hr.const_mul (ThinGauge.boost (Xη Lx)^(s-j))))
 let n:= sprayed k αT a; have hx:=completeSpray T h
 have p(s':ℕ):∃ U:Finset Cover,BQueue U (fun (_:ℕ)=>ridge P s' j o) (ridge P s' j o):=by
    let U:= orbitB Lx o (s'-j)
    let t:=lining_test P.calibration U (P.run.meter.a s') (payday P s')
    have g:InTest P.calibration true (bands U 22) false (ridge P s' j o):= t
    obtain ⟨i,f⟩:=Journey.valuation P.run P.large g
    exact ⟨_,BQueue.stay g (add_pos_of_nonneg_of_pos (pay_nonneg (F:=ridge P s' j o) f) zero_lt_one:0< i+1) (fun m x=>(f m x).trans (le_add_of_nonneg_right zero_le_one))⟩
 obtain ⟨Z,g⟩:=p (s+1)
 have hf:BQueue Z (fun i=>n i • ridge P (s+1) j o) (αT • ridge P (s+1) j o):=polyscale g hx
 have hh:= passes P s _ (ridge P s j o) (lining_test P.calibration (orbitB Lx o (s-j)) _ _)
 have hv:=polyscale hh (show Tendsto (fun _:ℕ=>βT) atTop (𝓝 βT) from tendsto_const_nhds)
 exact ⟨_,_,polyplus hf hv, fun i=> by unfold n; rw [sprays]⟩
#check Xη
#print axioms cover_deck
end Calico
end YM.CF.Buffered.Afterglow.Tower
