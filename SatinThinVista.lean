import SatinThinCardiff
import SatinThinRoman
import YM.SU5.FiniteGaugeData.Tower.Float

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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
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
-- tobacco denote
abbrev nomadic := P.period ∘ P.projection.rows
abbrev engine := P.cutoff ∘ P.projection.columns
abbrev NightCop:= IcePath P.run P.nomadic P.engine
local notation "aK"=> P.nomadic
local notation "bK"=> P.engine
abbrev coastT (s t i:ℕ)(S:Finset Cover):= train P.run P.large s (t-s) (P.nomadic i) (P.engine i) S
abbrev freightT (s i:ℕ):= distribute P.run P.large s (P.nomadic i) -- ok
lemma stockGo : Tendsto P.nomadic atTop atTop:= P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop
lemma amount_go (s:ℕ): Tendsto (fun r=>(Journey.side P.run (P.nomadic r) s).val) atTop atTop:= (count_grows P.run s).comp P.stockGo
lemma train_paper (S:Finset Cover)(A: Family P.calibration)(h:InTest P.calibration true S false A)(p:s≤t):
    ∀ᶠ i in atTop, P.freightT t i (P.coastT s t i S A)= convoy P.run (P.nomadic i) (P.engine i) p (P.freightT s i A):=by
 induction p with
 | refl=> apply Eventually.of_forall; intro i; rw [coastT,convoy,Nat.sub_self,climbing_refl]; rfl
 | @step t p ih =>
    let S':=volumeAround Λ P.width (t-s) S; let v:=wingspan Λ P.width S'; filter_upwards [ih,P.history.finance (t+1),P.stockGo.eventually (turning P.run P.large (t+1) v)] with i e V ht
    let n:=aK i; let k:=bK i; let W':= coastT P s t i S A; change Ferry Y (t+1) n k at V; rw [show P.coastT s t.succ i S A=Tower.block P.run P.large t n k S' W' from ?_, convoy,climbing_succ _ _ p]; unfold convoy at e
    rw [← e]; exact reserved Y H t S' n k (show legalAt Y t n k from ⟨V.depth,V.enters⟩) (prepared_train Y H s S _ _ _ h) ht
    unfold W' S' coastT; rw [Nat.succ_sub p, train_step,Nat.add_sub_of_le p]; try rfl
lemma commuter (Z:Weaver) :P.freightT s i (household P.calibration Z)= Z (N s (aK i)):=by
 have he{m n:Side}(h:m=n):ship h (Z m)= Z n:=by subst m; rfl
 exact he (Journey.terrain Y H (P.run.ir (aK i)) s)
lemma plotted_cost (Q':Family P.calibration){x:ℝ}(p:pay Q' x)(i:ℕ)(X:Fields (Journey.side P.run (P.nomadic i) s)): ‖P.freightT s i Q' X‖ ≤ x:=by
 have he{m n:Side}(h:m=n)(G:Mark m)(t:∀ x', ‖G x'‖ ≤ x)(X:Fields n): ‖ship h G X‖≤ x:=by subst m; exact t X
 exact he (terrain ..) _ (p _) X
lemma subtract_cost (z:Family P.calibration)(b:ℂ)(c:Family P.calibration) : P.freightT s i (b • (z-c))= b • (P.freightT s i z-P.freightT s i c):=by
 let A:=distribute_arith Y H s (aK i); rw [freightT,(A _ z b).2.2.1]; simp only [sub_eq_add_neg,←neg_one_smul ℂ c, (A _ _ 0).1, (A _ z _).2.2.1]; rw [neg_one_smul]
-- native representative, no width-Criterion installed
abbrev tallWorth (s:ℕ):= slotFee P.par s / ((temp (F s))^2* (F s))
-- orient clover factor may double. exact A q/tau²
abbrev visitOne (s:ℕ)(X:Cover):P.Test:= ((P.tallWorth s:ℝ):ℂ) • (P.visitLedger witnessZ (loneTrip X) s)
abbrev frameOne (x:Cover):=(loneTrip x).canvasC
variable {x:Cover}{o:Site (Journey.side P.run (P.nomadic i) s)}
lemma basesT : InTest P.calibration true (frameOne x) false (P.visitOne s x).val:= InTest.smul _ ((loneTrip x).issues witnessZ (F s) W)
lemma eerieT (h: wrap (More (side P.run (P.nomadic i) s)) x=node o)(u:s≤ P.run.uv (P.engine i)) (b:ℝ):
 P.freightT s i ((b:ℂ) • (P.visitOne s x).val)= routeTip P.run (P.nomadic i) (P.engine i) b s o:=by
 let x':= F s; have p:0<x':=(Real.exp_pos _).trans_le (P.large.trans (Vale.crown ..)); rw [routeTip,freightT,(distribute_arith Y H s (aK i) _ 0 _).2.2.1]; -- underscore metavars choose
 congr 1
 rw [show (RootBook Y (aK i) (bK i) s).p.threshold=temp (F s) from (congrArg BudgetPoint.threshold (Papal.prices_plot Y s (aK i) (bK i) u).1).trans (P.run.meter.boot s).1]; rw [worthiness _ o h _ p]; change distribute Y H s (aK i) ((↑(P.tallWorth s):ℂ) • (household W _))= _; rw [(distribute_arith Y H s (aK i) _ 0 _).2.2.1, show distribute Y H s (aK i) (household W _)= _ from P.commuter _] -- infer
-- geometry of shifts. Root Wrap EXACT
abbrev clockPlate (P:Spine) (f s:ℕ)(y:Cover):Cover:= (P.par.R.L.val^(s-f)) • nodeC y
def rootAt (P:Spine)(f i:ℕ)(x:Cover): Site (side P.run i f):= wrap (side P.run i f) x
lemma high_root (p:f ≤ s)(y:Cover): node (upRoot Y i p (P.rootAt f i y))= wrap (More (N s i)) (P.clockPlate f s y):=by
 induction p with| refl=> rw [clockPlate,Nat.sub_self,pow_zero,one_smul,upRoot,climbing_refl]; exact node_of ..| step h ih=> rw [upRoot,climbing_succ _ _ h,mansion_L (Vale.apt (P.run.ir _) P.par.block L _) P.par.R.odd_side]; unfold upRoot at ih; rw [ih, Ratio.embed_wrap, clockPlate, clockPlate,Nat.succ_sub h,pow_succ',mul_smul]; try rfl
variable (X:Cover)(p:f≤r)(u:r≤v)(b z:ℝ)
-- regulator itinerary of the actor in question.
local notation "Vx" v:max=> P.visitOne v (P.clockPlate f v X)
abbrev bookT (i:ℕ)(f r v:ℕ)(b:ℝ)(X:Cover): Family P.calibration := ((↑(zoomM P.par.R.L^(r-f)):ℂ) • (((b:ℂ) • (P.visitOne v (P.clockPlate f v X)).val) - (P.coastT r v i (frameOne (P.clockPlate f r X)) (P.visitOne r (P.clockPlate f r X)).val)))
include p u in
lemma touring_fee :∀ᶠ i:ℕ in atTop,∀ b z:ℝ,P.freightT v i (P.bookT i f r v (z*b) X)= gapMark Y (aK i) (bK i) b z p u (P.rootAt f (aK i) X):=by
 filter_upwards [P.history.finance v,P.train_paper _ _ (show InTest _ true (frameOne (P.clockPlate f r X)) false (P.visitOne r (P.clockPlate f r X)).val from P.basesT) u] with i Q' I b z
 let n:= aK i; let k:= bK i; let A:= P.rootAt f (aK i) X; have ht:v≤P.run.uv k:= Q'.enters; rw [bookT,P.subtract_cost,I];
 unfold gapMark Yoke.principal extra_δ Yoke.chamber; rw [← P.eerieT (P.high_root (p.trans u) X).symm ht,← P.eerieT (P.high_root p X).symm (le_trans u ht),Complex.ofReal_mul,Complex.ofReal_one,one_smul,freightT, mul_smul,(distribute_arith Y H v (aK i) _ 0 _).2.2.1]; try rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.touring_fee
