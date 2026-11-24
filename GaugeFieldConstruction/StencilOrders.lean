import GaugeFieldConstruction.AcrossCities
/-! # Metering helper for multiple-volume program. Uses BornTape notation for *joint* paths only; cost through ANY BornTape. Incomparable shifts on other tapes, see calendar for main qualifications. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Reconstruction Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open _root_.YM.OS.Ground TopologicalSpace
namespace Spine
open Six
open Tapestry.Fashion Tapestry.Altitude Tapestry.Exhibition PhaseChoice Reconstruction
open Set AcrossLands Heat
variable (P:Spine)
inductive BornTape : (ℕ→ℕ)→ (ℕ→ℕ)→ Prop where
  | main : BornTape (fun i=> P.diagonalᵢ (2*i)) (fun i=> P.diagonalₖ (2*i))
  | outer (f:ℕ→ℕ)(h:∀ᶠ i in atTop,legacy P.run (P.period i) (P.circuitDepth (P.period i) (f i))) : BornTape P.period (fun i=> P.circuitDepth (P.period i) (f i))
section
variable {P} (R:P.Register) {v:ℕ→ℝ}{n':ℕ}{δ : ℕ→ℝ}{x:P.Spectrum0 3}{c:P.Poll 3}(X:P.Selects R 3 x c)
variable (E:IntervalsSchedule P n' v δ) {I K:ℕ→ℕ}
open Heat
abbrev doubleCutSt :Filter (ℕ×ℕ):= (atTop:Filter ℕ).bind (fun n=> (atTop:Filter ℕ).map ((n,·)))
@[simp] theorem each_order_st {p:ℕ×ℕ→Prop} : (∀ᶠ x in doubleCutSt,p x) ↔ ∀ᶠ i in atTop,∀ᶠ r in atTop,p (i,r):=by rw [doubleCutSt,eventually_bind]; simp only [eventually_map]
instance : NeBot doubleCutSt:= by constructor; intro h; have p : ∀ᶠ x in doubleCutSt, False:= h.symm ▸ eventually_bot; obtain ⟨i,h⟩:= (each_order_st.1 p).exists; exact h.exists.choose_spec
noncomputable abbrev menuCurrencySt (P:Spine) (q:P.Poll 3)(v:ℕ→ℝ)(I K:ℕ→ℕ)(t:ℕ)(L:List (MeterQueryVU P))(d:ℕ×ℕ):ℂ:= P.panelCost v (I d.2) (K d.2) (TopCurrencyVU P t L++PollavuVU P 3 q d.1) / P.panelCost v (I d.2) (K d.2) (PollavuVU P 3 q d.1)
include E X
lemma launchMarketSt (h:BornTape P I K){L:List (MeterQueryVU P)} {t:ℕ}(g:P.EndTapeSt t L) : ∀ ε,0<ε→∀ᶠ d in doubleCutSt,P.MarketwithSt R v (x:=x) (c:=c) d.1 (I d.2) (K d.2) t L ε:=by
 intro ε hε; rw [each_order_st]; cases h with
 | main => exact (P.tapeTapeSt R v E X g ε hε).mono (fun i v=> v.1)
 | outer f h => exact (P.tapeTapeSt R v E X g ε hε).mono (fun i v=> (v.2.and h).mono (fun r μ => μ.1 _ μ.2))
lemma launchSinglePriceSt (h:BornTape P I K){L:List (MeterQueryVU P)} {t:ℕ}(g:P.EndTapeSt t L): Tendsto (menuCurrencySt P c v I K t L) doubleCutSt (𝓝 (P.singleState 3 t x ((L.map Prod.fst).prod))):=by
 refine Metric.tendsto_nhds.mpr (fun ε p=>?_); exact (launchMarketSt R X E h g ε p).mono (fun i p=> p.cost)
lemma launchSoloSt (h:BornTape P I K){t:ℕ}(A:P.Test){Y:Set Vantage}(p: P.asked_at t A Y∧ A∈ enclave P.calibration)(y:IsCompact Y) : P.EndTapeSt t [(A,Y)]∧ Tendsto (menuCurrencySt P c v I K t [(A,Y)]) doubleCutSt (𝓝 (P.singleState 3 t x A)):=by
 have hz:P.EndTapeSt t [(A,Y)]:= ⟨⟨(by simpa only [List.forall_mem_singleton] using p),by simp⟩,by simpa only [List.forall_mem_singleton] using y⟩
 exact ⟨hz, (by simpa only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] using launchSinglePriceSt R X E h hz)⟩
lemma launchDuetSt (h:BornTape P I K){t:ℕ}(A B:P.Test){Y Z:Set Vantage} (p:P.asked_at t A Y∧ A∈ enclave P.calibration)(q:P.asked_at t B Z∧ B∈ enclave P.calibration)(y:IsCompact Y)(z:IsCompact Z)(u:Disjoint Y Z) : P.EndTapeSt t [(A,Y),(B,Z)]∧Tendsto (menuCurrencySt P c v I K t [(A,Y),(B,Z)]) doubleCutSt (𝓝 (P.singleState 3 t x (A*B))):=by
 have hz:P.EndTapeSt t [(A,Y),(B,Z)]:= ⟨⟨List.forall_mem_cons.mpr ⟨p,List.forall_mem_singleton.mpr q⟩, List.pairwise_cons.mpr ⟨List.forall_mem_singleton.mpr u,List.pairwise_singleton ..⟩⟩,List.forall_mem_cons.mpr ⟨y,List.forall_mem_singleton.mpr z⟩⟩
 exact ⟨hz,(by simpa only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] using launchSinglePriceSt R X E h hz)⟩
#print axioms launchSinglePriceSt
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
