import GaugeFieldConstruction.CameraTxnVU
import GaugeFieldConstruction.OarlockTxnVU
import GaugeFieldConstruction.RamseyTurnVU
import GaugeFieldConstruction.RevelatoryVU
import GaugeFieldConstruction.CassioCurrencyVU
/-!
-/
set_option autoImplicit false
set_option maxHeartbeats 330000
set_option maxRecDepth 4000
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
variable {P: Spine}{R:P.Register}{x:P.Spectrum0 3}{i k s:ℕ}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "K"=> tent P.run P.large
local notation "N"=> side Y i (P.run.uv k)
local notation "ν"=> prior SU.group (More N)
local notation "Ω" => side P.run i s
open Six
variable {c:P.Poll 3}
variable (B:PollTrackVU x R c)
open Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open Complex
local notation "Iθ"=>P.diagonalᵢ
local notation "Kφ"=>P.diagonalₖ
local notation "Xε"=>P.singleState 3 s x
include B
abbrev ImpTrialVU (P:Spine)(s:ℕ)(f:P.Test)(i k:ℕ):Prop:= closePictureVU P i k (P.slotHole s f) ∧ widerAngleVU P s i f ∧ flashingVU P s i f
lemma impSeenVU {C:List (MeterQueryVU P)}(e:∀ u∈C,P.asked_at s u.1 u.2 ∧ u.1∈ enclave P.calibration)(q:C.Pairwise (fun a b=>Disjoint a.2 b.2))(w: Xε ((C.map Prod.fst).prod)≠0) (a)(p:a∈C)(f:a.1.val∈ CurrencyVU P.calibration):∀ᶠ r:ℕ in atTop,ImpTrialVU P s a.1 (Iθ r) (Kφ r):=by
 let ε:=‖Xε ((C.map Prod.fst).prod)‖
 obtain ⟨κ,y,h⟩:= PollTrackVU.asksVU B e q (show 0<ε from norm_pos_iff.mpr w)
 obtain ⟨i,w⟩:= h.exists; filter_upwards [w,P.pays_at (s+1),P.di_i.tendsto_atTop.eventually (flashingSeenVU (s:=s) (e a p).2 f)] with r t hp hf
 let A': MeterQueryVU P→MeterQueryVU P:=fun x=>(x.1,κ x); let C':=C.map A'; let X:= TopCurrencyVU P s C' ++ PollavuVU P 3 c i
 have hv:(C'.map Prod.fst) = C.map Prod.fst:=by unfold C'; rw[List.map_map]; rfl
 have ht:= (askVU t).1
 have hE:AskingPriceVU P r X≠0:=by
    intro H0; change dist (AskingPriceVU P r X / _) (P.singleState _ _ x (C'.map Prod.fst).prod)<ε at ht
    rw [H0,zero_div,dist_zero_left,hv] at ht; exact lt_irrefl _ ht
 have hh: closePictureVU P (Iθ r) (Kφ r) (P.slotHole s a.1):= frameSeenVU hE (MeterTranslateVU P s (A' a)) (List.mem_append.mpr (Or.inl (List.mem_map_of_mem (f:=MeterTranslateVU P s) (List.mem_map_of_mem (f:=A') p)))) -- tune
 have hu:= flashSeenVU (s:=s) hp hh; exact ⟨hh,hu,hf hu⟩
variable {C D: MeterQueryVU P} (vC:P.asked_at s C.1 C.2) (vD:P.asked_at s D.1 D.2) (uC:C.1∈enclave P.calibration)(uD:D.1∈enclave P.calibration)(fC:C.1.val∈CurrencyVU P.calibration)(fD:D.1.val∈CurrencyVU P.calibration)
include vC vD uC uD fC fD
lemma duoSeenVU(z:Disjoint C.2 D.2)(v:Xε (C.1 * D.1)- Xε C.1 * Xε D.1 ≠0):∀ᶠ r:ℕ in atTop,ImpTrialVU P s C.1 (Iθ r) (Kφ r) ∧ ImpTrialVU P s D.1 (Iθ r) (Kφ r):=by
 by_cases t:Xε (C.1* D.1)=0
 · have ht:Xε C.1* Xε D.1≠0:=fun u=> v (by rw[t,u,sub_self]); have hc:Xε _ ≠ 0:= left_ne_zero_of_mul ht; have hd:Xε D.1≠0:= right_ne_zero_of_mul ht
   apply (impSeenVU (C:=[C]) B ?_ (by simp) (by simpa using hc) C (by simp) fC).and (impSeenVU (C:=[D]) B ?_ (by simp) (by simpa using hd) D (by simp) fD) -- tune
   all_goals simp [vC,vD,uC,uD] -- tune
 let X:=[C,D]; have hz: X.Pairwise (fun a b=>Disjoint a.2 b.2):=by simpa [X] using z
 have ht:Xε ((X.map Prod.fst).prod)≠0:=by simpa [X] using t
 have hh : ∀ u∈X,P.asked_at s u.1 u.2 ∧ u.1∈ enclave P.calibration:=by simp [X, vC,vD,uC,uD] -- tune
 exact (impSeenVU B hh hz ht C (by simp[X]) fC).and (impSeenVU B hh hz ht D (by simp[X]) fD)
#print axioms duoSeenVU
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
