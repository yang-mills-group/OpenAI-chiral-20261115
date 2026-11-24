import GaugeFieldConstruction.AmberOasisVU
import YM.SU5.Six.PressSmear
import YM.SU5.Six.SupportPrice
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
variable {P:Spine}{R:P.Register}{x:P.Spectrum0 3}{c:P.Poll 3}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "lᴾ"=> P.width
local notation "Iᵣ"=> P.diagonalᵢ
local notation "Kᵣ"=> P.diagonalₖ
abbrev MeterQueryVU(P:Spine):= P.Test × Set Vantage -- May use any qualifying query with declared external harness. pinFoot
noncomputable abbrev MeterTranslateVU (P:Spine)(s:ℕ)(q:MeterQueryVU P) : MeterPanelVU P :=
 (P.slotHole s q.1,q.2)

lemma pin_legalVU {s:ℕ}{V:MeterQueryVU P}(e:V.1∈enclave P.calibration)(h: P.asked_at s V.1 V.2):
    (MeterTranslateVU P s V).1∈ PolAt P.run P.large s V.2:=by
 obtain ⟨S,v,w⟩:=h
 let U:= footprint Λ lᴾ s S
 have hv: V.1 ∈ keep Λ lᴾ s P.calibration true (handstamp U) := ⟨S, v, has_footprint Λ lᴾ s S⟩
 rw [P.usual_footprint] at w
 exact (isotone Y H w) (oneSlotWell Λ P.calibration lᴾ true _ _ s
     (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr le_rfl)) hv e)

abbrev TopCurrencyVU(P:Spine)(s:ℕ)(l:List (MeterQueryVU P)):=l.map (MeterTranslateVU P s)
abbrev AskingPriceVU(P:Spine)(r:ℕ)(c:BillsSumVU P):ℂ:=
 let ν:= prior SU.group (More (side P.run (P.diagonalᵢ r) (P.diagonalDepth r)))
 (∫ x, bareAmplitude P.run (P.diagonalᵢ r) (P.diagonalₖ r) (witnessCutVU P (P.diagonalᵢ r) (P.diagonalₖ r) c) x ∂ν)/(∫ x,bareAmplitude P.run (P.diagonalᵢ r) (P.diagonalₖ r) 1 x ∂ν)

lemma askofVU {s r:ℕ}{l:BillsSumVU P}(p:TenderΘVU s (P.diagonalᵢ r) (P.diagonalₖ r) l):
 HeightOutVU P r (ΞProdVU l)= AskingPriceVU P r l:=by
 unfold HeightOutVU Reconstruction.readingAtTop; rw [p.comp]; rfl

lemma askVU {s i r:ℕ}{l:List (MeterQueryVU P)}{ε:ℝ}(p:SummitInvoiceVU (R:=R) (s:=s) (x:=x) (c:=c) i r (TopCurrencyVU P s l) ε):
    dist (AskingPriceVU P r (TopCurrencyVU P s l++PollavuVU P 3 c i)/ AskingPriceVU P r (PollavuVU P 3 c i)) (P.singleState 3 s x ((l.map Prod.fst).prod))<ε ∧
    1/2< ‖AskingPriceVU P r (PollavuVU P 3 c i)‖:=by
 have A:ΞProdVU (TopCurrencyVU P s l)=P.slotHole s ((l.map Prod.fst).prod):=by
    clear p; induction l with
    | nil=> exact (map_one (pinhole P.Test s)).symm
    | cons a l ih=>
      simp only [TopCurrencyVU,List.map_cons,List.prod_cons,prod_consVU]
      rw [show _=P.slotHole s ((l.map Prod.fst).prod) from ih]; exact (map_mul (pinhole P.Test s) _ _).symm
 rw [←askofVU p.body,←askofVU p.screen]; rw [prod_addVU,CerealEqVU]
 refine ⟨?_,p.stay⟩
 rw [← P.oneCup R]; rw [← A]; exact p.price

variable (P)(R)(x)
lemma convertVU : ∃ c:P.Poll 3, P.Selects R 3 x c ∧
  ∀ {I:Type} (L:Finset I) (S:I→ℕ)(l:I→List (MeterQueryVU P)) (ε:ℝ)(w:0<ε),
   (∀ i∈L, (∀ u∈l i, P.asked_at (S i) u.1 u.2 ∧ u.1∈enclave P.calibration ∧ IsCompact u.2) ∧ (l i).Pairwise (fun a b=>Disjoint a.2 b.2))→
   ∀ᶠ i in atTop,∀ᶠ r:ℕ in atTop,∀ j∈L, SummitInvoiceVU (R:=R) (x:=x) (s:=S j) (c:=c) i r (TopCurrencyVU P (S j) (l j)) ε:=by
 obtain ⟨c',v⟩:=P.detectorSelect R 3 x
 refine ⟨c',v,?_⟩; intro I' L S l ε w h
 have ht : ∀ j∈L,∀ᶠ i in atTop,∀ᶠ r:ℕ in atTop, SummitInvoiceVU (R:=R) (x:=x) (s:=S j) (c:=c') i r (TopCurrencyVU P (S j) (l j)) ε:= by
    intro j p; obtain ⟨u,e⟩:=h j p; apply BiPayVU v _ _ _ w
    · intro a t; obtain ⟨y,QH,rfl⟩:=List.mem_map.mp t; exact (u y QH).2.2
    · intro a t; obtain ⟨y,QH,rfl⟩:=List.mem_map.mp t; exact pin_legalVU (u y QH).2.1 (u y QH).1
    exact List.pairwise_map.mpr e
 filter_upwards [(eventually_all_finset L).mpr ht] with i h; exact (eventually_all_finset L).mpr h
#print axioms convertVU
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
