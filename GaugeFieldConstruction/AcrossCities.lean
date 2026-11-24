import GaugeFieldConstruction.AcrossPoll
import GaugeFieldConstruction.RevelatoryVU
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
open Reconstruction Set
-- Guide typo in AcrossLands:P Plateau means common beta application here, not an externally certified Plateau path.
variable {P:Spine}
local notation "Y" => P.run
local notation "RΛ" => P.large
local notation "Λ" => P.par
section
variable {R:P.Register} {δ : ℕ→ℝ} {n :ℕ} (P) (v:ℕ→ℝ) {j:Axis} (E:IntervalsSchedule P n v δ)
local notation "bP" t:max m:max=> volumeInk (mesh m (Λ).R.L t) (Λ).U ((Y).meter.a t) (v t)
variable (l:BillsSumVU P){s:ℕ} {i k:ℕ}
include E
local notation "N" i:max k:max=> side Y i ((Y).uv k)
local notation "Ξ" i:max k:max=> prior SU.group (More (N i k))
structure PanelTapeSt (j k:ℕ) (l:BillsSumVU P):Prop where
 one : Integrable ((bP ((Y).uv k) ((Y).ir j)) 1) (prior SU.group (More (side Y j (P.run.uv k)))) ∧
      (∫ U, (bP (P.run.uv k) ((Y).ir j)) 1 U ∂prior SU.group (More (side Y j (P.run.uv k)))) ≠ 0
 mark : Integrable (volumeInk (mesh (P.run.ir j) P.par.R.L (P.run.uv k)) P.par.U (P.run.meter.a (P.run.uv k)) (v (P.run.uv k)) (witnessCutVU P j k l)) (prior SU.group (More (side Y j (P.run.uv k))))
 ratio : panelCost P v j k l = (∫ U, (bP (P.run.uv k) ((Y).ir j)) (witnessCutVU P j k l) U ∂(Ξ j k))/(∫ U, (bP (P.run.uv k) ((Y).ir j)) 1 U ∂(Ξ j k))

omit E
lemma panelsSt (h:TenderΘVU s i k l)(t:VolumeInk P.par.K P.par.U (P.run.meter.a (P.run.uv k)) (v (P.run.uv k)) (mesh (P.run.ir i) P.par.R.L (P.run.uv k))) : PanelTapeSt P v i k l:=by
 obtain ⟨_,_,_,_,pW⟩:= t.origin
 have hp: Envelope (witnessCutVU P i k l):= by rw [←h.comp]; exact P.prim_pay .. -- defeq
 obtain ⟨_,u,h,B,Q⟩:= t.actual _ hp
 exact ⟨⟨h,B.trans_ne pW⟩,u,Q⟩
include E
structure LettersTape (I K:ℕ→ℕ) (l:BillsSumVU P) (s:ℕ)(b:ℂ) :Prop where
 afford : ∀ᶠ t:ℕ in atTop,TenderΘVU s (I t) (K t) l ∧ PanelTapeSt P v (I t) (K t) l ∧panelCost P v (I t) (K t) l=P.torqueBare v (ΞProdVU l) (I t) (K t)
 leaders : Tendsto (fun t=> P.panelCost v (I t) (K t) l) atTop (𝓝 b)
lemma followTape (p:∀ a∈l,a.1∈PolAt Y RΛ s a.2)(c:∀ a∈l,IsCompact a.2)(d:l.Pairwise fun a b=> Disjoint a.2 b.2) {I K:ℕ→ℕ} {x:ℂ}(e:Tendsto I atTop atTop) (q:Tendsto K atTop atTop)(w:∀ᶠ i in atTop,P.shoulderTape n δ v (I i) (K i))(hu:Tendsto (fun t=> P.torqueBare v (ΞProdVU l) (I t) (K t)) atTop (𝓝 x)):
      P.LettersTape v I K l s x:=by
 have hv:∀ᶠ i in atTop,TenderΘVU s (I i) (K i) l ∧ P.PanelTapeSt v (I i) (K i) l∧panelCost P v (I i) (K i) l=P.torqueBare v (ΞProdVU l) (I i) (K i):=by
   filter_upwards [w,e.eventually (P.wide_cost p c d),((Y).uv_grows.tendsto_atTop.comp q).eventually_ge_atTop s] with r h X z₀
   let T:=X (K r) ⟨h.1.2,z₀⟩; let W:=P.independentCash v E ((Y).uv (K r)) ((Y).ir (I r)) h.1.1
   refine ⟨T,P.panelsSt v l T W,?_⟩; unfold panelCost torqueBare consultPrice; rw [← T.comp]; rfl
 exact ⟨hv,hu.congr' (hv.mono fun i p=>p.2.2.symm)⟩
variable (R)
local notation "μr" => fun r=>P.diagonalᵢ (2*r)
local notation "νr" => fun r=>P.diagonalₖ (2*r)
lemma ordinaryTape (p:∀ a∈l,a.1∈PolAt Y RΛ s a.2)(c:∀ a∈l,IsCompact a.2)(d:l.Pairwise fun a b=> Disjoint a.2 b.2):
    P.LettersTape v (fun r=> P.diagonalᵢ (2*r)) (fun r=> P.diagonalₖ (2*r)) l s (vistaTake Y RΛ (P.talks R) (ΞProdVU l)) ∧
    ∀ (f:ℕ→ℕ), (∀ᶠ i in atTop,legacy Y (P.period i) (P.circuitDepth (P.period i) (f i))) →
      P.LettersTape v P.period (fun i=> P.circuitDepth (P.period i) (f i)) l s (vistaTake Y RΛ (P.talks R) (ΞProdVU l)):=by
 have w:Tendsto (fun i:ℕ=>2*i) atTop atTop:= StrictMono.tendsto_atTop (φ:=fun i:ℕ=>2*i) (by intro _ _ h; exact Nat.mul_lt_mul_of_pos_left h (by decide))
 let D:= P.supportsRead v R E _ (inside_budget Y RΛ (PolExpoVU p)); refine ⟨P.followTape v E l p c d (P.di_i.tendsto_atTop.comp w) (P.di_k.tendsto_atTop.comp w) (P.thinPays v E) D.2,?_⟩
 intro f h; let t:=P.jointPays v E h; exact P.followTape v E l p c d P.law.pick.grow_i.tendsto_atTop t.1 t.2 (D.1.paths f h)
variable (s:ℕ)(L:List (MeterQueryVU P))
-- corollary for actual meter menus (further post-election follows full scheduling). Same $E$ & Poll witness
local notation "xf" => (L.map Prod.fst).prod
omit E
lemma slotTapeSt : ΞProdVU (TopCurrencyVU P s L)=P.slotHole s ((L.map Prod.fst).prod):=by
 induction L with
 | nil=> exact (map_one (pinhole P.Test s)).symm
 | cons a l ih=> simp only [TopCurrencyVU,List.map_cons,List.prod_cons,prod_consVU]; rw [show _=P.slotHole s ((l.map Prod.fst).prod) from ih]; exact (map_mul (pinhole P.Test s) _ _).symm
include E
abbrev GoodTapeSt (s:ℕ)(L:List (MeterQueryVU P)):= (∀ a∈L, P.asked_at s a.1 a.2 ∧ a.1∈ enclave P.calibration) ∧ L.Pairwise (fun a b=>Disjoint a.2 b.2)
structure AttemptsTape (L:List (MeterQueryVU P)) (U:MeterQueryVU P→Set Vantage) (s:ℕ):Prop where
 before_read : (∀ i∈L,U i⊆ i.2 ∧ IsCompact (U i) ∧ P.asked_at s i.1 (U i)) ∧
               GoodTapeSt P s (L.map fun a=>(a.1,U a))
 earns : P.LettersTape v (fun r=> P.diagonalᵢ (2*r)) (fun r=> P.diagonalₖ (2*r)) (TopCurrencyVU P s (L.map (fun x=>(x.1,U x)))) s (P.E s ((((L.map Prod.fst).prod)).val)) ∧
    ∀ (f:ℕ→ℕ), (∀ᶠ i in atTop,legacy Y (P.period i) (P.circuitDepth (P.period i) (f i))) →
      P.LettersTape v P.period (fun i=> P.circuitDepth (P.period i) (f i)) (TopCurrencyVU P s (L.map (fun x=>(x.1,U x)))) s (P.E s (((L.map Prod.fst).prod).val))
omit E
abbrev EndTapeSt (s:ℕ)(L:List (MeterQueryVU P)):= P.GoodTapeSt s L ∧ ∀ x∈L,IsCompact x.2
lemma qualifyTapeSt {s:ℕ} {L:List (MeterQueryVU P)} (v:P.EndTapeSt s L): let W:= TopCurrencyVU P s L; (∀ i∈W,i.1∈ PolAt Y RΛ s i.2)∧ (∀ i∈W,IsCompact i.2)∧ W.Pairwise (fun i j=> Disjoint i.2 j.2):=by
 intro W; refine ⟨?_,?_,List.pairwise_map.mpr v.1.2⟩
 · rintro j q; obtain ⟨i,X,rfl⟩:=List.mem_map.mp q; exact pin_legalVU (v.1.1 _ X).2 (v.1.1 _ X).1
 rintro j q; obtain ⟨i,X,rfl⟩:=List.mem_map.mp q; exact v.2 i X
private lemma mayCollectQSt {P:Spine} {s:ℕ}{u:P.Test}{A:Set Vantage}(a:P.asked_at s u A) : ∃ K:Set Vantage,K ⊆ A ∧ IsCompact K ∧ P.asked_at s u K:=by obtain ⟨W,l,e⟩:=a; exact ⟨P.pinFoot s W,e,(by rw[P.usual_footprint]; exact footprint_compact ..),W,l,Subset.rfl⟩ -- CameraTxnVU
include E R
lemma readingsToTapeSt {s:ℕ}{L:List (MeterQueryVU P)}(g:P.GoodTapeSt s L): ∃ U,P.AttemptsTape v L U s:=by
 choose! K t using fun i (w:i∈L)=> mayCollectQSt (show P.asked_at s _ _ from (g.1 i w).1)
 let Y':= L.map fun x=>(x.1,K x); have p : P.EndTapeSt s Y':=by
   refine ⟨⟨?_,List.pairwise_map.mpr (g.2.imp_of_mem fun a b h'=> h'.mono (t _ a).1 (t _ b).1)⟩,?_⟩
   · intro j q; obtain ⟨i,w,rfl⟩:= List.mem_map.mp q; exact ⟨(t i w).2.2,(g.1 i w).2⟩
   intro j q; obtain ⟨i,w,rfl⟩:= List.mem_map.mp q; exact (t i w).2.1
 obtain ⟨v₁,v₂,v₃⟩:=P.qualifyTapeSt p
 let W:= TopCurrencyVU P s Y'
 have hv:vistaTake Y RΛ (P.talks R) (ΞProdVU W)= P.E s (((L.map Prod.fst).prod).val):=by
    rw [P.slotTapeSt s Y',show Y'.map Prod.fst=L.map Prod.fst from List.map_map ..]; exact Exhibition.onVista Y RΛ s (P.talks R)
 exact ⟨K,⟨t,p.1⟩,hv ▸ P.ordinaryTape R v E W v₁ v₂ v₃⟩

variable {x:P.Spectrum0 3} {c:P.Poll 3} (X:P.Selects R 3 x c)
omit E
structure MarketwithSt (i r k s:ℕ) (L:List (MeterQueryVU P)) (e:ℝ) : Prop where
 title : P.pinligature (R:=R) (x:=x) (c:=c) v i r k (TopCurrencyVU P s L) e
 panel : P.PanelTapeSt v r k (PollavuVU P 3 c i) ∧ P.PanelTapeSt v r k (TopCurrencyVU P s L ++ PollavuVU P 3 c i)
 cost : dist (P.panelCost v r k (TopCurrencyVU P s L++PollavuVU P 3 c i) / P.panelCost v r k (PollavuVU P 3 c i)) (P.singleState 3 s x ((L.map Prod.fst).prod))<e
lemma pert_read_tape {s L i r k e}(u:P.pinligature (R:=R) (x:=x) (c:=c) v i r k (TopCurrencyVU P s L) e) : MarketwithSt P R v (x:=x) (c:=c) i r k s L e:=by
 refine ⟨u,⟨P.panelsSt v _ u.2.1 u.2.2.1,P.panelsSt v _ u.1 u.2.2.1⟩,?_⟩; rw [← P.oneCup R,← P.slotTapeSt]; exact u.2.2.2.2.1
include E X
lemma tapeTapeSt {s:ℕ}{L:List (MeterQueryVU P)}(h:P.EndTapeSt s L)(e:ℝ)(u:0<e): ∀ᶠ i in atTop,
   (∀ᶠ r in atTop, MarketwithSt P R v (x:=x) (c:=c) i (P.diagonalᵢ (2*r)) (P.diagonalₖ (2*r)) s L e) ∧
   (∀ᶠ r in atTop, ∀ k, legacy P.run (P.period r) (P.circuitDepth (P.period r) k) → MarketwithSt P R v (x:=x) (c:=c) i (P.period r) (P.circuitDepth (P.period r) k) s L e):=by
 obtain ⟨a,b,d⟩:=P.qualifyTapeSt h
 filter_upwards[P.intoCore v E X b a d u,P.pollingFreedom v E X b a d u] with i p q; exact ⟨p.mono fun _ t=> P.pert_read_tape R v t.1,q.mono fun _ t k e=> P.pert_read_tape R v (t _ e)⟩
structure CampaignSt (v:ℕ→ℝ) : Prop where
 before (s:ℕ)(L:List (MeterQueryVU P))(g:P.GoodTapeSt s L): ∃ U,P.AttemptsTape v L U s
 elected (s:ℕ)(L:List (MeterQueryVU P))(h:P.EndTapeSt s L)(e:ℝ)(u:0<e): ∀ᶠ i in atTop,
   (∀ᶠ r in atTop, MarketwithSt P R v (x:=x) (c:=c) i (P.diagonalᵢ (2*r)) (P.diagonalₖ (2*r)) s L e) ∧
   (∀ᶠ r in atTop, ∀ k, legacy P.run (P.period r) (P.circuitDepth (P.period r) k) → MarketwithSt P R v (x:=x) (c:=c) i (P.period r) (P.circuitDepth (P.period r) k) s L e)
lemma campaignValueSt : CampaignSt P R (x:=x) (c:=c) v:= ⟨fun _ _ q=>P.readingsToTapeSt R v E q,fun _ _ h e u=>P.tapeTapeSt R v E X h e u⟩
#print axioms campaignValueSt
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
