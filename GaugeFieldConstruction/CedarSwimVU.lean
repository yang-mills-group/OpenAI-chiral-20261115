import YM.SU5.MacroSix.Purchase
import GaugeFieldConstruction.Trajectory
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
variable {P : Spine} {s i k : ℕ}
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "H" => P.large
local notation "N" => side P.run i (Y.uv k)
local notation "F" => atCutoff P.run P.large i k

section
-- finite panel list: support in RSpace
abbrev MeterPanelVU (P:Spine) := P.Effect × Set RSpace
abbrev BillsSumVU (P:Spine) := List (MeterPanelVU P)

def sumΘVU {P:Spine} : BillsSumVU P → Set RSpace
| [] => ∅
| a::l => a.2 ∪ sumΘVU l

def ΞProdVU (X:BillsSumVU P):P.Effect := (X.map Prod.fst).prod
@[simp] lemma prod_consVU (a:MeterPanelVU P) (X): ΞProdVU (a::X)=a.1*ΞProdVU X:=by simp [ΞProdVU]
lemma prod_addVU (X X':BillsSumVU P): ΞProdVU (X++X')=ΞProdVU X*ΞProdVU X':=by simp [ΞProdVU]

lemma singleIncVU {l:BillsSumVU P}{a:MeterPanelVU P}(p:a∈l): a.2⊆sumΘVU l:=by
 induction l with
 | nil=> simp at p
 | cons b l ih=>
   rcases List.mem_cons.mp p with q|q; subst a; exact Set.subset_union_left; exact Set.Subset.trans (ih q) Set.subset_union_right
lemma cumulus_compactVU(l:BillsSumVU P) (X:∀ a∈l, IsCompact a.2): IsCompact (sumΘVU l):=by
 induction l with
 | nil=>exact isCompact_empty
 | cons b l ih=> exact (X _ (by simp)).union (ih fun z p=> X z (List.mem_cons_of_mem b p))
lemma PolExpoVU {l : BillsSumVU P}(p:∀ a∈l,a.1∈PolAt Y H s a.2): ΞProdVU l∈ PolAt Y H s (sumΘVU l):=by
 induction l with
 | nil=> exact one_mem _ -- test
 | cons a l ih=>
   have t:=ih (fun i h=> p _ (List.mem_cons_of_mem a h))
   rw [prod_consVU]; exact Subalgebra.mul_mem _ ((isotone Y H Set.subset_union_left) (p a (by simp))) ((isotone Y H Set.subset_union_right) t)

lemma diagOneSumVU (P:Spine)(i k:ℕ):atCutoff P.run P.large i k 1 = 1:=by
 unfold atCutoff breathing; rw[Decking.crown1]; rfl
lemma shelterResVU {a:MeterPanelVU P} {l:BillsSumVU P} (w:∀ i∈l, Disjoint a.2 i.2): Disjoint a.2 (sumΘVU l):=by
 induction l with
 | nil=> exact disjoint_bot_right
 | cons b l ih=>
    have h:= w b (by simp); have t:=ih (fun i m=>w i (List.mem_cons_of_mem b m)); exact Set.disjoint_union_right.mpr ⟨h,t⟩
lemma atCutoffFullVU (l:BillsSumVU P)(u:∀ a∈l, a.1∈PolAt Y H s a.2)
    (d:l.Pairwise (fun a b=> Disjoint a.2 b.2))
    (h: Pay Y s i k){C:ℝ}(v:GrowsPast Y i C)(y:sumΘVU l ⊆ cabin C):
    F (ΞProdVU l)= (l.map (fun p => F p.1)).prod:=by
 induction l with
 | nil=> exact diagOneSumVU _ i k
 | cons a l ih=>
   obtain ⟨w,p⟩:=List.pairwise_cons.mp d
   have A:= u a (by simp)
   have B := fun (x:MeterPanelVU P)(m:x∈l)=> u x (List.mem_cons_of_mem a m)
   have hi:sumΘVU l⊆ cabin C:=Set.Subset.trans Set.subset_union_right y
   have hp:= pairAtCutoff Y H i k s v (U:=a.2) (W:=sumΘVU l) (Set.Subset.trans Set.subset_union_left y) hi (shelterResVU w) Set.univ Set.univ ((well_spec ..).1 A).1 ((well_spec ..).1 (PolExpoVU B)).1 h
   rw [prod_consVU,hp, ih B p hi,List.map_cons,List.prod_cons]

local notation "ν" => prior SU.group (More (side Y i (Y.uv k)))
local notation "T" => bareAmplitude Y i k

def witnessCutVU (P:Spine) (i k:ℕ)(l:BillsSumVU P): Evaluation (side P.run i (P.run.uv k)):= (l.map (fun p => atCutoff P.run P.large i k p.1)).prod
structure TenderΘVU {P:Spine} (s i k:ℕ)(l:BillsSumVU P): Prop where
 pay : Pay P.run s i k
 locations : ∃ ξ:MeterPanelVU P→Finset Cover,
    (∀ a∈l, P.FootBill i k a.2 a.1 (ξ a)) ∧ FullDistances (l.toFinset.biUnion ξ) (side P.run i (P.run.uv k))
 comp : atCutoff P.run P.large i k (ΞProdVU l)= witnessCutVU P i k l
 -- cost
 value : let μ:= prior SU.group (More (side P.run i (P.run.uv k)))
   Integrable (bareAmplitude P.run i k (witnessCutVU P i k l)) μ ∧ Integrable (bareAmplitude P.run i k 1) μ ∧
   (∫ x, bareAmplitude P.run i k 1 x ∂μ)≠0 ∧
   taking P.run P.large i k (ΞProdVU l)=
     (∫ x,bareAmplitude P.run i k (witnessCutVU P i k l) x ∂μ)/(∫ x,bareAmplitude P.run i k 1 x ∂μ)

lemma productionTopVU{l:BillsSumVU P}(p:∀ a∈l,a.1∈PolAt Y H s a.2)(q:∀ a∈l,IsCompact a.2)
    (d:l.Pairwise (fun a b=> Disjoint a.2 b.2)):
    ∀ᶠ t:ℕ in atTop,TenderΘVU s (P.diagonalᵢ t) (P.diagonalₖ t) l:=by
 obtain ⟨C,pC⟩:= into_cabin (sumΘVU l) (cumulus_compactVU l q)
 filter_upwards [P.di_i.tendsto_atTop.eventually (wide_calendar Y C), P.pays_at s] with t hu hv
 let i':=P.diagonalᵢ t; let k':=P.diagonalₖ t
 have hp:Pay Y s i' k':=hv
 have ho:atCutoff Y H i' k' (ΞProdVU l)=witnessCutVU P i' k' l := atCutoffFullVU l p d hp hu pC
 refine ⟨hp,?_, ho,?_⟩
 · have ht: ∀ a∈l,∃ S:Finset Cover,P.FootBill i' k' a.2 a.1 S:=by
    intro a w; obtain ⟨S,x,e,v,_⟩:=P.atTop_flavor i' k' s _ (p a w) hp; exact ⟨S,v,x,e⟩
   choose! f k using ht; refine ⟨f,k, unwrap Y i' C hu _ _ ?_⟩
   intro r h; obtain ⟨a,z,b⟩:=Finset.mem_biUnion.mp h
   have hx: a∈l:=List.mem_toFinset.mp z; exact pC (singleIncVU hx ((k a hx).2.1.contains b))
 intro μ; obtain ⟨A,B,R⟩:=identifyRevenue Y H i' k' s (inside_budget Y H (PolExpoVU p)) hp
 rw [ho] at A R; exact ⟨A,(partitionIncome Y i' k' hp.1).1,B,R⟩

#print axioms productionTopVU
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
