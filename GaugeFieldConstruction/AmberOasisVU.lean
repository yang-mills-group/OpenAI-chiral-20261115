import GaugeFieldConstruction.CedarSwimVU
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
section
variable {P : Spine} {R:P.Register} {s : ℕ}{j:Axis}{c:P.Poll j}{x:P.Spectrum0 j}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "H"=> P.large
local notation "V" i:max=> (c i).t
local notation "D" i:max=> P.pollTicket j c i
local notation "left" i:max=> Future.closing P.run P.large j (c i)
local notation "rite" i:max=> Future.opening P.run P.large j (c i)

abbrev CerealAVU (P:Spine) (j:Axis)(c:P.Poll j)(i:ℕ): MeterPanelVU P:=
 (pinhole P.Test (c i).t (Future.kernelPast P.run P.large j (c i)),footprint P.par P.width (c i).t (Future.closing P.run P.large j (c i)))
abbrev CerealBVU (P:Spine) (j:Axis)(c:P.Poll j)(i:ℕ): MeterPanelVU P:=
 (pinhole P.Test (c i).t (Future.kernelRoot P.run P.large j (c i)),footprint P.par P.width (c i).t (Future.opening P.run P.large j (c i)))
local notation "T" i:max=> CerealAVU P j c i
local notation "Z" i:max=> CerealBVU P j c i
abbrev PollavuVU(P:Spine)(j:Axis)(c:P.Poll j)(i:ℕ):BillsSumVU P:= [CerealAVU P j c i,CerealBVU P j c i]
local notation "F"=> PollavuVU P j c
lemma CerealFairVU{X:BillsSumVU P} (p:∀ a∈X,IsCompact a.2)(e:∀ a∈X,a.1∈PolAt Y H s a.2)(d:X.Pairwise (fun a b=>Disjoint a.2 b.2)):
    ∀ᶠ i in atTop,∀ h:P.Poll j,
    let l:= X++PollavuVU P j h i
    (s≤(h i).t) ∧ (∀ a∈l,a.1∈PolAt Y H (h i).t a.2) ∧ (∀ a∈l,IsCompact a.2) ∧ l.Pairwise (fun a b=>Disjoint a.2 b.2):=by
 have hx:= cumulus_compactVU X p
 filter_upwards [eventually_sans Λ (sumΘVU X) j hx, eventually_ge_atTop s, (wait_grows Λ).eventually (eventually_gt_atTop 0)] with i hv hp hd h
 let a:=CerealAVU P j h i; let b:=CerealBVU P j h i; let t:=(h i).t
 have hA:= Future.labels_far Y H j (h i)
 have ht: s≤t:=hp.trans (h i).arrival
 have hy : Disjoint a.2 b.2:=Set.disjoint_left.mpr (by
    intro u x v; let d':ℝ:=whenly (timeMesh Λ) 0 i; have hq:u j ≤ -d':=hA.2 x; have hx:d'≤u j:=hA.1 v; have hc:0<d':=hd; linarith)
 have hB:= hv.mono_right (Set.union_subset_union hA.1 hA.2)
 have Hq{V':Set RSpace}{x: P.Effect}(r:x∈circum Λ P.width P.calibration true V' {t}): x∈PolAt Y H t V':=circum_widens Y H Set.Subset.rfl (by simp) r
 obtain ⟨q,r⟩:=Future.picture Y H j (h i)
 intro L; refine ⟨ht,?_,?_,List.pairwise_append.mpr ⟨d,?_,?_⟩⟩
 · intro z p; rcases List.mem_append.mp p with p|p; exact (polAt_up Y H ht) (e z p); simp only [PollavuVU,List.mem_cons,List.not_mem_nil,or_false] at p; rcases p with s'|s'; exact s' ▸ Hq q; exact s' ▸ Hq r -- rewrite direction?
 · intro z p'; rcases List.mem_append.mp p' with w|v; exact p z w; simp only [PollavuVU,List.mem_cons,List.not_mem_nil,or_false] at v; rcases v with z'|z' <;> subst z <;> exact footprint_compact ..
 · change [a,b].Pairwise (fun p q=>Disjoint p.2 q.2); simpa using hy
 intro x px y py
 simp only [PollavuVU,List.mem_cons,List.not_mem_nil,or_false] at py
 rcases py with z|z <;> subst y
 exact hB.mono (singleIncVU px) Set.subset_union_right
 exact hB.mono (singleIncVU px) Set.subset_union_left

lemma CerealEqVU(i:ℕ):ΞProdVU (F i)=D i:=by
 change ΞProdVU (F i)= (c i).boundary ..
 rw [Future.twoEnds]; simp only [PollavuVU,ΞProdVU,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]

end
section
variable {P:Spine} {R:P.Register}{j:Axis}{x:P.Spectrum0 j}{c:P.Poll j}
local notation "I"=> P.diagonalᵢ
local notation "Kq"=> P.diagonalₖ
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "H"=> P.large
local notation "V" i:max=> (c i).t
local notation "D" i:max=> P.pollTicket j c i
local notation "S"=> P.spirits R j x
abbrev HeightOutVU (P:Spine) (r:ℕ): P.Effect→ℂ:= Reconstruction.readingAtTop P.run P.large (P.diagonalᵢ r) (P.diagonalₖ r)

-- script receipt on all finite products EVEN WHEN placed differently & all components being asked at once
structure SummitInvoiceVU {s:ℕ} (i r:ℕ)(l:BillsSumVU P)(ε:ℝ) : Prop where
 body : TenderΘVU (c i).t (P.diagonalᵢ r) (P.diagonalₖ r) (l++PollavuVU P j c i)
 screen : TenderΘVU (c i).t (P.diagonalᵢ r) (P.diagonalₖ r) (PollavuVU P j c i)
 stay : 1/2< ‖HeightOutVU P r (P.pollTicket j c i)‖
 price : dist (HeightOutVU P r (ΞProdVU l*P.pollTicket j c i)/ HeightOutVU P r (P.pollTicket j c i))
       (P.spirits R j x (ΞProdVU l))<ε
 disjointSupports : (l++PollavuVU P j c i).Pairwise (fun a b=>Disjoint a.2 b.2)
 le_height:s≤ (c i).t

lemma BiPayVU (C:P.Selects R j x c){s:ℕ}{l:BillsSumVU P} (p:∀ a∈l,IsCompact a.2)(e:∀ a∈l,a.1∈PolAt P.run P.large s a.2)(d:l.Pairwise (fun a b=>Disjoint a.2 b.2)){ε:ℝ}(E:0<ε):
    ∀ᶠ i in atTop,∀ᶠ r:ℕ in atTop,SummitInvoiceVU (R:=R) (x:=x) (s:=s) (c:=c) i r l ε:=by
 let A:= ΞProdVU l
 have h:= CerealFairVU (j:=j) p e d
 have ho:A∈shorter P.Test s:=inside_budget Y H (PolExpoVU e)
 have hz':1/2< ‖(1:ℂ)‖:=by norm_num
 have hz := C.denominator_tends.norm.eventually (lt_mem_nhds hz')
 have hx:= (C.poll A s ho).1
 filter_upwards [h, hz, Selects.forJourneyPath P R j x c C A s ho, Metric.tendsto_nhds.mp hx (ε/2) (half_pos E)] with i h hz ht hl
 let G:= l++PollavuVU P j c i
 obtain ⟨ha,hb,hc,hu⟩:=h c
 let Y':=PollavuVU P j c i
 have ht' (a)(w:a∈Y'):a∈ G:=List.mem_append.mpr (Or.inr w) -- argument order
 have hw':=CerealEqVU (c:=c) i
 have ht₀:= P.cone_income R (v:=P.pollTicket j c i) (s:=(c i).t) (hw' ▸ inside_budget P.run P.large (PolExpoVU (fun a (m:a∈PollavuVU P j c i) => hb _ (ht' a m))))
 have hk:= ht₀.comp (P.all_heights_here R)
 filter_upwards [productionTopVU hb hc hu,productionTopVU (l:=Y') (fun a m=>hb _ (ht' a m)) (fun a m=>hc _ (ht' a m)) (List.pairwise_append.mp hu).2.1,
   hk.norm.eventually (lt_mem_nhds hz),Metric.tendsto_nhds.mp ht.2 (ε/2) (half_pos E)] with r he hE hx' hy
 refine ⟨he,hE,hx',?_,hu,ha⟩
 let f(r):= HeightOutVU P r (A*D i)/ HeightOutVU P r (D i)
 change dist (f r) _ < ε
 have ht : dist (f r) (P.RatioOn R j c i A)< ε/2:=hy
 exact lt_of_le_of_lt (dist_triangle _ _ _) (add_halves ε ▸ add_lt_add ht hl)

#print axioms BiPayVU
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
