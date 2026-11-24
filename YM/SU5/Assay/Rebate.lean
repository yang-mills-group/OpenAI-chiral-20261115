import YM.SU5.Assay.Cinder
import YM.SU5.Assay.Book
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
open Six
/-! `Spent`: rebate for linear combinations of the components; even offering the
 words after pairing separate probes' raw marginal lists, no prescription of
 membership tests for forms on an alternative operator system. -/
variable (s:ℕ)(M N:Set Vantage)
local notation "φ" m:max=>fun f=>P.asked_at s f m
def Spent:Submodule ℂ P.Test:=Submodule.span ℂ {f|P.asked_at s f M ∧ P.GFlame f}
local notation "μ"=>P.Spent s
variable {P j x M N s}{f g:P.Test}
lemma asked_at.add (p:P.asked_at s f M)(q:P.asked_at s g M):P.asked_at s (f+g) M:=by
 obtain ⟨A,u,h⟩:=p;obtain ⟨T,v,e⟩:=q
 exact ⟨A∪T,(bay K ..).add_mem (tallerBay _ _ _ Finset.subset_union_left u) (tallerBay _ _ _ Finset.subset_union_right v),(P.pin_union ..).symm ▸ Set.union_subset h e⟩
lemma asked_at.join (p:P.asked_at s f M)(q:P.asked_at s g N):P.asked_at s (f*g) (M∪N):=by
 obtain ⟨A,u,h⟩:=p;obtain ⟨T,v,e⟩:=q
 exact ⟨A∪T,(bay K ..).mul_mem (tallerBay _ _ _ Finset.subset_union_left u) (tallerBay _ _ _ Finset.subset_union_right v),(P.pin_union ..).symm ▸ Set.union_subset_union h e⟩
lemma Spent.flame (h:P.asked_at s f M)(t:P.GFlame f):f∈μ M:=Submodule.subset_span ⟨h,t⟩
lemma Spent.in_y (h:f∈μ M):P.asked_at s f M:=by
 refine Submodule.span_induction (p:=fun f _=>P.asked_at s f M) (fun _ h=>h.1) ?_ (fun _ _ _ _=> asked_at.add) ?_ h
 · exact ⟨∅,zero_mem _,by simp [pinFoot]⟩
 intro a f _ u; obtain ⟨A,h,w⟩:=u;exact ⟨A,(bay K ..).smul_mem h a,w⟩
lemma Spent.clips (h:f∈μ M):f∈P.Cinder:=Submodule.span_mono (show _ from fun _ v=>v.2) h
lemma Spent.visitor (p:f∈μ M)(q:P.asked_at s g N)(u:Disjoint M N):f*g∈μ (M∪N):=by
 let L:=μ (M∪N)
 refine Submodule.span_induction (p:=fun f _=> f*g∈ L) (fun w p=>?_) (by rw [zero_mul];exact L.zero_mem) (fun _ _ _ _ h v=>by rw [add_mul]; exact L.add_mem h v) (fun a _ _ h=>by rw [smul_mul_assoc];exact L.smul_mem _ h) p
 apply Spent.flame (p.1.join q)
 obtain ⟨⟨A,h,v⟩,t⟩:=p;obtain ⟨T,a,z⟩:=q
 exact t.beside h a (P.pin_disjoint _ _ _ (u.mono v z))
lemma Spent.mono (u:M⊆N):μ M ≤ μ N:=by
 refine Submodule.span_mono ?_
 rintro v ⟨⟨A,h,t⟩,z⟩;exact ⟨⟨_,h,t.trans u⟩,z⟩

-- Post assignment, incl applied to an earlier or native offer
variable {c:Bool}{D:Finset Cover}
lemma split_rebate (h:PureSplit K c D f g)(q:P.pinFoot s D ⊆ M) : f∈μ M∧g∈μ M:=by
 obtain ⟨a,v⟩:=pure_flames h
 exact ⟨Spent.flame ⟨_,h.2.2.1,q⟩ a,Spent.flame ⟨_,h.2.2.2.1,q⟩ v⟩
lemma PostAsk.sheet {x:P.Spectrum0 3}(q:P.PostAsk s x f M c):
 ∃D l,P.pinFoot s D ⊆ M∧ Presented K c D f l ∧ ∀a∈l,a.1∈μ M∧a.2∈μ M:=by
 obtain ⟨D,l,u,_,g,_⟩:=q; exact ⟨D,l,u,g,fun a k=>split_rebate (g.2 a k) u⟩

-- Pre assignment preserved for billing (on really the earlier list)
variable {A:P.Apron}{l:P.Folio}
lemma firstPose.rebate (p:P.FirstDress A c l)(r:P.Register)(v:A.s≤ s)(y:Cover) (q:P.Aperture A (P.meshPose s y)⊆M) :
 ∀i∈l,P.sParcel s A i.1 y ∈ μ M ∧ P.sParcel s A i.2 y ∈μ M:=by
 have z(f:P.Test)(h:f∈bay K A.S true)(e:P.GFlame f):P.sParcel s A f y∈μ M:=
   Spent.flame ⟨_,sParcel.atPlot A s h _,(P.inside_now _ _ _ v).trans q⟩ (sParcel.flame A s e y r)
 intro i u; have t:=p.2.prepared'.2 i u
 exact ⟨z _ t.2.2.1 (pure_flames t).1,z _ t.2.2.2.1 (pure_flames t).2⟩

-- Price across the whole space-price of a smear. Whole linear grids or terms
lemma firstPose.smear {F:SampleDose} (p:P.FirstDress A c l)(r:P.Register)(v:A.s≤ s)(y:Cover)
 (q:P.meshPose s y∈tsupport F.val) :∀i∈l,P.sParcel s A i.1 y ∈ μ (P.spacePrice A F) ∧ P.sParcel s A i.2 y ∈ μ (P.spacePrice A F):=
 firstPose.rebate p r v y (Set.subset_iUnion₂_of_subset _ q Set.Subset.rfl)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
