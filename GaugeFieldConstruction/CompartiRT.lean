import GaugeFieldConstruction.OpalRT
/-!
 # finite patch gluing for germs E^− and E^+ hol near boundary. E equality from both on contour. goal B germs incl any finite m.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.PortRT
open Filter Set MeasureTheory Function Topology Metric Complex Module
open scoped BigOperators Topology ContDiff NNReal ENNReal
variable {U:Type*}[NormedAddCommGroup U][NormedSpace ℂ U][FiniteDimensional ℂ U]
variable {Y:Type*}[TopologicalSpace Y][T2Space Y][RegularSpace Y][MeasurableSpace Y][BorelSpace Y][SecondCountableTopology Y]{μ:Measure Y}
variable {K:Set Y}(hK:IsCompact K)
-- iH α patches option S arbitrary. include integrable capability
variable {ι:Type*}(A:ι→ Set U)(F:ι→ U→Y→ℂ)(x:U)
abbrev QuiltLocalRt (S:Set Y):= ∃ G:U→ℂ, AnalyticAt ℂ G x ∧ ∀ i:ι, ∀ᶠ y in 𝓝[A i] x,IntegrableOn (F i y) S μ ∧ ∫ z in S,F i y z ∂μ= G y
variable (p:∀ y∈K,∃ H:Set Y, IsOpen H ∧ y∈H ∧ ∀ S⊆K∩H,MeasurableSet S→ QuiltLocalRt (μ:=μ) A F x S)
include p hK
lemma quiltCombineRt : QuiltLocalRt (μ:=μ) A F x K:=by
 classical
 choose G u g t using p
 let T:= fun y:K=> G y y.2
 obtain ⟨s,hs⟩:= hK.elim_finite_subcover T (fun i=>u _ i.2) (by intro x h; exact mem_iUnion.mpr ⟨⟨x,h⟩,g x h⟩)
 let I(s:Finset K):=⋃ i∈s,T i
 have he : ∀ s: Finset K, ∀ b:Set Y,MeasurableSet b→b⊆K→b⊆I s→ QuiltLocalRt (μ:=μ) A F x b:=by
    intro s; induction s using Finset.induction_on with
    | empty => intro b hb _ q; simp [I] at q; subst b; exact ⟨fun _=>0,analyticAt_const, fun _=>Eventually.of_forall fun _=>by simp⟩
    | @insert y s h ih =>
       intro b hb q l; let H:= b ∩ T y
       have p1:MeasurableSet H:= hb.inter (u _ y.2|>.measurableSet); have p2:H⊆K∩ T y:= fun x u=>⟨q u.1,u.2⟩ -- tune
       obtain ⟨f,o,hf⟩:= t y.val y.2 H p2 p1; obtain ⟨w,r,hw⟩:= ih (b\H) (hb.diff p1) (sdiff_subset.trans q) (by
          intro z hz
          have V:I (insert y s)= T y∪ I s:=by simp only[I,Finset.set_biUnion_insert]
          have p:z∈ T y∪ I s:= V ▸ l hz.1; exact p.resolve_left fun e=> hz.2 ⟨hz.1,e⟩)
       have v: H ∪ (b\H)=b:= Set.union_sdiff_cancel (inter_subset_left (s:=_) (t:=_)); refine ⟨fun i=> f i+w i, o.add r,fun i=>?_⟩
       filter_upwards [hf i,hw i] with k e p; rw [← v,e.2.symm,p.2.symm]; exact ⟨e.1.union p.1,setIntegral_union (Set.disjoint_left.mpr fun i hi h=>h.2 hi) (hb.diff p1) e.1 p.1⟩
 exact he s K hK.measurableSet (Subset.refl _) hs
end YM.PortRT
end
