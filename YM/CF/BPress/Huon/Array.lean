import YM.CF.BPress.Huon.Base
/-! shard of a payment in neighborhood of any incident bad block. No labels/selections assumed on cores not counting. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Along Spine Mosaic.Pulse Mosaic Palmer Contour Lilac.Stripe Ledger Push.AbsoluteSums
variable {R: Hangar (More N)} {H:Crew A}{I J L:Type}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]
variable {T Q: SlotT A R}{o b i:BlockY A R} {x y: Choir A R}
section general
variable (Y:J→Finset I) (x:Finset J)
lemma part [AddCommMonoid L] (f:I→L)(s:Finset I)(p:x.biUnion Y⊆s)(v:(x:Set J).PairwiseDisjoint Y) (h:∀ i∈s,i ∉ x.biUnion Y→ f i=0): (∑ i∈s,f i)=∑ t∈x,∑ i∈Y t,f i:=by rw [← sum_subset p h, sum_biUnion v]
variable (p:SlotT A R)(t:I→BlockY A R)
def chipAt(S:Finset I):= S.filter fun i=> t i∈ p
lemma cuts_q(x y:SlotT A R)(p:Disjoint x y)(S T: Finset I) : Disjoint (chipAt x t S) (chipAt y t T):= disjoint_left.mpr fun i h v=> disjoint_left.mp p ((mem_filter.mp h).2) ((mem_filter.mp v).2)
lemma bask0(S:Finset I)(V:J→SlotT A R) : x.biUnion (fun i=> chipAt (V i) t S)= chipAt (x.biUnion V) t S:=by ext1 i; simp only [mem_biUnion,chipAt,mem_filter]; aesop -- tune Heart
lemma bits0 (I:Finset I)(f:J→SlotT A R)(p:(x:Set J).PairwiseDisjoint f) : (x:Set J).PairwiseDisjoint (fun i=> chipAt (f i) t I):= fun i l j v e=> cuts_q t _ _ (p l v e) I I
-- alternate formula on blocked anchors, pack(P).State.Momentum.Window
lemma pieces [AddCommMonoid L](f:I→L)(S:Finset I): (∑ i∈ p, ∑ x∈ chipAt {i} t S, f x)=∑ x∈ chipAt p t S,f x:=by
 rw [← sum_biUnion, bask0, Finset.biUnion_singleton]; · simp -- tune
 exact bits0 p t S (fun i=>{i}) (fun i _ j _ h=> disjoint_singleton.mpr h)
lemma portions [AddCommMonoid L](f:I→L)(S:Finset I): (∑ i∈ p, ∑ x∈ S with t x=i,f x)=∑ x ∈ chipAt p t S,f x:=by simpa only [chipAt, mem_singleton] using pieces p t f S
lemma bucketM [MeasurableSpace L][MeasurableSpace I] [MeasurableSingletonClass I] (S:L→Finset I)(u:L→SlotT A R)(p: Measurable S)(v:Measurable u) : Measurable fun l=> chipAt (u l) t (S l):=(measurable_of_countable (fun i:SlotT A R × Finset I=> chipAt i.1 t i.2)).comp (v.prodMk p)
end general
abbrev badcore(x:Visit A R H) (f:I→BlockY A R)(S:SlotT A R) (t: Finset I):= chipAt (Vista H x.val S) f t
lemma partition (x: Visit A R H)(f:I→BlockY A R)(T:Finset I): (Camp x.val H).biUnion (fun i=> badcore x f i T)=chipAt (vicinity H x.val) f T:=by rw [show (Camp ..).biUnion _=_ from bask0 (Camp x.val H) f T (Vista H x.val), lands] -- tune ..
lemma separatesV(x:Visit A R H)(f:I→BlockY A R)(T:Finset I): ((Camp x.val H):Set _).PairwiseDisjoint (fun i=> badcore x f i T):= bits0 _ f _ _ (dark_disj ..)
lemma chargeG (x: Choir A R): (Camp x H).biUnion (Upper H x)= Peel.Place H x\vicinity H x:=by
 have ht:∀ i∈Camp x H, ∀ j,j∈Upper H x i↔ j∈i ∧ j∉vicinity H x:= fun i l j=> by rw [upper_l l]; exact Finset.mem_sdiff; -- tune indentation
 ext i; rw [mem_biUnion,Finset.mem_sdiff]; constructor; rintro ⟨j,g,q⟩; obtain ⟨u,v⟩:= (ht j g i).1 q; exact ⟨pay_p x g u,v⟩; rintro ⟨h,u⟩; obtain ⟨j,v,y⟩:= Peel.head H x h; exact ⟨j,v,(ht j v i).2 ⟨y,u⟩⟩
lemma upper_separates (x:Choir A R) : ((Camp x H):Set _).PairwiseDisjoint (Upper H x):=fun i u j v p=> (different fan (Peel.Place H x) u v p).mono (Finset.sdiff_subset) Finset.sdiff_subset -- tune
end YM.CF.BPress.Huon
