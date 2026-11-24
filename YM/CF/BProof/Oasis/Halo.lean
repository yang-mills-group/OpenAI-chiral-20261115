import YM.CF.BProof.Oasis.Hut
import YM.CF.Chaff.Pulse
/-! eq:B-wheat: micro-node ledger including support of the masks. Give actual
witness; no volume radius used either in occupied set or delivered estimates. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {N:Side}
def valley (P:BudgetPoint)(i:Hub N):= halo P.B (coverNumber_realized P.B i.val.2).choose
def lot(P:BudgetPoint)(i:Hub N) : Support (More N):= Lattice.halo 12 (valley P i)
lemma headQ(P:BudgetPoint)(i:Hub N): i.val.2 ⊆ valley P i:= ((coverNumber_realized P.B i.val.2).choose_spec.1).1
lemma seeQ(P:BudgetPoint)(i:Hub N){S:Support (More N)}(h:S⊆i.val.2): RG.inspected S ⊆ lot P i:= Subset.trans (Yaw.touchK _) (Corona.halo_mono le_rfl (h.trans (headQ P i)))
lemma seeT(P:BudgetPoint)(i:Hub N): i.val.2⊆ lot P i:= (headQ P i).trans (halo_subset 12 _)
lemma halo_shape {S:Support N}(w:S.Nonempty)(x:Grove (terr N) S)(k:ℕ): Grove (terr N) (halo k S):=by
 obtain ⟨i,h⟩:=w; apply trunk (x:=i) (halo_subset _ _ h); intro z u; obtain ⟨y,g,p⟩:=halo_spec.mp u; let K:=terr N; let T:=bay K y k; have he:T⊆ halo k S:=fun v hv=>halo_spec.mpr ⟨y,g,(bay_mem _).mp hv⟩; exact (orig_sub (rooted x _ h _ g) (halo_subset ..)).trans (orig_sub (rooted (Tenant.glen y k) _ (by simp [terr]) _ ((bay_mem _).mpr p)) he)
lemma lot_ok(P:BudgetPoint)(i:Hub N): Grove (terr _) (lot P i):=by
 have h:=headQ P i i.property; exact halo_shape ⟨_,h⟩ (trunk h (fun y hy=> ((coverNumber_realized P.B i.val.2).choose_spec.1).2 i.val.1 h y hy)) 12
def coverC(P:ℕ):ℕ:=(P+P+1)^4*(12+12+1)^4
-- for growth use name argument B not budget later
lemma lot_price (P:BudgetPoint)(i:Hub N) : (lot P i).card≤coverNumber P.B i.val.2*coverC P.B:=by
 let S:= (coverNumber_realized P.B i.val.2).choose; have hp:(valley P i).card≤ coverNumber P.B i.val.2*(P.B+P.B+1)^4:= by rw [←show S.card=coverNumber P.B i.val.2 from (coverNumber_realized P.B i.val.2).choose_spec.2]; exact Corona.halo_size .. -- tune orientation
 exact (Corona.halo_size ..).trans ((Nat.mul_le_mul_right ((12+12+1)^4) hp).trans_eq (mul_assoc ..))
def field(P:BudgetPoint)(i:Hub N): Y (More N):= ⟨lot P i,⟨_,seeT P i i.property⟩⟩
def lordR(P:BudgetPoint)(i:OptionR N):= field P i.1.2
def lordG(P:BudgetPoint)(i:OptionF N):= field P i.1.val.1
def lordJ(i:OptionJ N): Y (More N):=⟨{node i.1}, singleton_nonempty ..⟩
def streets(P:BudgetPoint)(i:Options N) : Y (More N):= Sum.elim lordJ (Sum.elim (lordR P) (lordG P)) i
abbrev corner(o: Lv N):=badgeOf (seam o).2
lemma toFinSpec{I J:Type*}[LinearOrder I][LinearOrder J](e:I↪ J)(L:List I): (L.map e).toFinset=L.toFinset.map e:=by ext x; simp only [List.mem_toFinset,List.mem_map,Finset.mem_map]
lemma crispGe(i:OptionG N) : ((Ark N).crisp (.inr i))=(((lineR N).addD (lineF N)).crisp i).map bendR:=by unfold Dew.crisp; change ((List.map (bendR (I:=Single N)) (_:List (Dwell N))).toFinset)=_; exact toFinSpec _ _
lemma crispJe(i: OptionJ N) : ((Ark N).crisp (.inl i))= i.2.val.map bendL:=by unfold Dew.crisp; change ((List.map (bendL (J:=Dwell N)) (bkiln i.2.val).reverse).toFinset)=_; refine Eq.trans (toFinSpec _ _) ?_; congr 1; rw [List.toFinset_reverse,bkiln_k]
def plaza(P:BudgetPoint)(N:Side): Civic (More N) (Ark N) where
 home:=corner
 zone:=streets P
 belt := by
    rintro (i|i) j h
    · rw [crispJe] at h; obtain ⟨k,v,rfl⟩:= mem_map.mp h; have ht:= (mem_alloy ..|>.mp i.2.property).1 v; change badgeOf k∈ {node i.1}; rw [mem_singleton]; exact congrArg node (mem_singleton.mp ((mem_stake ..).mp ht)) -- tune
    rw [crispGe] at h; obtain ⟨k,v,rfl⟩:= mem_map.mp h; rcases i with i|i
    · change k∈ (bkiln i.2.val).toFinset at v; rw [bkiln_k] at v; have hx:= (mem_powerset.mp ((mem_filter.mp (mem_of_mem_erase i.2.property)).1)) v; exact seeT P i.1.2 (mem_filter.mp hx).2
    change k∈ (bkiln i.2.val).toFinset at v; rw [bkiln_k] at v; have hx:= (mem_powerset.mp ((mem_filter.mp i.2.property).1)) v; exact seeT P i.1.val.1 (mem_filter.mp hx).2
 peace:= by
    rintro (i|(i|i)) (j|(j|j)) e
    all_goals first|exact trivial|skip
    · change i.1≠ j.1; intro u; apply Finset.disjoint_left.mp e (mem_singleton_self (node i.1)) (show node i.1∈({node j.1}:Support (More N)) from mem_singleton.mpr (congrArg node u))
    have he: Disjoint i.1.val.1.val.2 j.1.val.1.val.2:= e.mono (seeT ..) (seeT ..); refine ⟨?_,he⟩; intro v; rw [← v] at he; exact disjoint_left.mp he i.1.val.1.property i.1.val.1.property
lemma plazaHeat(P:BudgetPoint)(i:Options N): Grove (terr _) ((plaza P N).zone i).val:=by rcases i with i|(i|i); exact .single _; exact lot_ok ..; exact lot_ok ..
variable {j:ℕ}{a b l r δ c v η:ℝ} {R:Spin.Ready j a b l r}{F: Core j a b l r N}(H:Honor R F δ) {p:Pay}
lemma grant (P:BudgetPoint)(A:TariffE (Tape.kiln H.1 c v η|>.mark) p paymentE) : Civic.Bright (plaza P N) A.award p.rate (coins p):= TariffE.bright A (fun x=> congrFun (Tape.kiln H.1 c v η|>.index) _) (Tape.kiln H.1 c v η|>.town) -- tune
end YM.CF.BProof.Oasis
