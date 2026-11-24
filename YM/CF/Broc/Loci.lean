import YM.CF.Broc.Live
/-! Local set operations with spin. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasurableEquiv MeasureTheory Paige Phase Phase.Sample Brace Cube
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N m B:Side}
def foam (N:Side)(v:ℕ)(S:Seal (Site N)):= S.biUnion fun i=>bay (terr N) i v
lemma foam_in(N:Side)(v:ℕ)(S): S⊆foam N v S:= fun i h=> mem_biUnion.mpr ⟨i,h, by simp [terr]⟩
lemma foams(v:ℕ)(p:0<v)(N:Side): Exceed (terr N) (terr N) (foam N v) (feeG v) (feeG v):=by
 refine ⟨fun {S} g=>?_,fun {S} g=>?_,fun i=>?_⟩
 · induction g with
   | single x => simpa [foam] using glen x v
   | @join S x y g p' he ih=>
     rw [show foam N v (insert x S)=bay (terr _) x v ∪ foam N v S from Finset.biUnion_insert]; exact (glen x v).unite ih ((bay_mem _).mpr (he.trans p)) (foam_in _ _ _ p')
 · calc
    _ ≤ ∑ i∈S, ((bay (terr N) i v).card:ℝ):=by unfold foam; exact_mod_cast (Finset.card_biUnion_le)
    _ ≤ ∑ i∈S,feeG v:= sum_le_sum fun i _=>Tenant.reach ..
    _ = _:=by simp [mul_comm]
 refine ⟨bay (terr N) i v, Tenant.reach .., fun T h q=>?_⟩
 obtain ⟨j,h,k⟩:=mem_biUnion.mp q; exact ⟨j,(bay_mem _).mpr (by rw [(terr _).sym]; exact (bay_mem _).mp k),h⟩
-- Markov interior
abbrev Table(m B:Side):=Seal (Site (Domain m B))
def complexA(m B:Side)(S:Table m B): Finset (Index m):= univ.filter fun i=> room m B i⊆S
lemma complex_up (m B):Monotone (complexA m B):=fun a b h i p=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.trans h⟩
lemma complex_down (m B S):Down m (complexA m B S):=by intro i h j e; exact mem_filter.mpr ⟨mem_univ _,(room_in (mem_filter.mp e).2).trans (mem_filter.mp h).2⟩
lemma chaps (S:Table m B): chairs m B S⊆ complexA m B (foam _ (8*B.val) S):=by
 intro i h; obtain ⟨x,p,q⟩:=pad_hit i (chair_pad h)
 refine mem_filter.mpr ⟨mem_univ _,?_⟩; intro y l; refine mem_biUnion.mpr ⟨x,p,(bay_mem _).mpr ?_⟩; change separation x y≤_
 rw [separation_comm]; apply (separation_triangle y _ _).trans ((Nat.add_le_add (room_span l) q).trans (by omega))
lemma fins (S:Table m B): walls m B S⊆ foam _ (8*B.val) S:=by
 intro i h; rcases mem_union.mp h with g|g; exact foam_in _ _ _ g
 obtain ⟨p,h,l⟩:=mem_biUnion.mp g; obtain ⟨x,h,t⟩:= pad_hit p h; refine mem_biUnion.mpr ⟨x,h,(bay_mem _).mpr ?_⟩; change separation _ _ ≤ _; rw [separation_comm]; apply (separation_triangle i _ _).trans ((Nat.add_le_add (room_span l) t).trans (by omega))
lemma commonA{U V:Skin m B}{s t:ArrayF m}(q:Sq){S:Table m B}(h: Agrees (foam _ (8*B.val) S) U V)(e: ∀ i:Spot m, i.1∈ complexA m B (foam _ (8*B.val) S)→s i=t i):AgreeF S (paint m B U s q) (paint m B V t q):=by
 intro x p; obtain ⟨a,f,-⟩:=full_r m B x
 have hp:a∈pavilion m B S:=(pad_iff ..).mpr ⟨x,p,a,f,by simp⟩
 have hu: room m B a ⊆foam _ (8*B.val) S:= (in_wall hp).trans (fins _)
 have ht: Agrees (room m B a) U V:= fun j H P=> h j (hu H) (hu P)
 unfold paint; refine sum_congr rfl ?_; intro i _; by_cases g:i∈bandS m B x q
 · have hx:=spot_hit g; rw [e i (chaps S (chaff.mpr ⟨x,p,i.1,hx,fits_id m i.1⟩))]; apply congrArg; unfold freight; apply congrArg; apply sum_congr rfl; intro j _; unfold launch tax; rw [traverse f (room_in (room_active f hx) (raddr m B i.1)) ((separation_comm ..).trans_le (node_dist hx).le) j ht]
 simp [outside g]
lemma arr_s (X Y:Sheen m B)(S:Table m B)(p:AgreeF S X Y):∀ i:Spot m,i.1∈ complexA m B S→ arrayZ m B X i=arrayZ m B Y i:= fun i h=> p _ ((mem_filter.mp h).2 (raddr ..))
lemma honor (x y:Cue m)(S:Table m B)(h: AgreeF (complexA m B (foam _ (8*B.val) S)) x y){U V:Skin m B}(p:Agrees (foam _ (8*B.val) S) U V) : AgreeF S (starfish m B U x) (starfish m B V y):= fun i hp=> congrArg Brace.box (commonA _ p (fun _ hy=> h _ hy) i hp) -- tune inferred S
end YM.CF.Broc
