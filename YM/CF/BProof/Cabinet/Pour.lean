import YM.CF.BProof.Cabinet.Core
/- severe angular costs B-SBill. Assign log to root core containing b. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Cabinet
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Pods Posts Brick Account Moment
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)
local notation "BP"=> House.Season Y.yard Y.c'
local notation "B" => Y.Block
local notation "gY" => Y.g
variable (r:ℕ)(x:Pod Y)
lemma grandeur {A:Type*}[AddCommMonoid A](f:B→ A): ∑ Q∈ recital Y r x,∑ i∈ Q.val,f i=∑ i∈ bitL Y x,f i:=by
 let K:= plan BP r; have hv : Set.PairwiseDisjoint (↑(recital Y r x)) K.S:= fun i p j q e=> Disjoint.mono (K.sub i) (K.sub j) (orbitF BP r (bitL Y x) p q e); change (∑ Q∈_,∑ i∈ K.S Q,f i)=_; rw [← Finset.sum_biUnion hv,show (recital Y r x).biUnion K.S=bitL Y x from coverE BP r _] -- tune
namespace Pour
variable (u:θ∈Set.Icc (1/2) 2)(t:T.Bounds c w R v)(b:BudgetPoint)(h:b.threshold=thresh y)(β:ℝ)(vβ:y≤2*β)(pβ:β≤2*y)
-- logs on candidate binder u t; h formula; HoldScript
-- gauge weak mapped
abbrev Meter(q:ℂ):=q -- tune
abbrev wit(w:Entice S L a d y) (b:BudgetPoint)(e:b.threshold=thresh y): ValidR c b (S.M y):= Setup.permits w b e
def upkeep := Weights.lightG Y.yard Y.hall S.M T θ β (pulse P Y) (room P Y) t u b (wit P b h) (tool Y x)
def bulk := (upkeep Y P T θ x u t b h β:ℂ)
abbrev fŴ := wallet y Y.g.count.val S.P S.M c R w v S.height Y.yard.short (S.focus Y.yard.short y) 4
include vβ pβ
lemma weak : Nonempty (Teller (gridBase BP) (Cabinet.Ready P Y T θ) (Esp Y r) (Layer Y.yard) (fun x=>bulk Y P T θ x u t b h β) 4 (fŴ Y)):=by
 obtain ⟨A⟩:= furnish Y.yard Y.hall gY S.M T θ β (pulse P Y) (room P Y) t u b (wit P b h) S.height vβ pβ h (agenda P Y)
 let f(i:Layer Y.yard)(x:Pod Y):ℂ:=A.bill i (tool Y x); have ht(x:Pod Y)(l: Cabinet.Ready P Y T θ x):= Setup.proceeds P Y T θ _ l; refine ⟨A.starboard,A.size,f,fun x p=>?_, A.pay,?_,A.our,fun i=>Complex.continuous_ofReal.measurable.comp ((A.meas i).comp (Brick.Act.pawn_m ..)),?_⟩
 · unfold bulk upkeep; rw [A.values _ (ht x p),Complex.ofReal_sum]; -- tune f def
 · intro i x p; unfold f; rw [Complex.norm_real]; exact A.amount _ _ (ht x p)
 intro i x y v p q; exact congrArg Complex.ofReal (A.private_read i _ _ (Act.agrees Y.yard gY (esp_here Y x y r v)) (ht x p) (ht y q)) -- tune esp args
omit vβ pβ
-- gauge severe block exp counted once
abbrev bd(q:Y.yard.Col):ℝ:= Weights.burn Y.yard Y.hall S.M T θ β (pulse P Y) (room P Y) t u b (tool Y x) q
def FuelL :=∑ i∈ (tool Y x).sev,bd Y P T θ x u t b β i
abbrev fuelY := FuelL Y P T θ x u t b β
abbrev columns(i:B) := Finset.univ.filter fun q:Y.yard.Col=> bT Y q=i ∧ q∈ (tool Y x).sev
def stopL(i:B):=∑ q∈ columns Y x i,bd Y P T θ x u t b β q
lemma col_tr(i:B): (columns Y x i).Nonempty ↔ Mint.trueG Y x i:=by
 constructor; rintro ⟨q,l⟩; obtain ⟨v,t⟩:= (mem_filter.mp l).2; exact ⟨⟨q,v⟩,(Act.sev_c Y.yard gY x i _).1 t⟩; rintro ⟨j,l⟩; exact ⟨j.val,mem_filter.mpr ⟨mem_univ _,j.property,(Act.sev_c Y.yard gY x i j).2 l⟩⟩
lemma col_bad(i:B)(h:Mint.trueG Y x i): i∈ sick Y x:= (sick_c Y x i).2 (Or.inl h)
lemma col_t(i:B): columns Y x i= (tool Y x).sev.filter (fun q=> bT Y q=i):=by ext j; simp [columns]; exact and_comm
lemma fuel_stop : FuelL Y P T θ x u t b β= ∑ i∈ bitL Y x,stopL Y P T θ x u t b β i:=by
 have hp(i:B): stopL Y P T θ x u t b β i=∑ j∈(tool Y x).sev with bT Y j=i,bd Y P T θ x u t b β j:=by rw [stopL,col_t]
 simp_rw [hp,FuelL]; symm; apply sum_fiberwise_of_maps_to; intro i g; exact enlargement Y x (Act.severe_sector Y.yard gY y x i g) -- tune
include h
lemma tax_here (q:Y.yard.Col){x x'}{A:Finset (House.Block Y.yard Y.c')}(v:truck Y (bT Y q) 1⊆ A)(p:Spiced Y A x x')(η:Cabinet.Ready P Y T θ x)(g:Cabinet.Ready P Y T θ x') : bd Y P T θ x u t b β q= bd Y P T θ x' u t b β q:=by
 apply burn_same Y.yard Y.hall gY S.M T θ β (pulse P Y) (room P Y) t u b (wit P b h) _ _ q A (Setup.proceeds P Y T θ _ η) (Brick.Act.agrees Y.yard gY p) (Setup.proceeds P Y T θ _ g) (agenda P Y).range_cost (ray_loan Y.yard gY A 1 (by rw [one_mul]; exact (agenda P Y).limit) v) -- tune arg order
variable (r' : 1 ≤ r)
include r'
def baseG : Shift Y P T θ r:=by
 refine ⟨fun Q x=> (∑ i∈ Q.val,stopL Y P T θ x u t b β i:ℝ),fun i=>Complex.continuous_ofReal.measurable.comp (Finset.measurable_sum _ (fun j _=> ?_)),?_⟩
 · unfold stopL columns; simp_rw [sum_filter]; apply Finset.measurable_sum _; intro i _; apply Measurable.ite _ ((Weights.burn_m Y.yard Y.hall S.M T θ β (pulse P Y) (room P Y) t u b i).comp (Brick.Act.pawn_m ..)) measurable_const; apply MeasurableSet.inter; swap; · exact (Brick.Act.pawn_m ..) (Pawn.sev_sets (fun s=>i∈s))
   change MeasurableSet {x: Pod Y| bT Y i=j}; by_cases l:bT Y i=j <;> simp [l]
 · intro q x y _ _ a c v; have he:= (Brick.Act.agrees Y.yard gY v); apply congrArg Complex.ofReal; apply sum_congr rfl; intro i l
   have hp(j:Y.yard.Col)(k:bT Y j=i): j∈(tool Y x).sev ↔ j∈(tool Y y).sev:=he.sev j ((show bT Y j∈ plate Y r q from k.symm ▸ (plan BP r).sub q l)); unfold stopL columns; simp_rw [sum_filter]; apply sum_congr rfl; intro j _; by_cases H:bT Y j=i; swap; · simp [H];
   simp only [hp j H,H,true_and]; split; rename_i g; refine tax_here Y P T θ u t b h β j ?_ v a c; rw [H]; intro b p; rw [plate, Tower.whole]; exact Grid.collar_mem.mpr ⟨i,l,(Grid.dist_symm ..).trans_le (((ray_spec ..).1 p).1.trans r')⟩; exact rfl -- tune
lemma earns : (baseG Y P T θ r u t b h β r').amt x=FuelL Y P T θ x u t b β:=by unfold Shift.amt; rw [fuel_stop Y P T θ x u t b β,← grandeur Y r x (stopL Y P T θ x u t b β),Complex.ofReal_sum]; rfl
variable (p:ℝ)(e:0≤p)(k:p≤ Pricing.bill_c c Y.yard.short S.κ y β)
include vβ k e
lemma pays : (baseG Y P T θ r u t b h β r').Income (fun Q x=> -((Mint.stripe Y r Q x).card:ℝ)*p):=by
 intro x Q l v; change (Complex.ofReal _).re≤_; set W:=stopL Y P T θ x u t b β; let V:=bd Y P T θ x u t b β; let U:= Mint.stripe Y r Q x
 have ht(i:B)(q:i∈Q.val): i∈ U ↔ Mint.trueG Y x i:=by
    unfold U Mint.stripe; rw [mem_filter]; exact and_iff_right_of_imp (fun p=> mem_inter.mpr ⟨col_bad Y x i p,q⟩) -- tune
 have hx(j:Y.yard.Col)(h':j∈ (tool Y x).sev): V j≤-p:= le_trans (Weights.burn_c Y.yard Y.hall S.M T θ β (pulse P Y) (room P Y) t u b (wit P b h) _ j (Setup.proceeds P Y T θ _ l) (agenda P Y).thin (agenda P Y).ink h vβ (agenda P Y).stamp h') (neg_le_neg k)
 let f(i:B):= if i∈ U then -p else 0
 have hu:U⊆Q.val:= (filter_subset ..).trans (inter_subset_right (s₁:=sick Y x)) -- tune
 refine le_trans (b:=∑ i∈ Q.val,f i) (sum_le_sum (fun i q=>?_)) ?_
 · unfold f; split; next g=>
     set J:=columns Y x i; change ∑ j∈J,V j≤-p; apply le_trans (sum_le_sum fun j (v:j∈J)=> hx j (mem_filter.mp v).2.2); rw [sum_const,nsmul_eq_mul]; have hh:0<J.card:= card_pos.mpr ((col_tr Y x i).2 ((ht i q).1 g)); have hv:(1:ℝ)≤ J.card:= Nat.one_le_cast.mpr hh; nlinarith
   next g=>
     have he:columns Y x i=∅:= not_nonempty_iff_eq_empty.mp (fun t=>g ((ht i q).2 ((col_tr Y x i).1 t))); unfold W stopL; rw [he,sum_empty]
 unfold f; rw [←sum_filter,sum_const, show (Q.val.filter (· ∈ U))= U from ?_, nsmul_eq_mul]; swap; · ext i; exact (by rw [mem_filter]; exact and_iff_right_of_imp (fun k=>hu k))
 change ↑U.card * -p≤ -(U.card:ℝ) * p; rw [neg_mul,mul_neg] -- done
end Pour
end YM.CF.BProof.Cabinet
