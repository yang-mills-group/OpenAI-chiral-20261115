import YM.SU5.Relativistic.Hewn
import YM.SU5.Relativistic.TangentPrec
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count

def vivo:= univ.filter (how L)
def brick (i:T_):= (livelies W_).image (raise L i)
def mitt (i:T_) := ((univ:Finset (Link W_)).filter indoors).image (raise L i)
def batchIn:= (univ:Finset (Site C)).biUnion (brick L)
def wires: Finset (Link N):= vivo L \ batchIn L
lemma rise_b(i:T_): Injective (raise L i):= fun x y h=>by have he:=congrArg (vowel L) h; rw [vowel_p,vowel_p] at he; simpa using he
lemma brick_in (i:T_):brick L i⊆ mitt L i:= image_mono (raise L i) (Finset.filter_subset_filter _ (subset_univ _))
lemma brick_v (i:T_): brick L i⊆ vivo L:=by rintro j h; obtain ⟨x,p,rfl⟩:=mem_image.mp h; obtain ⟨s,t⟩:=mem_filter.mp p; exact mem_filter.mpr ⟨mem_univ _,(how_in L i x t).mpr (mem_filter.mp s).2⟩
lemma brick_b (i:T_):brick L i⊆ batchIn L:= subset_biUnion_of_mem (brick L) (mem_univ i)
lemma batch_in: batchIn L⊆ vivo L:=by intro i h; obtain ⟨j,u,t⟩:=mem_biUnion.mp h; exact brick_v L j t
lemma batch_card: (batchIn L).card=C.val^4*(livelies W_).card:=by
 unfold batchIn; rw [card_biUnion]; simp_rw [brick,card_image_of_injective _ (rise_b ..)]; simp [Lattice.site_card]
 intro i hi j hj x; change Disjoint (brick L i) (brick L j); rw [Finset.disjoint_left]; intro v t w; obtain ⟨y,r,rfl⟩:=mem_image.mp t; obtain ⟨z,p,o⟩:=mem_image.mp w; exact x (by have e:=congrArg (vowel L) o; simp at e; exact e.1.symm)
lemma mitt_d (i j:T_)(e:i≠j) : Disjoint (mitt L i) (mitt L j):=by rw [Finset.disjoint_left]; intro v t w; obtain ⟨y,r,rfl⟩:=mem_image.mp t; obtain ⟨z,p,o⟩:=mem_image.mp w; exact e (by have h:=congrArg (vowel L) o; simp at h; exact h.1.symm)
lemma wire_d (i:T_): Disjoint (mitt L i) (wires L):=by
 rw [Finset.disjoint_left]; intro v t w; obtain ⟨z,p,rfl⟩:=mem_image.mp t; obtain ⟨u,x⟩:=mem_sdiff.mp w; have hp:= (mem_filter.mp p).2
 apply x; apply brick_b L i; exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ z,(how_in L i z hp).mp (mem_filter.mp u).2⟩,hp⟩)
lemma vivot : wires L ∪ batchIn L=vivo L:= sdiff_union_of_subset (batch_in L)
lemma zero_pin {Y:Side} : (generators Y).card=4:=by
 apply le_antisymm pin_le; rw [←show Fintype.card Axis=4 from rfl,← Finset.card_univ (α:=Axis)]; let f(i:Axis):Link Y:=(- step i,i); have he:Injective f:=fun i j e=>congrArg Prod.snd e
 rw [←card_image_of_injective (f:=f) _ he]; refine card_le_card ?_; intro v t; obtain ⟨i,h,rfl⟩:=mem_image.mp t; exact mem_filter.mpr ⟨mem_univ _,cut_part Y i⟩
lemma countLess {Y:Side} : (pivots Y)ᶜ.card=Y.val^4+3:=by
 have h:=all_count (N:=Y); rw [zero_pin] at h; have he:= tree_card (N:=Y); have hp:=card_compl_add_card (pivots Y); rw [show Fintype.card (Link Y)=4*Y.val^4 by simp [Fixed.Pivots.Link,Edge,Lattice.site_card,Axis,Nat.mul_comm]] at hp; omega
lemma viva_card : (vivo L).card=(pivots N).card:=by
 let f(i:Link C):=raise L i.1 (seed L i.1 i.2, i.2); have hf:Injective f:=by intro i j h; rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩; have e:=congrArg (vowel L) h; unfold f at e; simp at e; rw [e.1,e.2.2]
 let c:=((univ:Finset T_)×ˢ treeLinks W_).map (lifted L); let v:=((pivots C)ᶜ).image f
 have hc(i:Link N) : i∈ c→ indoors (vowel L i).2 ∧ i∉vivo L:=by
    rintro x; obtain ⟨⟨p,y⟩,w,rfl⟩:=mem_map.mp x; have hp:Tree y:= (mem_filter.mp (mem_product.mp w).2).2; refine ⟨?_,?_⟩; · change indoors (vowel L (raise L p y)).2; rw [vowel_p]; exact hp.1
    intro g; exact ((how_in L p y hp.1).mp (mem_filter.mp g).2).1 hp
 have hv(i:Link N): i∈v→ ¬indoors (vowel L i).2∧i∉vivo L:=by
    intro e; obtain ⟨p,t,rfl⟩:=mem_image.mp e; have he: ¬indoors (seed L p.1 p.2,p.2):=endW.mpr (seed_j ..); unfold f; rw [vowel_p]; refine ⟨he,fun g=> (mem_compl.mp t) (mem_filter.mpr ⟨mem_univ _,?_⟩)⟩; exact ((how_out _ _ _ he).mp (mem_filter.mp g).2).resolve_right (not_not_intro rfl)
 have hD:(vivo L)ᶜ=c∪v:=by
    ext x; refine ⟨?_,?_⟩
    · intro p; obtain ⟨⟨i,j⟩,rfl⟩:= (vowel L).symm.surjective x; have he: ¬ how L (raise L i j):=fun g=> (mem_compl.mp p) (mem_filter.mpr ⟨mem_univ _,g⟩)
      by_cases h:indoors j; · apply mem_union_left; exact mem_map_of_mem _ (show (i,j)∈ (univ:Finset T_)×ˢ treeLinks W_ from mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ j, not_not.mp (mt ((how_in L _ _ h).mpr ∘ (indoors_m _ h).mpr) he)⟩⟩) -- Iff mpr not function comp? test
      rcases j with ⟨x,y⟩; obtain ⟨hx,g⟩:=not_or.mp (mt (how_out _ _ _ h).mpr he); have he':x=seed L i y:=not_not.mp g; apply mem_union_right; subst x; exact mem_image_of_mem f (show (i,y)∈ (pivots C)ᶜ from mem_compl.mpr (fun x=>hx (mem_filter.mp x).2))
    intro e; exact mem_compl.mpr ((mem_union.mp e).elim (fun g=>(hc x g).2) fun g=>(hv x g).2)
 have hz:(vivo L)ᶜ.card=(pivots N)ᶜ.card:=by
    rw [hD,card_union_of_disjoint (disjoint_left.mpr fun {x} p g=>(hv x g).1 (hc x p).1),countLess]; unfold c v; rw [card_map,card_product,card_image_of_injective _ hf,countLess,card_univ,Lattice.site_card,L.exact_size,mul_pow]; rw [←tree_card (N:= L.count)]; ring
 have hv:=card_compl_add_card (vivo L); have hh:=card_compl_add_card (pivots N); omega

-- billboard count link external
lemma wool_links(Y:Side)(i:Axis)(v:Per Y): ((univ:Finset (Site Y)).filter (fun k=> k i=v)).card ≤ Y.val^3:=by
 let S:=(univ:Finset (Site Y)).filter (fun k=> k i=v)
 let T:=(univ:Finset Axis).erase i; let f(x:Site Y)(a:↥T):= x a
 have h:S.card ≤ Fintype.card (↥T→Per Y):= by
   rw [←card_image_of_injOn (s:=S) (f:=f) ?_]; exact card_le_univ _
   intro x v' y t e; funext j; obtain rfl|q:=eq_or_ne j i; · exact (mem_filter.mp (show x∈S from v')).2.trans (mem_filter.mp (show y∈S from t)).2.symm
   exact congrFun e ⟨j,mem_erase.mpr ⟨q,mem_univ j⟩⟩
 refine h.trans_eq ?_; simp [Per,T,Axis]
lemma woolV : (wires L).card ≤ 4*C.val^4*L.count.val^3:=by
 let S(i:Axis):= ((univ:Finset (Site C))×ˢ ((univ:Finset P_).filter (fun x=> x i=peak W_ i))).image (fun p=>raise L p.1 (p.2,i)); have ht: wires L⊆ univ.biUnion S:=by
    intro j p; obtain ⟨⟨x,y,i⟩,rfl⟩:=(vowel L).symm.surjective j; apply mem_biUnion.mpr; refine ⟨i,mem_univ _,?_⟩; apply mem_image.mpr; refine ⟨(x,y),mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,endW.mp fun g=>?_⟩⟩,rfl⟩; exact Finset.disjoint_left.mp (wire_d L x) (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,g⟩)) p
 have hv(i:Axis):(S i).card ≤ C.val^4*L.count.val^3:=by refine card_image_le.trans ?_; rw [card_product,card_univ,Lattice.site_card]; apply Nat.mul_le_mul_left; apply wool_links
 refine (card_le_card ht).trans ((card_biUnion_le).trans ((Finset.sum_le_sum fun i _=> hv i).trans_eq ?_)); simp [Axis,Nat.mul_assoc]
open MinorPins
-- Membership reduces if Closed
lemma known_s {G:Type}[AddCommGroup G]{H:Set G}(t:H= (⊥:AddSubgroup G) ∨ ∃ S:AddSubgroup G,H=S)(F:Bond N→G)(x:Closed F)(p:2 ≤ C.val) (b:2≤N.val)(q:∀ i∉ vivo L,F i∈ H): ∀ i,F i∈H:=by
 obtain ⟨A,rfl⟩: ∃S:AddSubgroup G,H=S:= t.elim (fun i=>⟨⊥,i⟩) id; change ∀ i,F i∈A
 suffices he:∀ k:ℕ,∀ i:Bond N,ranking L i=k→F i∈A by exact fun i=> he _ _ rfl
 intro k; induction k using Nat.strong_induction_on with
 | h k ih =>
  intro i hi; by_cases u:i∈ vivo L; swap; · exact q i u
  obtain ⟨⟨y,⟨⟨a,c⟩,he⟩⟩,w,g⟩:= pays L p i (mem_filter.mp u).2; have hp(r:Link N)(t:r∈ window y a c)(e:r≠i): F r∈A:=by
    by_cases z:r∈vivo L; · exact ih _ (hi ▸ g _ t e (mem_filter.mp z).2) _ rfl
    exact q r z
  have hv: a≠c:=he.ne; have hx:y ≠ y+step c:=step_dist b y c; have hw:y ≠ y+step a:=step_dist b y a
  have ht:F (y,a)+F (y+step a,c)=F (y+step c,a)+F (y,c):= sub_eq_zero.mp (x (y,⟨(a,c),he⟩))
  change i∈ window y a c at w; simp only [window,mem_insert,mem_singleton] at w; rcases w with rfl|rfl|rfl|rfl
  · exact (A.add_mem_cancel_right (hp (y+step a,c) (by simp [window]) (by simp [hv.symm]))).mp (ht.symm ▸ A.add_mem (hp _ (by simp [window]) (by simp [hx.symm])) (hp _ (by simp [window]) (by simp [hv.symm]))) -- tune mp
  · exact (A.add_mem_cancel_left (hp (y,a) (by simp [window]) (by simp [hv]))).mp (ht.symm ▸ A.add_mem (hp _ (by simp [window]) (by simp [hv])) (hp _ (by simp [window]) (by simp [hw])))
  · exact (A.add_mem_cancel_right (hp (y,c) (by simp [window]) (by simp [hv.symm]))).mp (ht ▸ A.add_mem (hp _ (by simp [window]) (by simp [hx])) (hp _ (by simp [window]) (by simp [hv.symm])))
  exact (A.add_mem_cancel_left (hp (y+step c,a) (by simp [window]) (by simp [hv]))).mp (ht ▸ A.add_mem (hp _ (by simp [window]) (by simp [hv])) (hp _ (by simp [window]) (by simp [hw.symm])))

variable (J:Type)[Fintype J][DecidableEq J]
def sheet:= (vivo L)×ˢ(univ:Finset J)
lemma marksG(p:2≤ C.val)(h:2≤N.val): Grates (sheet L J) (closedC J N):=by
 let T:=sheet L J; let A:=closedC J N
 have hf(f:Bond N×J→ℝ)(g:f∈ A)(t:hide T f=0): f=0:=by
   funext i; exact (show f i∈ (⊥:AddSubgroup ℝ) from known_s L (Or.inl rfl) (fun k=> f (k,i.2)) (g i.2) p h (fun j e=> (show f (j,i.2)=0 from congrFun t ⟨(j,i.2),mem_compl.mpr (fun k=> e (mem_product.mp k).1)⟩)) i.1)
 have hp:Module.finrank ℝ A=Tᶜ.card:=by
    rw [← (grates (J:=J) N h).pin_card]; rw [card_compl,card_compl,show (interior J N).card=T.card from by unfold GaugeFlux.interior T sheet; rw [card_product,card_product,viva_card]]
 have hz(g:↥Tᶜ→ℝ): ∃ f∈ A, hide T f=g:=by
    let F:= LinearMap.pi fun i:↥Tᶜ=> (LinearMap.proj (R:=ℝ) i.val).comp A.subtype
    have he:Module.finrank ℝ A=Module.finrank ℝ (↥Tᶜ→ℝ):= (hp.trans (by simp only [Module.finrank_pi,Fintype.card_coe] -- tune
      ))
    have hx: Injective F:= fun x y t=>Subtype.ext (sub_eq_zero.mp (hf _ (A.sub_mem x.property y.property) (funext fun i=> (sub_eq_zero.mpr (congrFun t i) : x.val i-y.val i=0))))
    obtain ⟨i,w⟩:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mp hx g; exact ⟨i.val,i.property,w⟩
 refine ⟨hf,hz,fun f v=>?_⟩; obtain ⟨x,b,g⟩:= hz f; let P:= (Int.castAddHom ℝ).range; refine ⟨x,b,fun i=>?_,g⟩
 have he: x i∈P:= known_s L (Or.inr ⟨P,rfl⟩) (fun k=>x (k,i.2)) (b i.2) p h (fun j t=>by
    let l:↥Tᶜ:=⟨(j,i.2),mem_compl.mpr (fun e=>t (mem_product.mp e).1)⟩
    obtain ⟨a,v⟩:= v l; exact ⟨a,((congrFun g l).trans v).symm⟩) i.1
 obtain ⟨y,h⟩:= he; exact ⟨y,h.symm⟩
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.marksG
