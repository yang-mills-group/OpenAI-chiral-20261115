import YM.CF.Moen.Bard
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Moen.Space
open Function Filter Topology Metric Finset
open scoped Classical BigOperators
variable {I: Type*}[Fintype I][DecidableEq I][Nonempty I]
abbrev Δ(I:Type*)[Fintype I]:= (stdSimplex ℝ I)
local notation "N"=> Fintype.card I
local notation "C"=> Δ I
variable {ε:ℝ}
abbrev Coins (F:Finset (Δ I)):= Lex (ℝ× Fin (Fintype.card (I⊕ F)))
section
variable (F:Finset (Δ I))
abbrev πP(i:I)(x:I⊕F):ℝ:= Sum.elim (fun j=>if j=i then -1 else 2) (fun j:F=>j.val.val i) x
def stake : Gift I (I⊕ F) (Coins F) where
 corner:= Function.Embedding.inl
 score i x:= toLex (πP F i x,Fintype.equivFin _ x)
 inj i _ _ t:=(Fintype.equivFin _).injective (congrArg Prod.snd (toLex.injective t))
 low i x h:= by
    apply Prod.Lex.toLex_lt_toLex.mpr; left; cases x
    next j=> have hp:j≠i:=fun b=> h (by rw [b]; rfl); change πP F i (.inl i)<πP F i (.inl j); norm_num [πP,hp]
    next j=> change πP F i (.inl i) < j.val.val i; refine lt_of_lt_of_le ?_ (j.val.property.1 i); simp [πP]
 high i j u x v:=by
    apply Prod.Lex.toLex_lt_toLex.mpr; left; cases x
    next a=> exact False.elim (v ⟨a,rfl⟩)
    next a=> change a.val.val i< πP F i (.inl j); refine lt_of_le_of_lt (mem_Icc_of_mem_stdSimplex a.val.property i).2 ?_; norm_num [πP,Ne.symm u]
local notation "G"=> stake F
variable {X: Finset (I⊕ F)}(d:X.Nonempty)
abbrev winL (i:I):=πP F i (Gift.win G d i)
def cut (i:I):= if Sum.inl i∈X then 0 else winL F d i
lemma mask_v (x:F)(p:Sum.inr x∈X)(i:I):0 ≤ cut F d i∧ cut F d i ≤ x.val.val i:=by
 unfold cut; split
 · exact ⟨le_rfl,x.val.property.1 _⟩
 next v=>
    have ht(y z)(u:(stake F).score i y≤(stake F).score i z):πP F i y≤πP F i z:=le_of_not_gt (fun g=>not_lt.mpr u (Prod.Lex.toLex_lt_toLex.mpr (Or.inl g)))
    refine ⟨?_,ht _ (.inr x) ((stake F).floor _ _ p i)⟩; unfold winL; cases l:Gift.win G d i
    next y=> have he:y≠i:=fun t=> v (by rw [←t,←l]; exact Gift.enter _ _ i); simp [πP,he]
    next y=> exact y.val.property.1 i
lemma highSum (u:0 < ε) (v:∀ x:Δ I,∃ i:F,dist x i.val < ε)(x:F)(p:Sum.inr x∈X)(he:(stake F).good X): 1-N*ε≤∑ i:I,cut F d i:=by
 apply le_of_not_gt; intro m; let q:=cut F d; let t:=(1-∑ i:I,q i)/N; have hu:0<(N:ℝ):=by exact_mod_cast Fintype.card_pos
 have hx: ε<t:= (lt_div_iff₀ hu).mpr (by unfold q; linarith [mul_comm ε (N:ℝ)])
 let y:Δ I:= ⟨fun i=> q i+t,fun i=> add_nonneg (mask_v F d x p i).1 (u.trans hx).le,by rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_comm]; unfold t; rw [div_mul_cancel₀ _ (ne_of_gt hu)]; ring⟩; obtain ⟨j,w⟩:=v y
 obtain ⟨i,r⟩:=he (.inr j); by_cases a: Sum.inl i∈X
 · exact not_le.mpr (Gift.low G i (.inr j) (by change (.inr j:I⊕F)≠ .inl i; simp)) (r _ a)
 have hw:=dist_pi_le_iff u.le|>.mp (show dist y.val j.val.val≤ε from w.le) i; rw [Real.dist_eq,abs_le] at hw; change _∧ q i+t-j.val.val i ≤ ε at hw; exact not_le.mpr (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show winL F d i < j.val.val i from by unfold q cut at hw; rw [if_neg a] at hw; linarith [hw.2]))) (r _ (Gift.enter G d i))
lemma ticket (hp: 2 ≤ N) (u:0<ε)(v:∀ x:Δ I,∃ i:F,dist x i.val < ε)(f:F→ I): ∃ x:F,∀ i:I, x.val.val i≤ N*ε ∨ ∃ y:F,f y=i ∧ dist x.val y.val ≤ N*ε:=by
 let s:I:= Classical.arbitrary _; let g:=Sum.elim id f; obtain ⟨Y,p,t,b⟩:=Gift.sand G s g (fun i=> rfl) hp; have hx:Y.Nonempty:=card_pos.mp (by omega)
 have h:∃ x:F, Sum.inr x∈Y:=by
    by_contra q; push_neg at q; let z:Δ I:= ⟨_,single_mem_stdSimplex ℝ s⟩; obtain ⟨i,w⟩:= v z; obtain ⟨c,r⟩:= p (Sum.inr i); obtain ⟨x,m,u⟩:=mem_image.mp (show c∈Y.image g by rw [b]; simp); cases x; next j=> subst c; exact not_le.mpr (Gift.low G j (.inr i) (by change (.inr i : I⊕F) ≠ .inl j; simp)) (r _ m)
    next j=> exact q j m
 obtain ⟨x,r⟩:=h; refine ⟨x,fun i=>?_⟩; have h0:= highSum F hx u v x r p; let l:= cut F hx; have hf(o:F)(m: Sum.inr o∈Y)(k:I):l k ≤ o.val.val k ∧ o.val.val k ≤ N*ε+l k:=by
    have ht:= single_le_sum (s:=univ) (f:=fun j=> o.val.val j-l j) (fun j _=> sub_nonneg.mpr (mask_v F hx o m j).2) (mem_univ k); rw [sum_sub_distrib, o.val.property.2] at ht; refine ⟨(mask_v F hx o m k).2,?_⟩; change _≤∑ i:I,l i at h0; linarith
 by_cases hv: Sum.inl i∈Y
 · left; simpa [l,cut,hv] using (hf x r i).2
 right; obtain ⟨y,u',b'⟩:=mem_image.mp (show i∈ Y.image g by rw [b]; simp); cases y with
 |inl j=> exact False.elim (hv ((show j=i from b') ▸ u'))
 |inr j=> refine ⟨j,b', dist_pi_le_iff (by positivity)|>.mpr (fun k=> ?_)⟩; change dist (x.val.val k) (j.val.val k) ≤_; rw [Real.dist_eq,abs_le]; obtain ⟨w,s⟩:= hf x r k; obtain ⟨b,d⟩:= hf j u' k; constructor <;>linarith
end
variable (f:Δ I→Δ I)(k:Continuous f)
include k
lemma key (hp:2 ≤ N)(u:0 < ε):∃ x:Δ I,∀ i:I,x.val i ≤ (f x).val i + ε:=by
 obtain ⟨t,t0,t'⟩:=Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous k) (ε/2) (by linarith); let d:=min t (ε/2)/(N+1); have he:0 < min t (ε/2):= lt_min t0 (by linarith); have hu:0<d:=by unfold d; positivity
 obtain ⟨V,w,v⟩:=Metric.totallyBounded_iff.mp (isCompact_univ (X:=Δ I)).totallyBounded _ hu; let F:=w.toFinset; have hz(x:Δ I):∃ i:F,dist x i.val<d:=by obtain ⟨i,p⟩:= Set.mem_iUnion.mp (v (Set.mem_univ x)); obtain ⟨h,u⟩:=Set.mem_iUnion.mp p; exact ⟨⟨i,w.mem_toFinset.mpr h⟩,u⟩
 have hf(x:F):∃ i:I,x.val.val i ≤ (f x.val).val i:=by
    by_contra m; push_neg at m; have hx:=sum_lt_sum_of_nonempty (s:=univ) univ_nonempty (fun i _=> m i); rw [(f x.val).property.2,x.val.property.2] at hx; exact lt_irrefl _ hx
 choose E Z using hf; obtain ⟨x,p⟩:= ticket F hp hu hz E; have hl: (N:ℝ)*d< min t (ε/2):=by have ht:d*(N+1)=min t (ε/2):=div_mul_cancel₀ _ (by positivity); linarith
 refine ⟨x.val,fun i=>?_⟩; rcases p i with w|⟨y,a,b⟩; · have ht: min t (ε/2)≤ ε/2:= min_le_right ..; linarith [(f x.val).property.1 i]
 have hk:= dist_pi_le_iff (show (0:ℝ)≤ ε/2 by linarith)|>.mp (show dist (f x.val).val (f y.val).val ≤ ε/2 from (t' (b.trans_lt (hl.trans_le (min_le_left ..)))).le) i; rw [Real.dist_eq,abs_le] at hk; obtain ⟨g,m⟩:=hk; have hx:= dist_pi_le_iff (show (0:ℝ) ≤ ε/2 by linarith)|>.mp (show dist x.val.val y.val.val ≤ ε/2 from b.trans (hl.le.trans (min_le_right ..))) i; rw [Real.dist_eq,abs_le] at hx; have he := Z y; rw [a] at he; linarith [hx.2]
lemma spen (p: 2≤ N):∃ x:Δ I,f x=x:=by
 obtain ⟨t,h,g,k'⟩:=exists_seq_strictAnti_tendsto (0:ℝ); choose V Z using fun i=> key f k p (g i); obtain ⟨x,a,s,m,l⟩:=isCompact_univ.isSeqCompact (fun i=> Set.mem_univ (V i)); have he(i:I):x.val i ≤ (f x).val i:=by
    let g(i:I)(y:Δ I):= y.val i; have hg(i):Continuous (g i):= (continuous_apply i).comp continuous_subtype_val; simpa only [add_zero] using (le_of_tendsto_of_tendsto ((hg i).continuousAt.tendsto.comp l) (((hg i).continuousAt.tendsto.comp (k.continuousAt.tendsto.comp l)).add (k'.comp m.tendsto_atTop)) (Eventually.of_forall fun z=> Z (s z) i)) -- contraction
 refine ⟨x,Subtype.ext (funext fun i=> le_antisymm ?_ (he i))⟩; apply le_of_not_gt; intro u; have hx:= sum_lt_sum (s:=univ) (fun i _=> he i) ⟨i,mem_univ _,u⟩; rw [x.property.2,(f x).property.2] at hx; exact lt_irrefl _ hx
end YM.CF.Moen.Space
