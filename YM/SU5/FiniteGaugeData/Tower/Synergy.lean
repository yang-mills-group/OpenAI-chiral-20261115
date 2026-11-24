import YM.SU5.FiniteGaugeData.Tower.Multigrid
/- Joint ergodic powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Set Function Filter Metric Finset
open scoped Topology NNReal InnerProductSpace BigOperators Classical
namespace Average
variable {A B:Type*}[Fintype A][Fintype B]{H:Hilbert}
-- ordered products with deterministic links can be packaged as personal moves
-- in each M_i. Last product acts on vacuum
noncomputable def ordered (t:List A)(f:A→ H.Op):H.Op:= t.foldr (fun i (x:H.Op) => (f i).comp x) (ContinuousLinearMap.id ℂ H)
lemma orderly(i:A)(t:List A)(f:A→H.Op)(v:H):ordered (i::t) f v=f i (ordered t f v):=rfl
omit [Fintype A] in
lemma order_eq(t:List A)(f g:A→H.Op)(h:∀i∈t,f i=g i):ordered t f=ordered t g:=by induction t with
| nil=>rfl
| cons i t ih=>
   have hf:=ih (fun j a=>h _ (List.Mem.tail _ a)); unfold ordered at *
   simpa [hf,h _ (List.Mem.head ..)]
-- tail invariant to i, use dummy branch
lemma posts[Nonempty B](t:List A)(h:t.Nodup)(F:A→ B→ H.Op)(v:H):
 center (fun w:A→B=> ordered t (fun i=>F i (w i)) v)=ordered t (fun i=> center (F i)) v:=by
 induction t with
 | nil=>change center (fun _ : A→ B=>v)=v; exact constant v
 | cons i t ih=>
    let c:B:= Classical.arbitrary _
    let E:=Equiv.funSplitAt i B
    obtain ⟨z,ht⟩:=List.nodup_cons.mp h
    let g(p:Other A i→B):= E.symm (c,p)
    let f(p:Other A i→B):H:=ordered t (fun j=> F j (g p j)) v
    have hF(w:B)(p:Other A i→B): ordered t (fun j=>F j (E.symm (w,p) j)) v=f p:=by
       unfold f; rw [order_eq t _ (fun j=>F j (g p j))]; intro j k; have ht:j≠i:=fun a=>z (a ▸ k); unfold E g E; simp [ht]
    have hv: center f=ordered t (fun i=> center (F i)) v:=by
       rw [← ih ht,point i]; simp_rw [(show ∀ a:B,∀ b : Other A i→B, ordered t (fun j => F j (((Equiv.funSplitAt i B).symm (a,b)) j)) v=f b from hF), constant]
    rw [point i,orderly]; simp_rw [orderly, (show ∀ a:B,∀ b : Other A i→B, ordered t (fun j => F j (((Equiv.funSplitAt i B).symm (a,b)) j)) v=f b from hF)]; simp only [stops, natural]; rw [hv]
    exact natural (F i) (ContinuousLinearMap.apply ℂ H _) -- here H.Op, apply signature apply ℂ H codomain H.Op?
#check ContinuousLinearMap.apply
-- nonuniform jitter τ index also externally averaged after. uniformize
lemma by_choice {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y]{Z:ℕ→ Type*}[∀n,Fintype (Z n)][∀n,Nonempty (Z n)]
    (f:(n:ℕ)→Z n→ Y)(v:Y)(h:∀ u : (n:ℕ)→ Z n,Tendsto (fun i=>f i (u i)) atTop (𝓝 v)): Tendsto (fun i=>center (f i)) atTop (𝓝 v):=by
 -- diagonal choice yields uniform error at n
 apply Metric.tendsto_nhds.mpr; intro ε e
 have hE:∀ᶠ n:ℕ in atTop, ∀ i:Z n,dist (f n i) v≤ ε/2:=by
    classical
    by_contra! hu
    let w(n):Z n:= if h:∃ i:Z n,ε/2<dist (f n i) v then Classical.choose h else Classical.arbitrary _
    have ht:= Metric.tendsto_nhds.mp (h w) (ε/2) (by positivity)
    have hit:∀ᶠ n in atTop,∀ i:Z n,dist (f n i) v ≤ε/2:=by
       filter_upwards [ht] with n v i
       by_contra! hg; have hx:=Classical.choose_spec (show ∃ i:Z n,ε/2 <dist (f n i) _ from ⟨_,hg⟩)
       unfold w at v; rw [dif_pos (show ∃ i:Z n,ε/2<dist (f n i) _ from ⟨_,hg⟩)] at v; linarith
    exact hu (hit.mono (fun n h ⟨i,w⟩ => not_lt_of_ge (h i) w))
 filter_upwards [hE] with i t
 nth_rw 1 [show v=center (fun _ : Z i=>v) from (constant v).symm]
 exact lt_of_le_of_lt (norm_dist t) (half_lt_self e)
end Average

open Average
variable {A:Type*}{H:Hilbert}
structure Console (A:Type*)(H:Hilbert) extends Moving A H where
 Moment : ℕ → H.Op
 shrinking : ∀i,‖Moment i‖ ≤1
 steady: H.Op
 wave(i:H) : Tendsto (fun n=>Moment n i) atTop (𝓝 (steady i))
 -- s.a. etc separate package latter
 flip(i j a): (Moment i).comp ((toMoving.move j).wind a)=((toMoving.move j).wind a).comp (Moment i)
 rise:Moment 0=ContinuousLinearMap.id ℂ H
namespace Console
variable (C:Console A H)(p:List A)
set_option quotPrecheck false
local notation "J"=>C.toMoving
local notation "U" l:max=> (J).gallery p l
local notation "Y"=> (J).pause p
include C
lemma stage(n:A)(a:ℤ): ((J).move n|>.wind a).comp C.steady=C.steady.comp ((J).move n|>.wind a):=by -- i remove
 ext1 x
 let G:=((J).move n|>.wind a)
 refine tendsto_nhds_unique (f:=fun i=> G (C.Moment i x)) (G.continuous.continuousAt.tendsto.comp (C.wave _)) ?_
 have e(i:ℕ):G (C.Moment i x)=C.Moment i (G x):= by rw [←ContinuousLinearMap.comp_apply,(C.flip i n a).symm]; rfl
 simp_rw [e]; exact C.wave _
noncomputable def sky:H.Op:=C.steady.comp Y
lemma steady_lives {x:H}(h: x∈ (J).aligned p): C.steady x∈ (J).aligned p:=by
 apply (J).aligned_ok.mpr
 intro i u v; rw [←ContinuousLinearMap.comp_apply,C.stage i v,ContinuousLinearMap.comp_apply, (J).aligned_ok.mp h i u v]
lemma frozen (x:H)(v:A→ℤ):(U v) (C.sky p x)=C.sky p x:=by
 change (U v) (C.steady (Y x))=_; rw [←ContinuousLinearMap.comp_apply (U v), Moving.inter (J) _]; swap; · exact fun i v=>C.stage i v
 change C.steady ((U v) (Y x))=_; rw [Moving.stable _ _ _ _ _ (List.Subset.refl p)];rfl

variable [Fintype A]
-- one gap belongs to earlier than current cluster, C.Moment(ground) only paid in limit.
-- j time jitters → supply q varying independently, in applications q deterministic for now
noncomputable def personally (c:A→ℤ)(t:ℕ)(B:H.Op):H.Op:= (C.Moment t).comp (((U c).comp B).comp (U (-c)))
private lemma per(i:A→ℤ)(t:ℕ)(B:H.Op)(x:H): (C.personally p i t B) x=C.Moment t ((U i) (B ((U (-i)) x))):=rfl
private lemma per_le (i:A→ℤ)(t:ℕ)(B:H.Op): ‖C.personally p i t B‖≤ ‖B‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
 intro x; rw [per]; apply (ContinuousLinearMap.le_opNorm ..).trans; rw [Moving.rigid (J)]
 refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (C.shrinking _)) ((B.le_opNorm _).trans_eq ?_); rw [Moving.rigid (J)]

lemma lagZ {D:ℕ→ H.Op}{b:ℝ}(h:∀i,‖D i‖≤ b){y:ℕ→H}{x:H}(u:Tendsto y atTop (𝓝 x)){z:H}(q:Tendsto (fun i=>D i x) atTop (𝓝 z)):Tendsto (fun i=> D i (y i)) atTop (𝓝 z):=by
 apply Metric.tendsto_nhds.mpr; intro ε e; let k:=ε/(2*(b+1)); have hb:0≤b:=(norm_nonneg _).trans (h 0); have he:0<k:=by unfold k; positivity
 have ht:b*k< ε/2:=by have hv:k*(2*(b+1))=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
 filter_upwards [Metric.tendsto_nhds.mp u k he,Metric.tendsto_nhds.mp q (ε/2) (by positivity)] with i h1 h2
 apply lt_of_le_of_lt (dist_triangle _ (D i x) _)
 have hp:dist (D i (y i)) (D i x) ≤ b*k:=by
    rw [dist_eq_norm,←map_sub]; apply (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (h i) _ (norm_nonneg _) hb); rw [←dist_eq_norm]; exact h1.le
 linarith

-- arbitrary car labels S finitely enumerable, ordered in a line L. supply
-- arbitrary widths vs n for each gap; include before first (dummy enormous
-- gap, Ω doesn't see it), no winding bound on centers.
variable {S:Type*}[Fintype S]
open Moving
local notation "go" i:max z:max=>Moving.crew i z
local notation "car" v:max i:max x:max=>C.personally p v i x
lemma train (keys : p.Nodup)(l:List S)(l0:l.Nodup)(B:S→H.Op)(T:S→ℕ→ℕ)(h:∀i:S,Tendsto (T i) atTop atTop)(D:S→ℕ→A→ℤ)
 (v:H)(w: ∀i:A→ℤ,(U i) v=v):
 Tendsto (fun n:ℕ=>Average.center (fun q:S→A→Fin (n+1)=> Average.ordered l (fun s=> C.personally p (Moving.crew n (D s n) (q s)) (T s n) (B s)) v)) atTop (𝓝 (Average.ordered l (fun i=> C.sky p|>.comp (B i)) v)):=by
 let B₀(t:ℕ)(i:S):H.Op:=Average.center (fun c:A→ Fin (t+1)=> (car (Moving.crew t (D i t) c) (T i t) (B i)))
 have H0(i:S)(q:H)(hq:∀c:A→ℤ,(U c) q=q):Tendsto (fun n=>B₀ n i q) atTop (𝓝 (C.sky p (B i q))):=by
    let f(n:ℕ):=fun c:A→Fin (n+1)=>(U (Moving.crew n (D i n) c)) (B i q)
    have ht(n:ℕ):B₀ n i q=C.Moment (T i n) (Average.center (f n)):=by
       unfold B₀
       change ContinuousLinearMap.apply ℂ H q (Average.center (fun c:A→ Fin (n+1)=> car (Moving.crew n (D i n) c) (T i n) (B i)))=_
       rw [← Average.natural]; change Average.center (fun c=> (car (Moving.crew n (D i n) c) (T i n) (B i)) q)= _
       simp_rw [per,hq]; rw [Average.natural]
    simp_rw [ht]
    apply lagZ C (D:=fun n=>C.Moment (T i n)) (b:=1) -- args
    · intro i; apply C.shrinking
    · exact (J).median _ _ _ keys
    exact C.wave _ |>.comp (h i)
 have hb(i:S)(n:ℕ):‖B₀ n i‖≤‖B i‖:= Average.norm_worth (fun v=>C.per_le p _ _ _)
 have he:∀ l:List S,
    Tendsto (fun n:ℕ=> Average.ordered l (B₀ n) v) atTop (𝓝 (Average.ordered l (fun i=> C.sky p|>.comp (B i)) v))∧∀x:A→ℤ,(U x) (Average.ordered l (fun i=> C.sky p|>.comp (B i)) v)=Average.ordered l (fun i=> C.sky p|>.comp (B i)) v:=by
    intro k; induction k with
    | nil=> exact ⟨tendsto_const_nhds,w⟩
    | cons i k ih=>
       simp_rw [orderly]; constructor
       · exact lagZ C (hb i) ih.1 (H0 i _ ih.2)
       intro b; rw [ContinuousLinearMap.comp_apply,C.frozen]
 have ht:= (he l).1
 apply ht.congr; intro n
 exact (Average.posts l l0 (fun i c=> C.personally p (Moving.crew n (D i n) c) (T i n) (B i)) v).symm
end Console
end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.Console.train
