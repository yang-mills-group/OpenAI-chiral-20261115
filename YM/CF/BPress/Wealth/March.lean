import YM.CF.BPress.Sampler
import YM.CF.BPress.Wealth.Mercy
/-! Exact on all heavy fields in core and copy profiles. explicit H lemma. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix
variable {s:Side} {b:BandWidth}(X : Bands s b){T:Sheet.Atlas}{L y C C':ℝ}{a : ℕ}(F:Net s T L y C C' a) (i:X.Slates)(w:X.Sky)(V:Micro s)
open SU Net
lemma actor (u:X.Air) : F.roll X i w V (X.skylink u)=w u:= congrFun (F.roll_sky ..) u
lemma rep_pay (j:X.Index) (e:Link s) (p:e∈ X.pay j) : F.roll X i w V e=F.avgN X (X.atmospheric w) j (see (T:=T) (y:=y) X i (X.atmospheric w) j) e * V e:=by
 unfold Net.roll Net.play; rw [X.clear_coin _ _ _ _ p, Pi.mul_apply,F.chart_pay X i _ _ e p] -- tune placeholder F0

lemma fact_gap (t:Per s)(e:FlatLink s)(u : X.Index)(p:footTime X t u) : F.roll X i w V (fl t e)=anglePaid X y w V (fl t e):=by
 obtain ⟨k,h,rfl⟩:=time_depth X u t p; cases k with
 | zero =>
    let t:=X.depth u 0; let z:= X.dirichlet u; let j:=fl t e; have hx:z∈X.dc:=(X.dc_index ..).2 (X.b_zero ..|>.1); have v:j∈ X.pay z:= by unfold pay; rw [if_pos hx]; exact (X.mark z).crown_sub (X.crownD ..)
    change F.roll X i w V j= _; rw [rep_pay X F i w V _ j v]; unfold avgN anglePaid angleBeg; rw [if_pos hx,key_o,if_pos (X.coins_c z v)]; rfl -- tune
 | succ k=>
    let U:X.Air:= ((u,e.1),⟨k,h⟩,e.2); change F.roll X i w V (X.skylink U)= anglePaid X y w V (X.skylink U); rw [actor,anglePaid,angleBeg,key_depth, if_neg (Finset.disjoint_left.mp X.air_dis (show X.skylink U∈ X.air from mem_image_of_mem _ (mem_univ U)))]; simp
-- in copy collars either D (gets avgN=background) or N (gets tar...). requires k>=1 to avoid paid claim on faces. common proof param raw/pay at mark
lemma record_H (k:Per s)(x:FlatLink s)(j:X.Index)(d:ℕ)(g:0<d)(h:d < b.marked.val)(e:k=(X.mark j).rise d): fl k x ∈ X.pay j:=by
 let W:=X.mark j; have hv:d<W.n.val:=h; unfold pay; split; exact W.tang_in x|>.2 ⟨d,h.le,e⟩; exact W.banks_tem _|>.mpr (Or.inr ⟨d,h,g,_, congrArg (fun t=>fl t x) e⟩)
lemma fact_H (t:Per s)(e:FlatLink s)(u:X.Index) (g:station X t u) : F.roll X i w V (fl t e)=anglePaid X y w V (fl t e):=by
 rcases photo_collar X u (cloak_lt _) g with h|h
 · exact fact_gap X F i w V t e u h -- tune
 let f:= X.atmospheric w; let q:= X.mark u; let z:= X.mark (u+1); let J:Fin b.D:=⟨b.D-1,Nat.sub_one_lt b.D_pos.ne'⟩; have he:J.val+1=b.D:=Nat.sub_add_cancel b.D_pos; let U:X.Air:=((u,e.1),J,e.2); have ht:X.skylink U= fl (X.depth u b.D) e:=by change fl (X.depth u (J.val+1)) _=_; rw [he]
 have hp : cloak b < b.marked.val:= le_trans (by omega : cloak b≤ 2*cloak b) le_rfl |>.trans_lt (cloak_lt b)
 have frame (h:magtime X u t=b.D): angleBeg X y w (fl t e)=horizontal (X.depth u b.D) f e:= by unfold angleBeg; rw [EdgeKey_H,key_frame X t e u (k:=J) g (he.trans h.symm), horizontal,←ht]; exact (X.mat_atm w U).symm -- tune
 have none (h:magtime X u t=0): angleBeg X y w (fl t e)= background y (fl t e):=by unfold angleBeg; rw [EdgeKey_H, show keyV X t e=none from Option.not_isSome_iff_eq_none.mp fun p=> (((key_spec X t e u g).mp p) h)]; rfl
 rcases h with ⟨k,L,p,x⟩|⟨k,L,p,x⟩
 · have ha:= L.trans_lt hp; have hb:0 < b.marked.val-k:=Nat.sub_pos_of_lt ha; have hv:b.marked.val-k < b.marked.val:= Nat.sub_lt (b.marked.property) (Nat.pos_of_ne_zero p); have v:=record_H X t e u _ hb hv x
   rw [rep_pay X F i w V _ _ v,anglePaid,if_pos (X.coins_c u v)]; apply congrArg (· * V _); -- x direction tune
   by_cases w':u∈X.dc; unfold avgN; rw [if_pos w']; refine (none ?_).symm; rw [x,magfront X u L,if_pos w']; unfold avgN; rw [if_neg w',frame (by rw [x,magfront X u L, if_neg w',]), x]; let p:=(b.marked.val-k); let s:= F.template q (q.reads f) (see (T:=T) (y:=y) X i f u); change horizontal (q.rise p) s e= _; rw [show X.depth u b.D=X.stop u by rw [X.depth_D u,if_neg]; exact fun t=> w' ((X.dc_index u).mpr t), show X.stop u=q.last from rfl]; exact congrFun ((F.readH q _ _ hv.le).trans (F.tar_last q _ _ (show q.lip ≤ p from (by change b.marked.val-cloak b ≤ b.marked.val-k; omega)))) e
 have hv:= L.trans_lt hp; have v:=record_H X t e (u+1) k (Nat.pos_of_ne_zero p) hv x
 rw [rep_pay X F i w V _ _ v,anglePaid,if_pos (X.coins_c _ v)]; apply congrArg (· * V _); have p(u:X.Index): u+1∈X.dc ↔ ¬u∈X.dc:= by simp [X.prev_next u]
 by_cases g:u∈X.dc; unfold avgN; rw [if_neg ((p u).not.mpr (not_not_intro g)),frame (by rw [x,maglast X u L,if_pos g]),x,X.depth_D u,if_pos ((X.dc_index u).mp g)]; exact congrFun ((F.readH z _ _ hv.le).trans (F.tar_o z _ _ L)) e; unfold avgN; rw [if_pos ((p u).mpr g),none (by rw [x,maglast X u L,if_neg g])]

-- vertical reader in the same collars doesn't need h labels, just possible D noise. uncut precondition: exactly those k<=cloak depths cannot equal N-cut index. true L large; for L=4? k<1 => posterior vertical k=3; cut2; fine. etc.
lemma vertical_copy (j:X.Index)(k:ℕ)(t:k<b.marked.val)(h:k≠(X.mark j).cut)(x:Tri s):
 let e:= vl ((X.mark j).rise k) x; F.roll X i w V e=anglePaid X y w V e:=by
 intro e; unfold anglePaid angleBeg; rw [show edgeKey X e=none from EdgeKey_V .., show background y e=1 from normal_background ..]; unfold Option.elim; simp only [one_mul]; by_cases g:j∈X.dc
 · have he:e∈ X.pay j:= by unfold pay; rw [if_pos g]; exact (X.mark j).normal_in ..|>.mpr ⟨k,t,rfl⟩
   rw [if_pos (X.coins_c j he),rep_pay X F i w V j e he,avgN,if_pos g,show background y e=1 from normal_background ..,one_mul]
 have he:e∈ X.poles:= X.poles_s j (by rw [storesN,if_neg g]; exact (X.mark j).stores_eq.mpr ⟨k,t,h,x,rfl⟩); rw [if_neg (disjoint_left.mp X.pole_dis he)]; exact F.roll_hold X i w V _ he
lemma fact_V (t:Per s)(x:Tri s)(u:X.Index)(h:vl t x∈ inside (halo (cloak b) (X.gap u))) : F.roll X i w V (vl t x)=anglePaid X y w V (vl t x):=by
 rcases movie_collar X u (cloak_lt _) h with ⟨k,g,p⟩|⟨k,g,p⟩|⟨k,g,p⟩
 · have he:vl t x∈X.poles:= X.poles_g u ((X.gaps_b ..).2 ⟨k,g,x,by rw [p]⟩); rw [anglePaid,angleBeg,EdgeKey_V, if_neg (disjoint_left.mp X.pole_dis he),normal_background,mul_one]; exact F.roll_hold X i w V _ he
 · rw [p]; have he:= cloak_lt b; apply vertical_copy X F i w V u (b.marked.val-(k+1)) ?_ ?_ x; omega; change _≠ b.marked.val/2; -- may fail L=4? ok
   unfold cloak at *; omega
 rw [p]; have he:= cloak_lt b; apply vertical_copy X F i w V _ k (by omega) _; change _≠ b.marked.val/2; unfold cloak at *; omega

lemma marches : Mission X y w V (F.roll X i w V):= by
 refine ⟨fun j u a b=>?_,actor X F i w V,F.roll_hold X i w V⟩; rcases link_cases u with ⟨k,l⟩|l; rw [l]; apply fact_H X F i w V _ _ j; exact (zone_of_halo X j _ _|>.1 a); let t:= inside_iff ..|>.2 ⟨Finset.mem_coe.mp a, Finset.mem_coe.mp b⟩; rw [l]; apply fact_V X F i w V _ _ j; exact l ▸ t -- tune
end YM.CF.BPress.Wealth
