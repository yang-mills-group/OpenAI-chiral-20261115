import YM.SU5.Relativistic.Baker
/-! # tiled pressure proof. Positive positions. Mark plans. -/
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
def peak (Y:Side):Site Y:=fun _=> -(1:Per Y)
lemma peak_p (Y:Side)(i:Axis):(peak Y i).val+1=Y.val:=by
 obtain ⟨_|k,h⟩:=Y; · simp at h
 change (- (1:ZMod (k+1))).val+1=k+1; rw [ZMod.val_neg_one]
def seed (i:T_)(j:Axis) : P_:= if h:Active (i,j) then peak W_ + step (tooth (i,j) h) else peak W_
lemma seed_j (i:T_)(j:Axis) : seed L i j j=peak W_ j :=by
 unfold seed; split_ifs with g; · simp [(tooth_spec _ g).1.symm]
 rfl
lemma seed_k (i:T_)(j k:Axis): seed L i j k=peak W_ k ∨ seed L i j k=0:=by
 unfold seed; split_ifs with g; · by_cases e:k=tooth (i,j) g; exact Or.inr (by simp [e,peak]); exact Or.inl (by simp [e])
 exact Or.inl rfl
lemma endW {Y:Side}{x:Site Y}{i:Axis} : ¬indoors (x,i) ↔ x i=peak Y i:=by
 constructor; · intro g; change ¬ (x i).val+1< Y.val at g; have he:=ZMod.val_lt (x i); exact ZMod.val_injective Y.val (Nat.add_right_cancel ((show (x i).val+1=Y.val from by omega).trans (peak_p Y i).symm))
 intro h v; have hv:=(show (x i).val+1< Y.val from v); rw [h,peak_p] at hv; exact hv.false

def how (i: Link N): Prop:= let p:= vowel L i; if indoors p.2 then Active p.2 else Active (p.1,p.2.2) ∨ p.2.1≠ seed L p.1 p.2.2
instance(x: Link N): Decidable (how L x):=by classical exact Classical.propDecidable _
lemma how_in (i:T_)(p:Link W_)(h:indoors p) : how L (raise L i p)↔Active p:=by simp [how,h]
lemma how_out (i:T_)(p:Link W_)(h:¬ indoors p) : how L (raise L i p)↔ Active (i,p.2) ∨ p.1≠seed L i p.2:=by simp [how,h]
-- Priority.Calibrated using T_
def turn {Y:Side}(x y:Site Y):ℕ := ∑ j:Axis, if y j=peak Y j then Y.val-1-(x j).val else (x j).val
lemma turn_lt{Y:Side}(x y:Site Y): turn x y < 5*Y.val:=by
 have he: turn x y ≤ 4*Y.val:=le_trans (Finset.sum_le_sum (f:=fun j:Axis=>if y j=peak Y j then Y.val-1-(x j).val else (x j).val) (s:=univ) (g:=fun _=>Y.val) (fun i _=>by have he:=ZMod.val_lt (x i); split <;> omega)) (by simp [show Fintype.card Axis=4 from rfl])
 have h:0<Y.val:=Y.property; omega
def limit (W:Side):ℕ:= 5*W.val+1
def ranking (x:Link N):ℕ:= let p:=vowel L x; let Z:=limit W_; if indoors p.2 then originSum p.2.1 else Z*(1+(if Active (p.1,p.2.2) then 1+originSum p.1 else 0))+turn p.2.1 (seed L p.1 p.2.2)
lemma rank_in(i:T_)(p:Link W_)(h:indoors p): ranking L (raise L i p)=originSum p.1:=by simp [ranking,h]
lemma rank_ex(i:T_)(p:Link W_)(h:¬ indoors p):ranking L (raise L i p)=limit W_*(1+(if Active (i,p.2) then 1+originSum i else 0))+turn p.1 (seed L i p.2):=by simp [ranking,h]
lemma origin_lt_w {Y:Side}(x:Site Y): originSum x<limit Y:=by
 have he:originSum x≤4*Y.val:=le_trans (Finset.sum_le_sum (s:=univ) (g:=fun _:Axis=> Y.val) (fun i _=> (ZMod.val_lt (x i)).le)) (by simp [show Fintype.card Axis=4 from rfl]); unfold limit; omega
lemma rank_cut (i j:T_)(p q:Link W_)(x: indoors p)(y:¬indoors q) : ranking L (raise L i p) < ranking L (raise L j q):=by
 rw [rank_in L _ _ x,rank_ex L _ _ y,Nat.mul_add, Nat.mul_one]; exact lt_of_lt_of_le (origin_lt_w p.1) (Nat.le_add_right_of_le (Nat.le_add_right ..)) -- tune
lemma rank_seed(i j:T_)(a b:Link W_)(h:Active (i,a.2))(e:Active (j,b.2)→ originSum j<originSum i)(u:¬ indoors a)(v:¬ indoors b): ranking L (raise L j b)< ranking L (raise L i a):=by
 rw [rank_ex L _ _ u,rank_ex L _ _ v,if_pos h]; have hh:turn b.1 (seed L j b.2)<limit W_:=Nat.lt_succ_of_lt (turn_lt ..)
 let x:= 1+(if Active (j,b.2) then 1+originSum j else 0)
 have he: x+1 ≤ 1+(1+ originSum i):=by
    unfold x; split
    · next g => have he:= e g; omega
    omega
 calc _<limit W_*x+limit W_:= Nat.add_lt_add_left hh _
      _=limit W_*(x+1):=by ring
      _ ≤ _:= le_trans (Nat.mul_le_mul_left _ he) (Nat.le_add_right ..)
lemma step_dist{Y:Side}(p:2≤Y.val)(x:Site Y)(i:Axis): x≠x+step i:=by intro w; have ht:=congrFun w i; simp at ht; have he:=congrArg ZMod.val ht; rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (by omega)] at he; simp at he
lemma grant_seed (p:2≤ C.val)(x:T_)(i:Axis)(h:Active (x,i)) : let v:=raise L x (seed L x i,i); ∃ f:Face (Per N), v∈support f∧∀ j∈ support f,j≠v→ how L j→ ranking L j<ranking L v:=by
 intro v; let k:= tooth (x,i) h; let y:=x-step k; let z:= setDown L y (peak W_)
 let s:=peak W_; have hy:y+step k=x:=sub_add_cancel ..; have he:seed L x i= s+step k:=dif_pos h; have hx:k≠i:= (tooth_spec _ h).1
 have hv:raise L y (s,i)=(z,i):=rfl; have hp:raise L y (s,k)=(z,k):=rfl
 have hs:raise L (y+step i) (s+step i,k)=(z+step i,k):= Prod.ext (oddShift L y s i (peak_p ..)) rfl
 have ht:v=(z+step k,i):=by unfold v; rw [he,show raise L x (s+step k,i) = raise L (y+step k) (s+step k,i) from by rw [hy]]; exact Prod.ext (oddShift L y s k (peak_p ..)) rfl
 have hr(j:T_)(a:Axis)(b:P_)(t:b a=peak W_ a)(H:(j,a)∈window y i k)(g:(j,a)≠(x,i)) : ranking L (raise L j (b,a))<ranking L v := rank_seed L x j (seed L x i,i) (b,a) h (fun u=> behind (x,i) h (j,a) u ((mark_window x i h).symm ▸ H) g) (endW.mpr (seed_j ..)) (endW.mpr t)
 refine ⟨(z,PlaqAxes.ordered i k hx.symm),by rw [win_shuffle,ht]; simp [window],?_⟩
 rw [win_shuffle]; intro j e w _; simp only [window,mem_insert,mem_singleton] at e; rcases e with rfl|rfl|rfl|rfl
 · rw [←hv]; exact hr y i s rfl (by simp [window]) (fun g=>step_dist p y k ((congrArg Prod.fst g).trans hy.symm))
 · rw [←hs]; exact hr _ k (s+step i) (by simp [s,hx]) (by simp [window]) (by simp [hx])
 · exact (w ht.symm).elim
 rw [←hp]; exact hr _ k s rfl (by simp [window]) (by simp [hx])

lemma rank_move{i:T_}{x:P_}{j k:Axis}(h:j≠k)(u:x j=peak W_ j)(p:(x k).val+1 < L.count.val) : let G:=ranking L (raise L i (x,j)); let H:=ranking L (raise L i (x+step k,j)); if seed L i j k=peak W_ k then H<G else G<H:=by
 intro G H; unfold G H; have hp:(x+step k : P_) j=peak W_ j:=by simp [u,h]
 simp only [rank_ex L i _ (endW.mpr u),rank_ex L i _ (endW.mpr hp),Nat.add_lt_add_iff_left] -- inside seed
 -- turn comparison by sum erase
 let F (x:P_)(l:Axis):= if seed L i j l=peak W_ l then L.count.val-1-(x l).val else (x l).val
 let S:=∑ l∈univ.erase k,F x l
 have ht: turn (x+step k) (seed L i j)= S+ F (x+step k) k:=by
   unfold turn
   rw [← Finset.sum_erase_add _ _ (mem_univ k)]; congr 1
   exact Finset.sum_congr rfl (fun i hi => (show F (x+step k) i= F x i from by simp [F,(mem_erase.mp hi).1])) -- rw turn reducible?
 rw [ht,show turn x (seed L i j)=S+ F x k from (sum_erase_add _ _ (mem_univ k)).symm]
 split_ifs with g -- ifs from rank throughput careful
 all_goals first| assumption| (unfold S F; rw [next_s x k p]; split_ifs <;> omega) -- tune

lemma lift_window (i:T_)(x:P_)(j k:Axis)(h:j≠k)(u:x j=peak W_ j)(p: (x k).val+1<L.count.val) : let y:=setDown L i x; let V:=raise L i (x,j); let V':=raise L i (x+step k,j); ∃ m n : Link N, (support (y,PlaqAxes.ordered j k h))={V,V',m,n}∧ (ranking L m<ranking L V∧ranking L m<ranking L V')∧ranking L n<ranking L V∧ranking L n<ranking L V':=by
 intro y V Q
 have hw:indoors (x,k):=p; have hp: (x j).val+1=L.count.val:= u.symm ▸ peak_p _ _; let z:=x+step j;
 have hx:indoors (z,k):=by change (z k).val+1<L.count.val; simpa [h.symm,z]
 let m:= raise L i (x,k); let n:=raise L (i+step j) (z,k)
 have hu:¬ indoors (x,j):=endW.mpr u; have hv:¬ indoors (x+step k,j):= endW.mpr (by simp [h,u]); refine ⟨m,n,?_,⟨rank_cut L _ _ _ _ hw hu,rank_cut L _ _ _ _ hw hv⟩,rank_cut L _ _ _ _ hx hu,rank_cut L _ _ _ _ hx hv⟩
 rw [win_shuffle]; ext t; unfold window V Q m n z y raise; simp only [oddShift L _ _ _ hp, evenShift L _ _ _ p,mem_insert,mem_singleton]; tauto

lemma grant_move (i:T_)(x:P_)(j:Axis)(v:x j=peak W_ j)(h:x≠seed L i j) : let y:= raise L i (x,j); ∃ f:Face (Per N), y∈support f∧∀ m∈ support f,m≠y→how L m→ ranking L m<ranking L y:=by
 intro y; obtain ⟨k,hK⟩ : ∃ k,x k ≠ seed L i j k:=Function.ne_iff.mp h
 have he:j ≠ k:=by intro w; subst k; rw [v,seed_j] at hK; contradiction
 rcases seed_k L i j k with g|g
 · rw [g] at hK; have hp: (x k).val+1<L.count.val:= not_not.mp (mt endW.mp hK); obtain ⟨m,n,H,u,t,U⟩:=lift_window L i x j k he v hp
   refine ⟨_,H.symm ▸ (mem_insert_self ..),?_⟩; rw [H]; intro a b w h'; simp only [mem_insert,mem_singleton] at b; rcases b with b|rfl|rfl|rfl
   · exact (w b).elim
   · have he:=rank_move L (i:=i) (x:=x) (j:=j) (k:=k) he v hp; simpa only [if_pos g] using he
   · exact u.1
   exact t
 have hx:x k≠0:=g ▸ hK; let u:=x-step k; have he':u+step k=x:=sub_add_cancel ..; have hp: (u k).val+1< L.count.val:= (previous_s x k hx).trans_lt (ZMod.val_lt _); have hu:u j= peak W_ j:=by simp [he,v,u]
 obtain ⟨m,n,H,t,l,r⟩:=lift_window L i u j k he hu hp
 have hq: seed L i j k≠peak W_ k:=by
    intro w; have ht: peak W_ k=0:= w.symm.trans g; have hh:=peak_p W_ k; rw [ht,ZMod.val_zero,Nat.zero_add] at hh; have h0:= ZMod.val_lt (x k); exact hx ((ZMod.val_eq_zero _).mp (by omega))
 rw [he'] at H t r; refine ⟨(setDown L i u,PlaqAxes.ordered j k he),?_,?_⟩; · rw [H]; simp [y]
 rw [H]; intro a b w _; simp only [mem_insert,mem_singleton] at b; rcases b with rfl|e|rfl|rfl
 · have H':=rank_move L (i:=i) (x:=u) he hu hp; rw [he'] at H'; simpa only [if_neg hq] using H'
 · exact (w e).elim
 · exact t.2
 exact r

lemma pays (p:2≤ C.val)(x:Link N) (h: how L x) : ∃ f:Face (Per N), x∈support f∧∀ i∈ support f,i≠x→ how L i→ ranking L i<ranking L x:=by
 obtain ⟨⟨i,y⟩,rfl⟩:= (vowel L).symm.surjective x; change how L (raise L i y) at h
 by_cases v:indoors y
 · have he:Active y:=(how_in L _ _ v).mp h
   refine ⟨loom L i y he,?_,?_⟩; · rw [at_loom _ _ _ v]; exact mem_image_of_mem _ (mark_roll ..)
   rw [at_loom _ _ _ v]; intro j hj e t; obtain ⟨z,u,rfl⟩:=mem_image.mp hj; have hp:=pin_space _ v he _ u
   change _ ≠ raise L i y at e; change ranking L _<ranking L (raise L i y); rw [rank_in L _ _ v,rank_in L i z hp]; exact behind _ he _ ((how_in L _ _ hp).mp t) u (mt (congrArg _) e)
 rcases y with ⟨y,j⟩; by_cases g:y=seed L i j
 · have he':= (how_out L i _ v).mp h; have he:Active (i,j):= he'.resolve_right (not_not_intro g); subst y; exact grant_seed L p i j he
 exact grant_move L _ y j (endW.mp v) g
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.pays
