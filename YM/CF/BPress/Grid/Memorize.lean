import YM.CF.BPress.Grid.Spout
import YM.CF.BPress.Grid.Thin
/-! `eq:B-fare`: the large Mark extension uses thin, connected supports at these same
     scales. Never purchase a four- (or three-) dimensional ball of volume O(R^3) per query. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid.Half
open Function Lattice MeasureTheory Finset Filter SU Cube Branch
open scoped Topology BigOperators Classical
variable {s:Side} {d r : ℕ} (S : Finset (Space d s))(p: Grove (field d s) S)
include p
private lemma layer (k:ℕ)(v:0<r)(t:r∣s.val) : ∃ T : Finset (Space d s), S⊆T ∧ Grove (field d s) T ∧ T⊆ broad (field d s) S ((2*k+1)*r) ∧
    T.card≤ (1+(4*(k+2)+1)^d*(k+1+(d+1)*2))*(S.card+r) ∧ ∀ i∈S,∀ x∈mesh r, delta i x≤ k*r→ whole x r ⊆ T:=by
 let A:=(broad (field d s) S (k*r)).filter (·∈mesh r)
 have Ha(x:A):∃ i∈ S, delta i x.val ≤ k*r:= (broad_mem ..).mp (mem_filter.mp x.property).1
 choose u H g using Ha
 choose B h f C I q using fun (x:A)=> thin _ _ (g x)
 let T(x:A):=B x ∪ whole x.val r; have ht(x:A): (u x∈ T x) ∧ Grove (field d s) (T x) ∧ (T x).card≤(k+1+(d+1)*2)*r∧ T x⊆ broad (field d s) S ((2*k+1)*r):=by
   obtain ⟨b,P,F,V⟩:= paid_rail x.val r; refine ⟨mem_union_left _ (C x), (f x).unite P (I x) b, card_union_le .. |>.trans ((add_le_add (q x) F).trans ?_), ?_⟩
   · nlinarith
   intro i t; refine broad_mem ..|>.mpr ⟨u x,H x,?_⟩; rcases mem_union.mp t with v|v; refine (bay_mem _ |>.mp (h x v)).trans ?_; nlinarith
   exact (delta_triangle (u x) x.val i).trans ((add_le_add (g x) ((bay_mem _).mp (V v))).trans (by nlinarith))
 obtain ⟨b,D⟩:= many (field d s) S p univ T (fun i _=> (ht i).2.1) (fun i _=> ⟨u i,H i,(ht i).1⟩); refine ⟨_, subset_union_left,b, ?_, D.trans ?_,?_⟩
 · refine Finset.union_subset ?_ (biUnion_subset.mpr fun i _=> (ht i).2.2.2); intro i h; exact (broad_mem ..).mpr ⟨i,h, by change delta _ _ ≤ _; simp⟩
 · let Q:=(k+1+(d+1)*2); let W:= (4*(k+2)+1)^d; apply le_trans (add_le_add_right (sum_le_sum (fun i (_:i∈(univ:Finset A))=> (ht i).2.2.1)) S.card); rw [sum_const, card_univ,Fintype.card_coe,nsmul_eq_mul]; change S.card+A.card*(Q*r)≤_; rw [show A.card*(Q*r)=Q*(r*A.card) by ring]; have h : r*A.card ≤ W*(S.card+r):=around t S p k v; apply le_trans (add_le_add_right (Nat.mul_le_mul_left Q h) _); change _ ≤ (1+W*Q)*_; nlinarith
 intro i hi x e g; let z:↥A:= ⟨x,mem_filter.mpr ⟨ (broad_mem ..).mpr ⟨i,hi,g⟩,e⟩⟩; intro y p; exact mem_union_right _ (mem_biUnion.mpr ⟨z,mem_univ _, mem_union_right _ p⟩)

omit p
/-- Actual fare estimate on gauge of smoothing, using integer log-two widths. `EqOn` on coarse
    grids for initial frame inputs. `delta` is micro sup graph metric. -/
structure Keeps (R n C:ℕ)(φ:Flow s→ Fabric 3 s E) : Prop where
 memo (S:Finset (Space 3 s))(p:Grove (field 3 s) S): ∃ T, Grove (field 3 s) T ∧ S⊆ T ∧
    T ⊆ broad (field 3 s) S (C*R) ∧ T.card≤ C*(R+(n+1)*S.card) ∧
    ∀ x y:Flow s, equalOn x.1 y.1 T → Set.EqOn x.2 y.2 (↑T ∩ mesh R)→ Set.EqOn (φ x) (φ y) ↑S

private lemma cost_n (b:Side) : ∃ C:ℕ, ∀ s:Side, ∀ n:ℕ, (2^n)*b.val∣s.val → ∀ φ:Flow s→ _, radixRead b 0 n φ → Keeps ((2^n)*b.val) n C φ:=by
 let l:=10*b.val; let Q:= 1+(4*(l+2)+1)^3*(l+1+(3+1)*2); refine ⟨max (2*l+1) (2*Q+1), fun s n p φ g=> ⟨fun S h=> ?_ ⟩⟩
 let I:=range (n+1); have p'(k)(v:k∈I) : 2^k∣s.val:= dvd_trans (dvd_mul_of_dvd_left (pow_dvd_pow _ (mem_range_succ_iff.mp v)) _) p; choose! T G V t C D using fun k (v:k∈I)=> layer S h l (by positivity : 0<2^k) (p' k v)
 let χ:= I.biUnion T; let F:=S ∪ χ; have he(k)(v:k∈ I): T k⊆ F:= Subset.trans (subset_biUnion_of_mem T v) subset_union_right
 obtain ⟨x,hx⟩:= inhabited_grove h; obtain ⟨A,B⟩:=many _ _ h I T V (fun i v=> ⟨x,hx,G i v hx⟩); let X:=max (2*l+1) (2*Q+1)
 refine ⟨F,A, subset_union_left, ?_,B.trans ?_,fun x y w f i u=> g.2.2 x y i ?_ ?_ ?_⟩
 · intro i g; refine (broad_mem ..).mpr ?_; rcases mem_union.mp g with g|g; exact ⟨i,g,by change delta _ _ ≤ _; simp⟩; obtain ⟨k,p,u⟩:=mem_biUnion.mp g; obtain ⟨j,t,g⟩:= broad_mem ..|>.mp (t k p u); refine ⟨j,t,g.trans (Nat.mul_le_mul (le_max_left ..) ?_)⟩; exact (pow_le_pow_right₀ (show (1:ℕ)≤2 by norm_num) (mem_range_succ_iff.mp p)).trans (Nat.le_mul_of_pos_right _ b.property)
 · apply le_trans (add_le_add_right (sum_le_sum (g:=fun i=> Q * (S.card+2^i)) (fun i v=>C i v)) S.card); have hx: (∑ i∈range (n+1),(2:ℕ)^i) ≤ 2*2^n:= by
     have hh(k): (∑ i ∈ range k,(2:ℕ)^i)+1=2^k:=by induction k with|zero=>simp|succ k ih=>rw [sum_range_succ,pow_succ]; omega
     have h:=hh (n+1); rw [pow_succ'] at h; omega
   change S.card+_ ≤ X*_; apply le_trans _ (Nat.mul_le_mul_right _ (le_max_right (2*l+1) (2*Q+1))); rw [← mul_sum,sum_add_distrib, sum_const,nsmul_eq_mul, card_range]; apply le_trans (add_le_add_right (Nat.mul_le_mul_left Q (add_le_add_right hx _)) _); have hu:2^n ≤ 2^n*b.val:= Nat.le_mul_of_pos_right _ b.property; change S.card + Q*((n+1)*S.card+2*2^n) ≤ _; apply le_trans (b:=S.card + Q*((n+1)*S.card+2*(2^n*b.val))) _
   · exact (show ∀ (Q H A n:ℕ), H+Q*((n+1)*H+2*A) ≤ (2*Q+1)*(A+(n+1)*H) from fun Q H A n=> by nlinarith [Nat.zero_le (Q*n*H)]) Q S.card _ n
   gcongr -- tune
 · simp [mesh,aligned]
 · intro k v _ j g p; have hz:k∈I:=mem_range_succ_iff.mpr v; apply equal_line; refine equal_weaken w (Subset.trans (show rail j.1 j.2 _⊆whole j.1 _ from fun x h=> mem_union_right _ (mem_biUnion.mpr ⟨_,mem_univ j.2,h⟩)) ((D k hz i u j.1 g ?_).trans (he k hz))) -- tune Finset.trans
   apply p.trans; unfold bound; unfold l; exact (Nat.sub_le ..).trans_eq (by ring)
 intro j q p; apply f; constructor; swap; · exact q
 have hv:n∈ I:=mem_range_succ_iff.mpr le_rfl; refine he n hv (D n hv i u j (align_subdiv j q (dvd_mul_right ..)) ?_ (paid_rail ..|>.1)); apply p.trans; unfold bound; unfold l; exact (Nat.sub_le ..).trans_eq (by ring)


/-- B-gate Lemma B-frames. Use explicit integer `rate` for log R since R=2^rate.
    The lemma permits any algorithm bought with these properties; our choice implements the
    proof's mesh extension and the dyadic projected-mean interpolation (tensorwise).
    Holds on every tangent input with the plaquette bound, not merely almost surely.
    Uses nearest-neighbor action of SU(5) on the **same** tangent links. (Hypothesis
    m R² < c can even use c=1.) -/
theorem frames : ∃ l B : ℕ, ∃ C : ℝ, 0<C ∧ ∀ (s:Side), ∀ i ≥ l, let R:=2^i; R∣s.val → R<s.val →
    ∃ φ:Flow s→ Fabric 3 s E, Measurable φ ∧ (∀ x o, o∈mesh R → φ x o=x.2 o) ∧ Keeps R i B φ ∧
    ∀ (m:ℝ)(U:GaugeField group 3 s)(F:Fabric 3 s E), Flat U m → (R:ℝ)^2*m ≤1 → arcFee 1 U (φ (U,F)) (C/R) := by
 obtain ⟨N,C,h,H⟩:= multi_frame
 obtain ⟨l,hL⟩:= pow_unbounded_of_one_lt N (by decide : 1<(2:ℕ))
 let b:Side:=2^l; have ht:b.val=2^l:=by simp [b]
 obtain ⟨B,P⟩:=cost_n b; refine ⟨l,B,2*C,by positivity,?_⟩; rintro s i he R hv hg
 let n:=i-l; have p: 2^n*b.val = R:= by rw [ht,←pow_add,Nat.sub_add_cancel he]
 obtain ⟨F,q,y⟩:= H b (ht.symm ▸ hL.le) s n (p.symm ▸ hv) (p.symm ▸ hg); have hc := P s n (p.symm ▸ hv) F q
 rw [p] at hc y; refine ⟨F,q.1,p ▸ q.2.1,⟨?_⟩,y⟩; intro S h; obtain ⟨T,t,u,v,w,y⟩:= hc.memo S h; refine ⟨_,t,u,v,w.trans (Nat.mul_le_mul_left _ (add_le_add_right ?_ _)),y⟩; gcongr; omega
end YM.CF.BPress.Grid.Half
