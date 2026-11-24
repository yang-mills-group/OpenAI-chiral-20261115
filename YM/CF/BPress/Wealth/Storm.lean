import YM.CF.BPress.Wealth.Mercy
/-! Supports in angle/core: heavy units only. In special vertical case take only that column (the indicated within-gap test in the orientation specific to its D face), using explicit links for vertical cost. Otherwise support via full post-channel depot (all sites, as eq:B-kept). Use signed orientations whether small or large. Range PL. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix
variable {s:Side} {b:BandWidth}(X : Bands s b) (M : ℕ)
def steep : Root s → Prop:= Sum.elim lower (fun _=> False)
def columnBall (x:X.Hcols)(r:ℕ) := univ.filter fun i:X.Hcols=> i.1=x.1 ∧ delta x.2 i.2 ≤ r
def rangeTh (u:Root s) := columnBall X (block X M u) (3*M)
def danger (u : Root s) : Finset X.Hcols:= if steep u then {block X M u} else rangeTh X M u
-- required hypotheses for depots, heights and range uses. particular every-purchase event condition via PL buys.
structure High (b:BandWidth)(M:ℕ) : Prop where
 large : 1≤ M
 spans : 8*M<b.marked.val
 copy : 5*M+2 ≤ cloak b

variable {X M}
lemma column_eq {u v:X.Hcols}{r :ℕ} : u∈columnBall X v r ↔ u.1=v.1 ∧ delta v.2 u.2 ≤ r:=by simp [columnBall]
@[simp] lemma column_self (u:X.Hcols)(r:ℕ) : u∈ columnBall X u r:= column_eq.mpr ⟨rfl,by simp⟩
lemma danger_sub (i: Root s) (X:Bands s b) (M:ℕ) : danger X M i ⊆ rangeTh X M i:=by unfold danger; split; exact singleton_subset_iff.mpr (column_self ..); rfl
lemma danger_house (i: Root s) (X:Bands s b)(M:ℕ): block X M i ∈ danger X M i:=by unfold danger; split; simp; apply column_self -- tune
lemma near_zone (h:High b M)(i:Root s)(t:retained X M i) : depot M i ⊆ halo (cloak b) (X.gap (house X M i)):=by
 apply Subset.trans (hall_depot X M i t); intro a v; obtain ⟨j,p,f⟩:= halo_spec.mp v; exact halo_spec.mpr ⟨j,p,f.trans h.copy⟩
lemma inside_le {S T:Support s}(p:S⊆ T): inside S⊆ inside T:= fun i t=> inside_iff ..|>.mpr ⟨p (inside_iff ..|>.mp t).1,p (inside_iff ..|>.mp t).2⟩
lemma columns_only (h: High b M)(i:Root s) (t:retained X M i) {p:Link s}(v:p∈inside (depot M i)) {q:X.Air} (g:edgeKey X p=some q): q.1 ∈ rangeTh X M i:=by
 obtain ⟨a,b⟩:= inside_iff ..|>.mp v; have ht:station X (p.1 0) (house X M i):=(zone_of_halo ..).1 (near_zone h i t a); rw [key_housed X ht g]; obtain ⟨j,t,g⟩:= halo_spec.mp (central_mem M i|>.2.2 a); rw [mem_singleton.mp t] at g; refine column_eq.mpr ⟨rfl,delta_le.mpr fun j=>?_⟩; refine ((Grid.delta_at (central i) p.1 j.succ).trans g).trans ?_; have he:=h.large; omega

def aperture (i:Bonding s) (k:Fin 4) : Link s:= let a:=i.1; let u:= i.2.val.1; let b:= i.2.val.2; ![(a,u),(a+step u,b),(a+step b,u),(a,b)] k
def tickets (M:ℕ) : Root s → Finset (Link s):= Sum.elim (fun i=> univ.image (aperture i)) fun i=> inside (depot M (Sum.inr i))
lemma ap_limit (i:Bonding s)(k) : aperture i k∈inside (touched i):=by
 rw [inside_iff]; fin_cases k<;> simp [aperture,touched,square_corners,add_assoc, add_comm (step _ : Site s) (step _ : Site s)] -- tune add_comm
lemma key_vert_H (i:X.Air){k:Fin 4}{a:X.Air} (p:edgeKey X (aperture (vert X i) k)=some a): a.1=i.1:=by
 rcases i with ⟨⟨i,x⟩,n,j⟩; let t:= lowTime X i n; have v:= low_gaps X i n x; obtain ⟨p',b⟩:= inside_iff ..|>.mp (mem_filter.mp v).1; have ht: station X t i:= time_zero X i _ ((time_Zone X i _).2 (show event t x∈ _ from p')) _; rw [show (vl t x).1+step (vl t x).2=event (t+1) x from event_up ..] at b -- tune time shadow
 have hu:station X (t+1) i:=time_zero X i _ ((time_Zone X i _).2 b) _
 let P:= vert X ((i,x),(n,j)); have he:aperture P 2=vl t (glide j x):=Prod.ext (event_across t x j) rfl; have hg:aperture P 1=fl (t+1) (x,j):= Prod.ext (event_up t x) rfl
 fin_cases k
 · change edgeKey X (vl t x)=some a at p; rw [EdgeKey_V] at p; contradiction
 · change edgeKey X (aperture P 1)=some a at p; rw [hg,EdgeKey_H] at p; exact key_reads X hu p
 · change edgeKey X (aperture P 2)=some a at p; rw [he,EdgeKey_V] at p; contradiction
 change edgeKey X (fl t (x,j))=some a at p; rw [EdgeKey_H] at p; exact key_reads X ht p
lemma ticket_mem (M:ℕ)(i:Root s) : tickets M i⊆ inside (depot M i):= by rcases i with i|i; intro u k; obtain ⟨j,_,rfl⟩:= mem_image.mp k; exact ap_limit ..; rfl
lemma ticket_key (h:High b M)(i:Root s)(p:retained X M i){j:Link s}(v:j∈ tickets M i){a:X.Air}(g:edgeKey X j=some a): a.1 ∈ danger X M i:=by
 unfold danger; split; next t=>
    rcases i with i|i; · obtain ⟨i,rfl⟩:=low_all X M i t p; obtain ⟨l,u,rfl⟩:= mem_image.mp v; exact mem_singleton.mpr ((key_vert_H i g).trans ((vert_block X M h.spans i).symm)) -- tune
    exact False.elim t
 apply columns_only h i p (ticket_mem M i v) g
def regular (S:Finset X.Hcols)(i:Root s) := Disjoint S (danger X M i) -- fix def
lemma use_vert (h:High b M) (S:Finset X.Hcols)(i:X.Air): regular (X:=X) (M:=M) S (.inl (vert X i))↔ i.1 ∉ S:=by unfold regular danger; rw [if_pos (show steep (.inl (vert X i)) from vert_l X i),vert_block X M h.spans]; simp
lemma use_reg {S:Finset X.Hcols}{i:Root s} (h:High b M)(t: regular S (X:=X) (M:=M) i)(p:retained X M i){j:Link s}(v:j∈ tickets M i){a:X.Air}(g:edgeKey X j=some a): a.1∉ S:= disjoint_left.mp (Disjoint.symm t) (ticket_key h i p v g)
lemma use_same {S S':Finset X.Hcols}{i:Root s}(p : ∀ j∈rangeTh X M i,j∈S↔j∈ S') : regular (X:=X) (M:=M) S i↔ regular (X:=X) (M:=M) S' i:=by
 unfold regular; rw [Finset.disjoint_right, Finset.disjoint_right]; apply forall_congr'; intro j; exact imp_congr_right fun h=> (p j (danger_sub i X _ h)).not
lemma column_sym {i j:X.Hcols}{k:ℕ} : j∈columnBall X i k ↔ i∈columnBall X j k:=by rw [column_eq,column_eq,delta_comm]; exact and_congr_left fun _=> eq_comm
lemma tail_sep (x y : Site s) : delta (Fin.tail x) (Fin.tail y) ≤ separation x y:= delta_le.mpr fun i=> delta_at x y i.succ
lemma event_sep {k:ℕ}{x y : Site s}(p:delta (Fin.tail x) (Fin.tail y)≤k)(v:delta1 s (x 0) (y 0)≤k): separation x y≤ k:= @delta_le 4 k s x y|>.mpr fun i=> Fin.cases v (fun a=> delta_le.mp p a) i -- tune argument order
lemma town (h:High b M)(i:Root s)(p:retained X M i){x:X.Hcols}(g:x∈rangeTh X M i): separation (event (X.stop x.1) x.2) (central i) ≤ 8*M + b.D:=by
 obtain ⟨f,g⟩:= column_eq.mp g; change x.1=house X M i at f; change delta (Fin.tail (central i)) _≤3*M at g; have hh:= housed X M i p; obtain ⟨a,⟨k,v,j⟩,q⟩:= hh; apply event_sep
 · rw [show Fin.tail (event _ x.2)=x.2 from Fin.tail_cons ..]; refine (Grid.delta_comm ..).le.trans (g.trans ?_); omega
 rw [event_time,f,d_sym]; apply (d_one_triangle (central i 0) a _).trans; have ht:= X.ditch_o x.1; rw [j]; unfold Tunnel.rise; rw [ditch_o]; rw [j] at q; refine (add_le_add q (delta_nat ..)).trans ?_; omega
set_option maxRecDepth 4000 in
lemma ticket_copies (h:High b M)(x:X.Hcols): ((univ.filter (fun i:Root s=> retained X M i ∧ x∈rangeTh X M i)).card) ≤ (2*(8*M+b.D)+1)^4 * Fintype.card (Option Signed × PlaqAxes):=by
 let K:= halo (8*M+b.D) {event (X.stop x.1) x.2}; let S := univ.filter fun i:Root s=> retained X M i ∧ x∈rangeTh X M i; have he : S.card≤ (K×ˢ (univ:Finset (Option Signed × PlaqAxes))).card:= card_le_card_of_injOn (fun i=>(central i, Wealth.brand i)) (fun i p=> show _ from mem_product.mpr ⟨halo_spec.mpr ⟨_,mem_singleton_self _, town h i ((mem_filter.mp p).2).1 ((mem_filter.mp p).2).2⟩,mem_univ _⟩) (levyH_inj.injOn) -- tune
 refine he.trans ?_; rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ (halo_size ..)
end YM.CF.BPress.Wealth
