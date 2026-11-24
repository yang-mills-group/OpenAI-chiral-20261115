import YM.CF.BPress.Wealth.Income
/-!
Precise direct plaquette geometry, severe-column assignment for ONLY vertical direct; heavy residual others charged on tangential condition. Stage interfaces use same Root index. Unused d_cut Opt definitions separate. All coordinates gauge-origin in orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel
open scoped Topology BigOperators Classical Matrix
variable {s:Side} {b:BandWidth} (X:Bands s b) (p:X.Index)
-- ease proof with unshifted ditch coordinates

def lower (j:Bonding s) := j.2.val.1 = 0 -- uses time
lemma later (j:Bonding s): j.2.val.2≠0:= Fin.ne_zero_of_lt j.2.property
lemma tang_iff {z:Bonding s} (g: ¬ lower z)(W:Tunnel s) : touched z ⊆ W.mem ↔ z.1∈ W.mem := by
 refine ⟨fun h=> h (touched_limit ..|>.1),?_⟩; intro h i k; apply W.internal _|>.mpr; rw [show i 0=z.1 0 from ?_]; exact (W.internal _).mp h
 rw [touched,square_corners] at k; simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at k; unfold lower at g; rcases k with rfl|rfl|rfl|rfl|rfl <;> simp_all [Ne.symm g,Ne.symm (later z)]  -- tune simp_all worry
lemma vert_iff {z:Bonding s}(g:lower z) (W:Tunnel s): touched z⊆ W.mem ↔ (z.1,0) ∈ inside W.mem:=by
 rw [inside_iff]; dsimp only; constructor
 · intro k; refine ⟨k (touched_limit ..|>.1), k ?_⟩; unfold lower at g; rw [touched,square_corners,g]; simp
 rintro ⟨k,g'⟩ i h; unfold lower at g; rw [touched,square_corners,g] at h; simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl|rfl; exact k; exact g'; exact W.internal ..|>.mpr ((W.internal _).mp g'|>.imp fun i h=> ⟨h.1,Eq.trans (by simp [Ne.symm (later z)]) h.2⟩); exact (W.internal _).mpr ((W.internal _).mp k|>.imp fun i h=> ⟨h.1,Eq.trans (by simp [Ne.symm (later z)]) h.2⟩); exact k
lemma depth_time {k:ℕ}(g:k≤ b.D) : footTime X (X.depth p k) p:=(time_Zone X p (event (X.depth p k) (0:Tri s))).2 (X.depth_gap _ g _)
lemma time_depth (t:Per s)(g:footTime X t p) : ∃ k≤ b.D,t=X.depth p k:=by
 obtain ⟨k,f,rfl⟩:= g; exact X.depth_flip p f
lemma depth_next (e:p∈X.dc) (k:ℕ): X.depth p (k+1)=X.depth p k+1:=by rw [depth,depth, if_pos (X.dc_index ..|>.mp e), if_pos (X.dc_index ..|>.mp e),rise_succ]
lemma depth_before (e:p∈X.nc) {k:ℕ}(u:k<b.D): X.depth p k=X.depth p (k+1)+1:=by rw [depth,depth,if_neg (X.nc_index ..|>.mp e),if_neg (X.nc_index ..|>.mp e)]; exact Tunnel.fall_before _ u -- tune

lemma two_ends (x : Site s)(t:x∈ X.gap p) : (∃ i,x∈ X.band i) ↔ x 0=X.depth p 0 ∨ x 0=X.depth p b.D:=by
 rw [X.depth_zero,X.depth_D]; have v : (∃ i,x∈ X.band i)↔ x 0=X.stop p ∨ x 0=X.start (p+1):=by simp_rw [X.at_overlap t]; rw [exists_or]; simp
 split; exact v; exact v.trans (or_comm)

/-- Clock step from distance k to D, pay vertical link at temporal LOWER of k,k+1. -/
def lowTime (k : Fin b.D) := if p∈X.dc then X.depth p k.val else X.depth p (k.val+1)
lemma low_time (e:p∈X.dc) (k: Fin b.D) : lowTime X p k=X.depth p k.val ∧ lowTime X p k+1=X.depth p (k.val+1):=by
 rw [lowTime,if_pos e]; exact ⟨rfl,(depth_next X p e k.val).symm⟩
lemma low_before (e:p∈X.nc)(k:Fin b.D) : lowTime X p k=X.depth p (k.val+1) ∧ lowTime X p k+1=X.depth p k.val:=by
 rw [lowTime,if_neg (mem_sdiff.mp e).2]; exact ⟨rfl,(depth_before X p e k.isLt).symm⟩
lemma low_inj : Injective (lowTime X p):=by
 intro i j v; unfold lowTime at v; split at v; exact Fin.ext (X.depth_inj i.isLt.le j.isLt.le v); apply Fin.ext; exact Nat.succ_inj.mp (X.depth_inj i.isLt j.isLt v)
lemma low_onto {u:ℕ}(g:u<b.D) : ∃ k: Fin b.D,lowTime X p k=(X.ditch p).rise u:=by
 by_cases t:X.Dmark p; refine ⟨⟨u,g⟩, by simp [lowTime,depth,t]⟩; let l:= b.D-u-1; have he:l < b.D:=by unfold l; omega
 refine ⟨⟨l,he⟩,by simp only [lowTime,dc_index, depth,t,↓reduceIte, Tunnel.fall,X.ditch_n,Fin.val_mk]; congr; unfold l; omega⟩
lemma low_gaps (k : Fin b.D)(x:Tri s): vl (lowTime X p k) x ∈ X.gaps p:=by
 apply mem_filter.mpr; refine ⟨(inside_iff ..).mpr ⟨?_,?_⟩,rfl⟩; all_goals dsimp only [vl]; try rw [event_up]
 all_goals by_cases u:p∈X.dc
 · rw [(low_time X _ u k).1]; exact X.depth_gap p k.isLt.le _
 · rw [(low_before X _ (mem_sdiff.mpr ⟨mem_univ _,u⟩) k).1]; exact X.depth_gap p k.isLt _
 · rw [(low_time X _ u k).2]; exact X.depth_gap p k.isLt _
 · rw [(low_before X _ (mem_sdiff.mpr ⟨mem_univ _,u⟩) k).2]; exact X.depth_gap p k.isLt.le _

def vert (i:X.Air) : Bonding s:= (event (lowTime X i.1.1 i.2.1) i.1.2,⟨(0,i.2.2.succ),Fin.succ_pos _⟩)
lemma vert_l (i:X.Air):lower (vert X i):=rfl
lemma vert_sub (i:X.Air) : touched (vert X i)⊆ X.gap i.1.1:= (vert_iff (vert_l X i) (X.ditch i.1.1)).2 (mem_filter.mp (low_gaps X i.1.1 i.2.1 i.1.2)).1 -- tune
lemma vert_one: Injective (vert X):=by
 rintro ⟨⟨i,x⟩,k,q⟩ ⟨⟨j,y⟩,l,v⟩ e; obtain ⟨a,g⟩:=Prod.mk.inj e; obtain ⟨hp,hq⟩:= event_eq.mp a; have he:i=j:= by apply Classical.byContradiction; intro t; apply disjoint_left.mp (X.ditch_disjoint t); swap; exact vert_sub X ((j,y),(l,v)) (touched_limit ..|>.1); refine vert_sub X ((i,x),(k,q)) ?_; rw [e]; apply (touched_limit ..).1
 subst j; exact Prod.ext (Prod.ext rfl hq) (Prod.ext (low_inj X _ hp) (Fin.succ_inj.mp (congrArg (fun t:PlaqAxes=> t.val.2) g)))
variable (M : ℕ)
lemma vert_ret (i:X.Air):retained X M (.inl (vert X i)):=by
 intro j h; let p:=vert X i; let t:= (low_gaps X i.1.1 i.2.1 i.1.2); obtain ⟨x,e⟩:= X.link_overlap (i:=i.1.1) (j:=j) (k:= vl (lowTime X i.1.1 i.2.1) i.1.2) (mem_filter.mp t).1 ((vert_iff (vert_l X i) (X.mark j)).mp (show touched p⊆ (X.mark j).mem from h)); rcases e with ⟨h,v⟩|⟨h,v⟩<;> exact fl_ne_vl _ _ _ _ v.symm
lemma low_all (i:Bonding s)(p:lower i) (t:retained X M (.inl i)): ∃ j:X.Air,i=vert X j:=by
 obtain ⟨k,v|v⟩:= X.links_cover (i.1,0); exact False.elim (t k ((vert_iff p (X.mark k)).2 v)); obtain ⟨j,e,x,h⟩:= (X.gaps_b k (i.1,0)).mp (mem_filter.mpr ⟨v,rfl⟩); obtain ⟨l,v⟩:= low_onto X k e; rw [←v] at h; obtain ⟨d,g⟩:= Fin.exists_succ_eq.mpr (later i); exact ⟨((k,x),(l,d)), Prod.ext (congrArg (fun z:Link s=>z.1) h) (Subtype.ext (Prod.ext p g.symm))⟩
lemma tang_ret {i:Bonding s}(p : ¬lower i) : retained X M (.inl i) ↔ ∃ k,i.1∈ X.gap k∧ i.1 0≠X.depth k 0 ∧ i.1 0≠X.depth k b.D:=by
 constructor
 · intro t; obtain ⟨j,h|h⟩:= X.cover i.1; exact False.elim (t j ((tang_iff p (X.mark j)).2 h)); have hh:= mt ((two_ends X j i.1 h).2) (show ¬ ∃ j,i.1∈ X.band j from fun ⟨j,v⟩=> t j ((tang_iff p (X.mark j)).2 v)); exact ⟨j,h,not_or.mp hh⟩
 rintro ⟨j,t,v,g⟩ i' p'; exact (not_or.mpr ⟨v,g⟩) ((two_ends X j _ t).1 ⟨i',(tang_iff p (X.mark i')).1 p'⟩)
lemma open_gap (i:Bonding s)(h:retained X M (.inl i)): ∃ k,touched i⊆ X.gap k:=by
 by_cases u:lower i; obtain ⟨i,rfl⟩:= low_all X M i u h; exact ⟨_,vert_sub X i⟩; obtain ⟨k,p,x,q⟩:= tang_ret X M u|>.1 h; exact ⟨k,(tang_iff u (X.ditch k)).2 p⟩
lemma retained_near (i:Root s)(h:retained X M i): ∃ k, ZoneNear X k (4*M) (central i 0):=by
 rcases i with i|i; obtain ⟨k,p⟩:= open_gap X M i h; exact ⟨k,time_zero X k _ ((time_Zone X k _).2 (p (touched_limit .. |>.1))) (4*M)⟩; exact (letKeep ..).1 h
-- Given h zone size disjoint, actual gap identity WELL-defined. row counts ≤ PL.
def house (i:Root s) : X.Index:= if h:∃ k, ZoneNear X k (4*M) (central i 0) then h.choose else 0
lemma housed (i:Root s)(t:retained X M i): ZoneNear X (house X M i) (4*M) (central i 0):=by unfold house; rw [dif_pos (retained_near X M i t)]; exact Exists.choose_spec  (retained_near X M i t)
lemma housed_id (h: 8*M<b.marked.val){i : Root s} (v:ZoneNear X p (4*M) (central i 0)): house X M i=p:=by
 let x:=central i; unfold house; rw [dif_pos ⟨p,v⟩]; refine Classical.byContradiction (fun t=> disjoint_left.mp (pill X (r:=4*M) (by omega) t ) ?_ ((zone_of_halo X p (4*M) x).2 v)); exact (zone_of_halo ..).2 (Exists.choose_spec (show ∃ j,ZoneNear X j _ (x 0) from ⟨p,v⟩))
lemma vert_house (h: 8*M<b.marked.val)(i:X.Air): house X M (.inl (vert X i))= i.1.1:= housed_id X i.1.1 M h (time_zero X i.1.1 _ ((time_Zone X i.1.1 _).2 (vert_sub X i (touched_limit ..|>.1))) _)
def block (i:Root s) : X.Hcols := (house X M i,Fin.tail (central i))
lemma vert_block (h:8*M<b.marked.val)(i:X.Air): block X M (.inl (vert X i))= i.1:= Prod.ext (vert_house X M h i) (by simp [block,central,vert,event])
lemma hall_depot (i:Root s)(v: retained X M i): depot M i⊆halo (5*M+2) (X.gap (house X M i)):= ((central_mem ..).2.2).trans (by rw [show 5*M+2=4*M+(M+2) by omega]; exact enclosed X _ (housed X M i v)) -- tune
end YM.CF.BPress.Wealth
