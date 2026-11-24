import YM.CF.BPress.Parade
/-! Partition of links & columns. `coins`: paid links in marks. `pole`: gap forest combined with N stores. `air`: angular data. Bridge supports for gauge fix/charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bands
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Tunnel Finset
open scoped Topology BigOperators Classical Matrix
variable {s : Side}{B : BandWidth} (X : Bands s B)
abbrev Hcols:= X.Index × Tri s -- tune def want abbrev
abbrev Body := Fin B.D × SpatialDir
abbrev Air := X.Hcols × Body (B:=B) -- tune dependency Lean can't named only abbrev?
def skylink (i : X.Air) : Link s:= fl (X.depth i.1.1 (i.2.1.val+1)) (i.1.2,i.2.2)
def air := univ.image X.skylink
lemma sky_mem (i : X.Air) : X.skylink i ∈ inside (X.gap i.1.1):= (inside_iff ..).mpr ⟨X.depth_gap _ i.2.1.isLt _, by simpa only [skylink,fl,event_across] using (X.depth_gap i.1.1 i.2.1.isLt (glide i.2.2 i.1.2))⟩
lemma match_uniq {i j : X.Index}{x : Link s} (p:x∈inside (X.band i))(v:x∈inside (X.band j)): i=j:= Classical.byContradiction fun t=> disjoint_left.mp (X.band_disjoint t) ((inside_iff ..).mp p).1 ((inside_iff ..).mp v).1
lemma gap_uniq {i j : X.Index}{x : Link s}(p:x∈inside (X.gap i))(v:x∈inside (X.gap j)): i=j:= Classical.byContradiction fun t=> disjoint_left.mp (X.ditch_disjoint t) ((inside_iff ..).mp p).1 ((inside_iff ..).mp v).1
lemma sky_inj : Injective X.skylink:=by
 rintro ⟨⟨i,x⟩,k,q⟩ ⟨⟨j,y⟩,l,t⟩ h; have he : i=j:= X.gap_uniq (X.sky_mem ((i,x),(k,q))) (show X.skylink _∈ inside (X.gap j) from h.symm ▸ X.sky_mem ((j,y),(l,t))); subst j; obtain ⟨e,p⟩:= fl_eq.mp h; obtain ⟨v,rfl⟩:= Prod.mk.inj p; have h:=X.depth_inj k.isLt l.isLt e; exact Prod.ext (Prod.ext rfl v) (Prod.ext (Fin.ext (Nat.succ_inj.mp h)) rfl)

/-- index families are disjoint for each kind of integration -/
def dc := univ.filter X.Dmark
def nc := univ \ X.dc
@[simp] lemma dc_index (i:X.Index): i∈ X.dc ↔ X.Dmark i:=by simp [dc]
@[simp] lemma nc_index (i:X.Index): i∈ X.nc ↔ ¬ X.Dmark i:=by simp [nc]
def gaps (i:X.Index) := (inside (X.gap i)).filter fun x=>x.2=0
def storesN (i:X.Index) := if i∈X.dc then ∅ else (X.mark i).stores
def pay (i:X.Index) := if i∈X.dc then inside (X.band i) else (X.mark i).banks
-- use same letters `pole` for forest, `coins` for charged.
def poles := (univ.biUnion X.gaps) ∪ univ.biUnion X.storesN
def coins := univ.biUnion X.pay
lemma poles_g (i:X.Index) : X.gaps i⊆ X.poles:= fun x p=> mem_union_left _ (mem_biUnion.mpr ⟨_,mem_univ i,p⟩)
lemma poles_s (i:X.Index) : X.storesN i⊆ X.poles:= fun x p=> mem_union_right _ (mem_biUnion.mpr ⟨_,mem_univ i,p⟩)
lemma coins_c (i:X.Index) : X.pay i⊆ X.coins:=subset_biUnion_of_mem _ (mem_univ _)
lemma gaps_b (i:X.Index)(x:Link s) : x∈ X.gaps i↔ ∃ k<B.D, ∃ j,x=vl ((X.ditch i).rise k) j:=by
 rw [gaps,mem_filter]; constructor
 · rintro ⟨p,e⟩; rcases link_cases x with ⟨u,g⟩|g; rw [g] at e; exact False.elim (Fin.succ_ne_zero u.2 e); rw [g] at p; obtain ⟨k,v,h⟩:= (X.ditch i).normal_in _|>.mp p; exact ⟨k,v,Fin.tail x.1,g.trans (congrArg (fun k=> vl k _) h)⟩
 rintro ⟨j,k,u,rfl⟩; exact ⟨ (X.ditch i).normal_in _|>.mpr ⟨j,k,rfl⟩,rfl⟩
lemma gap_h (i:X.Index){x:Link s}(p:x∈X.gaps i): x.2=0:=(mem_filter.mp p).2
lemma store_h (i:X.Index) {x:Link s}(p:x∈X.storesN i): ¬ X.Dmark i ∧ x∈ (X.mark i).stores:= by unfold storesN at p; split at p; simp at p; next h=> exact ⟨by simpa using h,p⟩
lemma pay_b (i:X.Index) : X.pay i ⊆ inside (X.band i):= by unfold pay; split; rfl; exact (X.mark i).banks_sub
lemma pole_v {x : Link s}(p : x∈ X.poles) : x.2=0:=by
 rcases mem_union.mp p with p|p <;> obtain ⟨j,v,k⟩:= mem_biUnion.mp p; exact X.gap_h _ k
 obtain ⟨l,q,a,x,rfl⟩:= Tunnel.stores_eq _|>.mp (X.store_h _ k).2; rfl
lemma pole_dis : Disjoint X.poles X.coins:=by
 refine disjoint_left.mpr fun x h v=>?_ ; obtain ⟨i,_,p⟩:= mem_biUnion.mp v; rcases mem_union.mp h with t|t; obtain ⟨j,_,k⟩:= mem_biUnion.mp t; obtain ⟨b,v,l,rfl⟩:= X.gaps_b _ _|>.mp k; obtain ⟨x,v|v⟩:= X.link_overlap (mem_filter.mp k).1 (X.pay_b _ p) <;> exact fl_ne_vl _ _ _ _ v.2.symm
 obtain ⟨j,_,t⟩:= mem_biUnion.mp t; obtain ⟨f,g⟩:= X.store_h _ t; have hi := X.match_uniq (X.pay_b _ p) (show x∈inside (X.band j) from (X.mark j).stores_sub g); subst i; unfold pay at p; rw [if_neg (fun v=> f ((X.dc_index j).mp v))] at p; exact (mem_sdiff.mp p).2 (mem_union_left _ g)
lemma pole_air : Disjoint X.poles X.air:=by
 refine disjoint_left.mpr fun x h v=>?_ ; obtain ⟨i,_,rfl⟩:=mem_image.mp v; exact Fin.succ_ne_zero i.2.2 (X.pole_v h)
lemma pay_uniq {i j : X.Index}{x: Link s} (p:x∈ X.pay i)(v:x∈X.pay j) : i=j:= X.match_uniq (X.pay_b _ p) (X.pay_b _ v)
lemma air_dis : Disjoint X.air X.coins:=by
 refine disjoint_left.mpr fun x h v=>?_ ; obtain ⟨⟨⟨i,k⟩,l,t⟩,_,rfl⟩:= mem_image.mp h; obtain ⟨j,_,p⟩:= mem_biUnion.mp v; let z:=X.skylink ((i,k),(l,t)); let h' := X.pay_b _ p; have he (u:FlatLink s) (v:z=fl (X.depth i 0) u): False:=by have ht:= X.depth_inj l.isLt (Nat.zero_le _) (fl_eq.mp v).1; omega
 have hh(f : X.Dmark j) : False:= by
    obtain ⟨x,⟨rfl,p⟩|⟨p,h⟩⟩:= X.link_overlap (X.sky_mem ((i,k),(l,t))) (show z∈inside (X.band j) from h'); -- tune rfl dep
    · apply he x; rwa [X.depth_zero,if_pos f]
    change j=i+1 at p; subst j; apply he x; rwa [X.depth_zero,if_neg ((X.prev_next i).mp f)]
 unfold pay at p; rw [if_neg (fun t=> hh ((X.dc_index ..).mp t))] at p; obtain ⟨x,⟨e,p'⟩|⟨e,p'⟩⟩:= X.link_overlap (X.sky_mem ((i,k),(l,t))) (show z∈inside (X.band j) from h'); change i=j at e; subst j; exact (mem_sdiff.mp p).2 (mem_union_right _ ((Tunnel.crown_mem ..).mpr ⟨x,Or.inr p'⟩)); change j=i+1 at e; subst j; exact (mem_sdiff.mp p).2 (mem_union_right _ ((Tunnel.crown_mem ..).mpr ⟨x,Or.inl p'⟩))
lemma crown_air (i:X.Index) (p : ¬ X.Dmark i) : (X.mark i).crown ⊆ X.air:=by
 let l:Fin B.D:=⟨B.D-1, Nat.sub_one_lt (B.D_pos.ne')⟩; have h:l.val+1=B.D:=Nat.sub_add_cancel B.D_pos
 intro k e; obtain ⟨x,v|v⟩:= Tunnel.crown_mem ..|>.mp e
 · apply mem_image.mpr; let A:= ((i-1,x.1),(l,x.2)); refine ⟨A,mem_univ _,?_⟩; apply Eq.trans ?_ v.symm; unfold skylink; dsimp only [A]; rw [h,X.depth_D,if_pos ((X.next_prev i).mpr p),sub_add_cancel]; rfl
 apply mem_image.mpr; refine ⟨((i,x.1),l,x.2),mem_univ _,?_⟩; apply Eq.trans ?_ v.symm; unfold skylink; dsimp only; rw [h,X.depth_D,if_neg p]; rfl
lemma kind_of_gap {i:X.Index}{x:Link s}(t:x∈ inside (X.gap i)): x∈ X.air ∨ x∈ X.coins ∨ x∈ X.poles := by
 by_cases p:x∈X.gaps i; exact Or.inr (Or.inr (X.poles_g _ p)); rcases link_cases x with ⟨j,h⟩|h; swap; · exact False.elim (p (mem_filter.mpr ⟨t,congrArg Prod.snd h⟩))
 rw [h] at t; obtain ⟨k,v,w⟩:= (X.ditch i).tang_in _|>.mp t; obtain ⟨a,u,z⟩:= X.depth_flip i v; have hx:= h.trans (congrArg (fun k=> fl k _) (w.trans z)); cases a with
 | zero=> refine Or.inr (Or.inl (X.coins_c (X.dirichlet i) ?_)); rw [hx,pay,if_pos ((X.dc_index _).mpr (X.b_zero i).1)]; exact (X.mark (X.dirichlet i)).crown_sub (X.crownD i j)
 | succ k=> exact Or.inl (mem_image.mpr ⟨((i,j.1),⟨k,u⟩,j.2),mem_univ _,hx.symm⟩)
lemma kind_of_band {i:X.Index}{x:Link s}(t:x∈ inside (X.band i)): x∈ X.air ∨ x∈ X.coins ∨ x∈ X.poles:= by
 by_cases w:i∈ X.dc; exact Or.inr (Or.inl (X.coins_c i (by rwa [pay,if_pos w]))); have hx: x∉ (X.mark i).crown → x∉ (X.mark i).stores → x∈ X.pay i:= by intro h p; unfold pay; rw [if_neg w]; exact mem_sdiff.mpr ⟨t,fun z=> (mem_union.mp z).elim p h⟩
 by_cases p:x∈ (X.mark i).crown; exact Or.inl (X.crown_air i (fun h=> w ((X.dc_index _).mpr h)) p); by_cases q:x∈ (X.mark i).stores; exact Or.inr (Or.inr (X.poles_s _ (by unfold storesN; rw [if_neg w]; exact q))); exact Or.inr (Or.inl (X.coins_c _ (hx p q)))
lemma kind (x:Link s) : x∈X.air ∨ x∈ X.coins ∨ x∈ X.poles:=by obtain ⟨i,p|p⟩:= X.links_cover x; exact X.kind_of_band p; exact X.kind_of_gap p
end YM.CF.BPress.Bands
