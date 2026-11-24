import YM.CF.BProof.Angular.Draw

/-! Exact alternating band/gap layout. forest normals and disjoint sampling sets. Include
where-qualifications for unused coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side}

structure Yard (s : Side) extends Strips s where
 even_q : Even q.val
namespace Yard
variable (Y:Yard s)(i:Y.Index)(x:Per s)
abbrev u := Y.pole i
abbrev v := Y.edge i
-- expose Strips fields via alias? dots lookup fails? add
abbrev Band := along (Y.u i) x≤Y.long
abbrev Gap := along (Y.v i) x≤Y.short
abbrev D := dirichlet Y.q Y.even_q i
lemma next : Y.D (i+1)↔¬Y.D i:=dirichlet_step ..
lemma prev : Y.D (i-1)↔¬Y.D i := by
 have h:=Y.next (i-1); rw [sub_add_cancel] at h; tauto
lemma lL : Y.long+1<s.val:=by have :=Y.long_lt.trans Y.count_lt; have hz:=Y.long_lt; have :=Y.count_lt; omega
lemma dD : Y.short+1<s.val:=by have hz:=Y.short_lt; have :=Y.count_lt; omega
lemma u_in : along (Y.u i) (Y.v i)=Y.long:=by unfold u v; rw [← Y.last_pole]; exact along_add _ (Y.long_lt.trans Y.count_lt)
lemma v_in : along (Y.v i) (Y.u (i+1))=Y.short:=by unfold u v; rw [← Y.last_edge]; exact along_add _ (Y.short_lt.trans Y.count_lt)
lemma u_part (h:Y.Band i x) : Y.twinsBand x=i:=Y.band_heir h
lemma v_part (h:Y.Gap i x) : Y.twinsGap x=i:=Y.gap_heir h
lemma common (h:Y.Band i x){j:Y.Index}(e:Y.Gap j x) : (x=Y.u i∧i=j+1) ∨ x=Y.v i∧j=i := by
 by_cases hq:x= Y.v i
 · subst x; exact Or.inr ⟨rfl,(Y.v_part j _ e).symm.trans (Y.v_part i _ (by simp [Gap]))⟩
 have hh:along (Y.u i) x<Y.long:= lt_of_le_of_ne h (fun v=> hq ((add_along ..).symm.trans (v.symm ▸ Y.last_pole i)))
 have hx : along (Y.v j) x=Y.short:=le_antisymm e (le_of_not_gt (fun v=> Y.edge_disjoint hh v)); have v:x=Y.u (j+1):= (add_along ..).symm.trans (hx.symm ▸ Y.last_edge j)
 have hi : i=j+1:= (Y.u_part i x h).symm.trans (Y.u_part (j+1) x (v ▸ (by simp [Band] : Y.Band (j+1) (Y.u (j+1))))) -- tune
 exact Or.inl ⟨by rw [hi]; exact v,hi⟩

/-- swept (both layers). -/
def Cut : Prop := along (Y.u i) x=cut Y.long
def NBroom (x:Per s) := ∃ i, ¬ Y.D i ∧ along (Y.u i) x<Y.long ∧ ¬ Y.Cut i x
def GBroom (x:Per s) := ∃ i, along (Y.v i) x<Y.short
def trunks := univ.filter (fun p:Bond s=> p.2=0 ∧ (Y.GBroom (time p.1) ∨ Y.NBroom (time p.1)))
def leases := if Y.D i then washes (Y.u i) Y.long else watches (Y.u i) Y.long
lemma leases_w {b:Bond s}(h:b∈ Y.leases i): Wet (Y.u i) Y.long b:= by rw [leases] at h; split at h; exact (mem_wash ..).1 h; exact ((mem_watch ..).1 h).1
lemma leases_dist {i j:Y.Index}{b:Bond s}(h:b∈Y.leases i)(g:b∈Y.leases j): i=j:=by
 have he:=mem_strip.mp (Y.leases_w i h).1; have h:=mem_strip.mp (Y.leases_w j g).1; exact (Y.u_part i _ he).symm.trans (Y.u_part j _ h)
@[simp] lemma trunk_v (p:Space s) : vert x p∈ Y.trunks↔Y.GBroom x∨Y.NBroom x:=by simp only [trunks,mem_filter,mem_univ,true_and,time_join,vert]
@[simp] lemma trunk_h (p:Space s)(n:TAxis) : horiz x p n ∉Y.trunks:= by simp only [trunks,mem_filter,mem_univ,true_and,horiz,Fin.succ_ne_zero,false_and,not_false_eq_true]
lemma trunk_dist : Disjoint Y.trunks (Y.leases i):=by
 rw [disjoint_left]; intro b h g; rcases whichBond b with ⟨x,p,rfl⟩|⟨x,p,n,rfl⟩; swap; exact trunk_h Y _ _ _ h
 have hx:= (wet_v (Y.u i) Y.long Y.lL).1 (Y.leases_w _ g); rw [trunk_v] at h; rcases h with ⟨j,h⟩|⟨j,h,h',e⟩
 · exact Y.edge_disjoint hx h
 have hu:i=j:= (Y.u_part i x hx.le).symm.trans (Y.u_part j x h'.le); subst j; rw [leases,if_neg h] at g; exact e ((watch_v _ _ _ p Y.long_pos Y.lL).1 g)
def rent := univ.biUnion (fun i=> Y.leases i)
abbrev field := (Y.trunks ∪ Y.rent)ᶜ
lemma rents {b:Bond s}: b∈Y.rent ↔ ∃ i,b ∈ Y.leases i := by simp [rent]
lemma field_spec (b:Bond s) : b ∈ Y.field ↔ b ∉ Y.trunks ∧ ∀ i, b∉ Y.leases i:=by simp only [field,mem_compl,mem_union,rents,not_or,not_exists]
lemma leased {b:Bond s}(h:b ∈ Y.leases i) : b ∉ Y.trunks:=fun u=> disjoint_left.mp (Y.trunk_dist i) u h
lemma fieldV (p:Space s): vert x p ∉ Y.field := by
 rw [field_spec]; rintro ⟨h,g⟩; obtain h'|v:= Y.edge_from x
 · generalize hi:Y.twinsBand x=i at h'; by_cases hd:Y.D i
   · exact g i (by rw [leases,if_pos hd,mem_wash,wet_v (Y.u i) _ Y.lL]; exact h')
   by_cases hp:Y.Cut i x
   · exact g i (by rw [leases,if_neg hd,watch_v (Y.u i)]; exact hp; exact Y.long_pos; exact Y.lL)
   exact h ((Y.trunk_v x p).2 (Or.inr ⟨_,hd,h',hp⟩))
 exact h ((Y.trunk_v x p).2 (Or.inl ⟨_,v⟩))

/-- Time in lift of gap i, measured FROM D end. -/
abbrev dEnd := if Y.D i then Y.v i else Y.u (i+1)
abbrev nEnd := if Y.D i then Y.u (i+1) else Y.v i
def depth := if Y.D i then along (Y.v i) x else Y.short-along (Y.v i) x
def atD (d:ℕ) := if Y.D i then atL (Y.v i) d else atL (Y.v i) (Y.short-d)
lemma atD_mem {d:ℕ}(h:d≤Y.short) : Y.Gap i (Y.atD i d):=by
 unfold Gap atD; split; rw [along_add _ (by have := Y.dD; omega)]; exact h; rw [along_add _ (by have := Y.dD; omega)]; omega
lemma at_depth (h:Y.Gap i x): Y.atD i (Y.depth i x)=x:=by
 unfold Gap at h; unfold atD depth; split <;> rename_i H
 · exact add_along ..
 rw [ Nat.sub_sub_self h]; exact add_along ..
lemma depth_at {d:ℕ}(h:d≤Y.short): Y.depth i (Y.atD i d)=d:=by
 unfold depth atD; split <;> rename_i H
 · rw [along_add _ (by have := Y.dD; omega)]
 rw [along_add _ (by have :=Y.dD; omega),Nat.sub_sub_self h]
lemma depth_le (h:Y.Gap i x): Y.depth i x≤Y.short:=by unfold depth; split; exact h; exact Nat.sub_le ..
@[simp] lemma atD_zero : Y.atD i 0=Y.dEnd i:=by unfold atD dEnd; split; simp [atL]; rw [Nat.sub_zero]; exact Y.last_edge i
@[simp] lemma atD_full : Y.atD i Y.short=Y.nEnd i:=by unfold atD nEnd; split; exact Y.last_edge i; simp [atL]
lemma dEnd_mem : Y.Gap i (Y.dEnd i):= Y.atD_zero i ▸ Y.atD_mem i (Nat.zero_le _)
lemma nEnd_mem : Y.Gap i (Y.nEnd i):= Y.atD_full i ▸ Y.atD_mem i le_rfl
lemma noPay (h:Y.Gap i x)(p:Space s)(j:TAxis): horiz x p j∈Y.field ↔ 0<Y.depth i x:=by
 have hu'(a:Y.Index) (hd:Y.D a)(hh:Y.Band a x) : horiz x p j ∈ Y.leases a:=by rw [leases,if_pos hd,mem_wash,wet_h]; exact hh
 rw [field_spec,and_iff_right (show horiz x p j ∉ Y.trunks from Y.trunk_h x p j)]; constructor
 · intro g; by_contra! e
   have k : x=Y.dEnd i:=(Y.at_depth i x h).symm.trans (by rw [Nat.le_zero.mp e,Y.atD_zero])
   unfold dEnd at k; split at k<;>rename_i c <;> subst x
   · exact g i (hu' i c (Y.u_in i).le)
   exact g (i+1) (hu' (i+1) ((Y.next i).2 c) (by simp [Band]))
 intro c a hx; obtain ⟨H,hH⟩:=Y.leases_w a hx; have hh: Y.Band a x:=mem_strip.mp H; have hD:=Y.next i
 rcases Y.common a x hh h with ⟨e,rfl'⟩|⟨e,rfl⟩ <;> rw [leases] at hx <;> subst x <;> try subst a
 · split at hx
   · rename_i k; rw [depth,if_neg (hD.mp k), Y.v_in i,Nat.sub_self] at c; omega
   rw [watch_h] at hx; simp [along_self] at hx -- danger time coord simp
 split at hx
 · rename_i k; rw [depth,if_pos k,along_self] at c; omega
 rw [watch_h,Y.u_in _] at hx; omega
lemma fieldH (p:Space s)(j:TAxis): horiz x p j∈ Y.field ↔ ∃ i:Y.Index,Y.Gap i x ∧ 0<Y.depth i x:=by
 constructor; swap; · rintro ⟨i,h,g⟩; exact (Y.noPay i x h p j).2 g -- tune
 intro c; have H : ∃ i:Y.Index,Y.Gap i x:=by
   rcases Y.edge_from x with h|h; swap; · exact ⟨_,h.le⟩ -- tune
   generalize he:Y.twinsBand x=i at h; change along (Y.u i) x <Y.long at h; have hv:= ((Y.field_spec _).1 c).2 i; rw [leases] at hv
   split at hv
   · exact absurd ((mem_wash ..).2 ((wet_h ..).2 h.le)) hv
   rw [watch_h,and_iff_left h] at hv; have hg:Y.u i=x:=along_zero.mp (by omega)
   exact ⟨i-1,by rw [← hg]; nth_rw 2 [← sub_add_cancel i 1]; exact (Y.v_in _).le⟩
 obtain ⟨i,H⟩:=H; exact ⟨i,H,(Y.noPay i x H p j).1 c⟩
end Yard
end YM.CF.BProof.Angular
