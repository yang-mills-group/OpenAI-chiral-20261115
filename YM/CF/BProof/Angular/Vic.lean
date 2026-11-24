import YM.CF.BProof.Site.Interval
import YM.CF.BProof.Angular.Layout
import YM.CF.BProof.Site.Micro

/-! Unique gap of any fixed-neighborhood use. Also deep- and no gap- neighborhoods.
Dimensions measured in gauge steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Lattice Finset Cube Micro Circle -- Moment maybe absent
open scoped Topology BigOperators Classical
variable {s:Side}(Y:Yard s)(i:Y.Index)(r:ℕ)(x:Per s)

def Vic := ∃ y:Per s,Y.Gap i y∧ δ y x≤r
lemma padding (p: 2*r<Y.long): Y.short+2*r < Y.grid.count.val:=by have := Y.total; omega
lemma vic_pad (p:2*r<Y.long): Y.Vic i r x ↔ padded (Y.v i) x Y.short r:= (pad_iff (Y.v i) x Y.short r ((Y.padding r p).trans Y.count_lt)).symm
lemma vic_beam (p:2*r<Y.long) (h:Y.Vic i r x) : owner Y.grid (before Y.fromGap r) x=i:=by
 have hv:origin Y.grid (before Y.fromGap r) i=before (Y.v i) r:=by unfold origin before; unfold v Strips.edge origin; abel
 have he:along (before (Y.v i) r) x≤_:= (Y.vic_pad i r x p).1 h; apply Eq.trans _ (owner_native Y.grid (before Y.fromGap r) i (lt_of_le_of_lt he (Y.padding r p))); rw [native,hv,add_along]
lemma vic_unique (p:2*r<Y.long){j:Y.Index}(h:Y.Vic i r x)(k:Y.Vic j r x): i=j:= (Y.vic_beam i r x p h).symm.trans (Y.vic_beam j r x p k)
lemma vic_nearer (d:ℕ)(k:r≤d) (h:Y.Vic i r x): Y.Vic i d x:=by obtain ⟨y,h,hp⟩:=h; exact ⟨y,h,hp.trans k⟩
lemma vic_trans (y:Per s)(b:ℕ)(h:Y.Vic i r x)(k:δ x y≤ b): Y.Vic i (r+b) y:=by
 obtain ⟨z,h,u⟩:=h; exact ⟨z,h,(d_one_triangle z x y).trans (Nat.add_le_add u k)⟩
lemma time_jump (x y:Site s): δ (time x) (time y)≤ separation x y:=component_le (x-y) _
lemma outside_gap (h:Y.Gap i x): Y.Vic i r x:= ⟨x,h,by simp [δ,d_id]⟩
lemma before_u {x:Per s}(h:Y.Band i x): along (Y.u i) x+along x (Y.v i)=Y.long:= by rw [← u_in]; exact (distance (Y.u i) x (Y.v i) (h.trans_eq (Y.u_in _).symm)).symm

def Cold := along x (Y.v i)≤r ∧ Y.Band i x
def Hot := along (Y.u i) x≤r ∧ Y.Band i x
lemma vic_split (p:2*r<Y.long) (h:Y.Vic i r x): Y.Cold i r x ∨ Y.Gap i x ∨ Y.Hot (i+1) r x:= by
 rcases pad_wing (Y.v i) x Y.short r ((Y.vic_pad i r x p).1 h) ((Y.padding r p).trans Y.count_lt) with h|h|h
 · exact Or.inr (Or.inl h)
 · refine Or.inl ⟨h,?_⟩; unfold Band; by_contra q; have he:= Y.u_in i; have hk:=distance (Y.u i) (Y.v i) x (by omega); by_cases hv:x=Y.v i; subst x; omega
   have hx:=lag x (Y.v i) hv; have := along_lt (Y.u i) x; omega
 have he : along (Y.u (i+1)) x≤r:= (show Y.v i+(Y.short:Per s)=Y.u (i+1) from Y.last_edge i) ▸ h; exact Or.inr (Or.inr ⟨he, show Y.Band (i+1) x from he.trans (by omega)⟩)
lemma cold_vic (h:Y.Cold i r x): Y.Vic i r x:=⟨Y.v i,by simp [Gap],(δle _ r x).2 (Or.inr h.1)⟩
lemma hot_vic (h:Y.Hot (i+1) r x): Y.Vic i r x:= ⟨Y.u (i+1),(Y.v_in i).le,(δle _ r x).2 (Or.inl h.1)⟩
lemma hot_vic' (h:Y.Hot i r x): Y.Vic (i-1) r x:= by apply hot_vic; simpa using h
lemma vic_halo {a:Site s} (h:Y.Vic i r (time a)) {b:ℕ} {x:Site s}(u:x∈halo b {a}) : Y.Vic i (r+b) (time x):= Y.vic_trans _ _ (time a) _ _ h ((time_jump ..).trans (by simpa [halo_spec] using u))
lemma margin (h:∀ j:Y.Index,¬ Y.Vic j r x) : Y.Band (Y.twinsBand x) x∧ r < along (Y.u (Y.twinsBand x)) x ∧ r<along x (Y.v (Y.twinsBand x)):=by
 rcases Y.edge_from x with k|k; swap; · exact False.elim (h _ (Y.outside_gap _ r x k.le))
 let i:=Y.twinsBand x; exact ⟨k.le,lt_of_not_ge (fun q=>h _ (Y.hot_vic' i r x ⟨q,k.le⟩)),lt_of_not_ge (fun q=>h _ (Y.cold_vic i _ _ ⟨q,k.le⟩))⟩
lemma seated {a:Site s} (h:∀ j:Y.Index, ¬ Y.Vic j r (time a)) : halo r {a}⊆ Y.band (Y.twinsBand (time a)):=by
 intro x hx; let i:=Y.twinsBand (time a); obtain ⟨hl,hv,hp⟩:=Y.margin _ (time a) h; change Y.Band i (time a) at hl; let v:=time a; change r<along (Y.u i) v at hv; change r<along v (Y.v i) at hp; apply mem_strip.mpr; have hg:= Y.before_u i hl; change along (Y.u i) v+along v (Y.v i)=_ at hg
 apply deep (Y.u i) v Y.long r hv.le (by omega) (by have := Y.count_small; have := Y.long_lt; omega) _ ((time_jump ..).trans (by simpa [halo_spec] using hx)) -- tune

/-- all connected supports not fully Mark internal hit a gap-near site. -/
lemma gain (T: Support s)(v:T.Nonempty)(ht:Loc T)(q:∀ i:Y.Index,¬T⊆ Y.band i): ∃ x∈T, ∃ i, Y.Vic i 1 (time x):=by
 by_contra! u
 obtain ⟨x,hx⟩:=v; let i:=Y.twinsBand (time x); have h0:x∈Y.band i:=mem_strip.mpr (Y.margin 1 _ (u x hx)).1; apply q i; intro y hy
 induction ht x hx y hy with
 | refl=> exact h0
 | @tail a b _ h ih=>
   have ha:=Y.u_part i _ (mem_strip.mp (ih h.1)); rw [← ha]; exact Y.seated 1 (u a h.1) (halo_spec.mpr ⟨a,mem_singleton_self _,h.2.2⟩)
end YM.CF.BProof.Angular.Yard
