import YM.CF.BPress.Assignment
/-! Thickened gap zones. All widths in gauge steps. `ZoneNear` exact sup balls from closed gap, temporal distance stipulated. Support inclusions and canonical labels use this geometry. No accidentally reading extension toward the opposite gap. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel
open scoped Topology BigOperators Classical Matrix
variable {s : Side} {b: BandWidth} (X : Bands s b) (i : X.Index)
/-- existence of gap site within t at this time, independent of other coordinates. -/
def footTime (u:Per s)(i:X.Index) : Prop:= ∃ k ≤ b.D, u=(X.ditch i).rise k
def ZoneNear (r:ℕ)(x:Per s) := ∃ a:Per s, footTime X a i ∧ delta1 s x a≤r
lemma time_Zone (x : Site s) : footTime X (x 0) i ↔ x∈X.gap i:= ((X.ditch i).internal x).symm
lemma time_zero (x:Per s) (q:footTime X x i)(r:ℕ): ZoneNear X i r x:= ⟨x,q,d_id x|>.le.trans (Nat.zero_le r)⟩
lemma zone_add {u v:Per s}{t r:ℕ}(p:ZoneNear X i r u)(q:delta1 s u v≤t): ZoneNear X i (r+t) v:=by
 obtain ⟨a,b,h⟩:=p; exact ⟨a,b, (d_one_triangle v u a).trans ((add_le_add ((d_sym u v).le.trans q) h).trans_eq (add_comm ..))⟩
lemma zone_of_halo (r:ℕ)(x:Site s): x∈halo r (X.gap i) ↔ ZoneNear X i r (x 0):=by
 rw [halo_spec]; constructor
 · rintro ⟨y,p,q⟩; exact ⟨y 0,(time_Zone X ..).2 p, (Grid.delta_at x y 0).trans ((delta_comm x y).le.trans q)⟩
 rintro ⟨a,f,q⟩; let y:= event a (Fin.tail x); refine ⟨y,(time_Zone X i y).1 (show footTime X a i from f), (delta_le (x:=y) (y:=x) (k:=r)).mpr (fun j=>?_)⟩; refine Fin.cases ?_ ?_ j; exact (d_sym _ a).le.trans q; intro i; rw [show y _=x i.succ by simp [y,event,Fin.tail], d_id]; omega
lemma meet_iff (P: Support s)(r:ℕ) : ¬ Disjoint P (halo r (X.gap i)) ↔ ∃ x∈ P, ZoneNear X i r (x 0):=by rw [not_disjoint_iff]; simp_rw [zone_of_halo]
lemma enclosed {r M:ℕ}{x:Site s}(p:ZoneNear X i r (x 0)) : halo M {x} ⊆ halo (r+M) (X.gap i):=by
 intro j h; obtain ⟨t,g,h⟩:=halo_spec.mp h; rw [mem_singleton.mp g] at h; exact (zone_of_halo ..).mpr (zone_add X i p ((delta_at x j 0).trans h))

/-- behind L&front written via Tunnel.rise/fall. relabel gap halo using **uniform radix shift** even if it consumes marks. -/
def ZoneClock (t : Per s) : X.Index × Fin b.full.val ≃ Per s := X.clock.trans (Equiv.addRight t)
@[simp] lemma z_pos (a:X.Index)(k:Fin b.full.val)(t : Per s) : ZoneClock X t (a,k)= (X.mark a).rise k.val +t:= congrArg (·+t) (X.size a k|>.symm)
lemma step_exists (a b:Per s)(r:ℕ) : delta1 s a b ≤ r → ∃ x:ℤ, x.natAbs ≤ r ∧ a=b+x:=by
 intro t; exact ⟨ (a-b).valMinAbs,t,by rw [ZMod.coe_valMinAbs]; abel⟩
def z_o (t:ℕ) := X.stop i - (t: Per s)
def hall (t:ℕ) := b.D+2*t -- tune X not include
lemma zone_to {r:ℕ} (p:2*r< b.marked.val) : hall (b:=b) r < b.full.val:= by unfold hall; have h:= b.full_eq; omega
-- x suffers parity overlap at seam; shifted clock is allowed.
def Fest (t:ℕ)(p:2*t<b.marked.val) : Tunnel s := ⟨ z_o X i t,⟨ hall (b:=b) t, Nat.add_pos_left b.D_pos _⟩,(Nat.succ_le_of_lt (zone_to p)).trans_lt X.full_lt⟩
lemma hall_eq {r:ℕ}(p:2*r<b.marked.val) : (Fest X i r p).n.val = hall (b:=b) r:=rfl
variable {r:ℕ}
lemma z_iff (p:2*r<b.marked.val)(x:Site s): x∈halo r (X.gap i) ↔ x∈(Fest X i r p).mem:=by
 let F:= Fest X i r p; rw [zone_of_halo, F.internal]; constructor
 · rintro ⟨w,⟨k,h,f⟩,g⟩; obtain ⟨a,t,a'⟩:=step_exists _ _ r g; let L:ℤ:= ↑k+a+↑r; have hp:0≤ L:= by unfold L; omega
   have ht:L.toNat ≤ F.n.val:=by change L.toNat≤ b.D+2*r; unfold L; omega
   refine ⟨L.toNat,ht,?_⟩; rw [a',f]
   change (X.stop i + ↑k) + (a:Per s) = X.stop i-(r:Per s)+ ↑L.toNat; nth_rw 1 [← Int.cast_natCast (R:=Per s) (L.toNat)]; rw [ Int.toNat_of_nonneg hp]; unfold L; push_cast; abel
 rintro ⟨k,v,q⟩; change k ≤ b.D+2*r at v; change x 0=X.stop i- (r:Per s)+ ↑k at q; by_cases e:k<r
 · refine ⟨X.stop i,⟨0,Nat.zero_le _, (Tunnel.rise_zero (X.ditch i)|>.symm)⟩,?_⟩; rw [d_sym]; rw [show X.stop i=x 0+↑(r-k) from (by rw [q,Nat.cast_sub e.le]; abel)]; exact (delta_nat ..).trans (Nat.sub_le ..)
 by_cases f:b.D+r<k
 · refine ⟨(X.ditch i).last,⟨b.D, le_rfl,rfl⟩,?_⟩; have h : x 0 = (X.ditch i).last + ↑(k-(b.D+r)):=by rw [q,Nat.cast_sub f.le]; change _=X.stop i+↑b.D+ _; push_cast; abel
   rw [h]; refine (delta_nat ..).trans ?_; omega
 have h : x 0=(X.ditch i).rise (k-r):= by rw [q]; unfold Tunnel.rise; rw [ditch_o, Nat.cast_sub (by omega : r≤k)]; abel
 exact time_zero X i _ ⟨k-r,by omega,h⟩ r
lemma pill (p:2*r<b.marked.val){i j:X.Index}(h:i≠j): Disjoint (halo r (X.gap i)) (halo r (X.gap j)):=by
 let t:= ((b.marked.val:Per s)-r); have he (i:X.Index)(k:ℕ)(h:k ≤ (Fest X i r p).n.val) : (Fest X i r p).rise k= ZoneClock X t (i,⟨k,h.trans_lt (zone_to p)⟩):=by
    rw [z_pos]; change X.stop i-r+↑k=X.start i+↑k+t; unfold Bands.stop t; abel
 refine disjoint_left.mpr fun x hx hy=>?_ ; obtain ⟨k,v,t⟩:= (Fest X i r p).internal x |>.mp ((z_iff ..).mp hx); obtain ⟨q,e,g⟩:=(Fest X j r p).internal x|>.mp ((z_iff ..).mp hy); exact h (congrArg Prod.fst ((ZoneClock X _).injective (((he _ _ v).symm.trans (t.symm.trans g)).trans (he _ _ e))))

-- chronology-conversions
lemma case_left (p:2*r<b.marked.val){k:ℕ}(v:k≤r): (Fest X i r p).rise k=(X.mark i).fall (r-k):=by
 unfold Tunnel.fall; have ht:r-k≤ b.marked.val:=by omega
 change X.stop i-r+ (k:Per s)= X.start i + ↑(b.marked.val-(r-k)); rw [Nat.cast_sub ht,Nat.cast_sub v]; unfold Bands.stop; abel
lemma case_right (p:2*r<b.marked.val){k:ℕ}(v:r+b.D≤k): (Fest X i r p).rise k= (X.mark (i+1)).rise (k-(r+b.D)):=by
 change X.stop i- r+ (k:Per s)= X.start (i+1)+ ↑(k-(r+b.D)); rw [←X.stop_next, Nat.cast_sub v]; push_cast; abel
lemma case_ditch (p:2*r<b.marked.val){k:ℕ}(v:r≤k): (Fest X i r p).rise k=(X.ditch i).rise (k-r):=by change X.stop i- r+(k:Per s)= X.stop i+↑(k-r); rw [Nat.cast_sub v]; abel
lemma photo_collar (p:2*r < b.marked.val) {t:Per s}(v:ZoneNear X i r t):
    footTime X t i ∨ (∃ k≤r,k≠0 ∧ t=(X.mark i).fall k) ∨ (∃ k ≤ r, k≠0∧t=(X.mark (i+1)).rise k):=by
 let x:= event t (0:Tri s); obtain ⟨j,h,g⟩:=(Fest X i r p).internal x|>.mp ((z_iff ..).mp ((zone_of_halo ..).2 v)) -- tune
 change t=_ at g; change j ≤ b.D+2*r at h; by_cases u:j < r; exact Or.inr (Or.inl ⟨r-j,by omega,by omega,g.trans (case_left _ _ p u.le)⟩); by_cases p':j ≤ r+b.D; exact Or.inl ⟨j-r,by omega, g.trans (case_ditch _ _ p (by omega : r≤j))⟩; exact Or.inr (Or.inr ⟨j-(r+b.D),by omega, by omega,g.trans (case_right _ _ p (by omega : _≤ j))⟩)
lemma movie_collar (p:2*r < b.marked.val){t:Per s}{x:Tri s}(v:vl t x ∈ inside (halo r (X.gap i))) :
    (∃ k < b.D, t= (X.ditch i).rise k) ∨ (∃ k<r,t=(X.mark i).fall (k+1)) ∨ ∃ k<r,t=(X.mark (i+1)).rise k:=by
 have ht : halo r (X.gap i)=(Fest X i r p).mem:= Finset.ext (z_iff X i p); rw [ht] at v; obtain ⟨j,h,g⟩:= Tunnel.normal_in _ _|>.mp v; change j < b.D+2*r at h
 by_cases u:j<r; exact Or.inr (Or.inl ⟨r-j-1,by omega,by rw [show r-j-1+1=r-j by omega]; exact g.trans (case_left _ _ p u.le)⟩); by_cases e:j<r+b.D; exact Or.inl ⟨j-r,by omega,g.trans (case_ditch _ _ p (by omega : r ≤ j))⟩; exact Or.inr (Or.inr ⟨j-(r+b.D),by omega,g.trans (case_right _ _ p (by omega))⟩)

-- near weak array terms require at least one gap site in support! Includes only internal marks cancelled. use connectedness, can't have consecutive micro-neighbors jumping across gap WITHOUT meeting fence.
lemma inside_step {x y:Per s} {W: Tunnel s} (h:delta1 s x y ≤1)(k:ℕ)(t:0<k)(v:k < W.n.val)(g:x=W.rise k) : ∃ i ≤ W.n.val,y=W.rise i:=by
 obtain ⟨i,p,f⟩:=step_exists y x 1 ((d_sym ..).le.trans h); have hx:i=0 ∨ i=1 ∨ i= -1:=by omega
 rcases hx with hx|hx|hx <;> rw [hx,g] at f; exact ⟨k,v.le,by simpa using f⟩; exact ⟨k+1,v,by simpa using f⟩; exact ⟨k-1,by omega, f.trans (show W.rise k+((-1:ℤ):Per s)=_ from (by unfold Tunnel.rise; rw [Nat.cast_sub (show 1≤k from t)]; push_cast; abel))⟩
lemma pack_noGap (x : Support s)(p:Grove (Grid.field 4 s) x)(t:∀ i:X.Index,Disjoint x (X.gap i)): ∃ i,x⊆ X.band i:=by
 have ht(y)(w:y∈ x) (i : X.Index)(k:y∈ X.band i)(j) (v:j∈ x)(h: Grid.delta j y≤1): j ∈ X.band i:=by
   obtain ⟨k,g,Q⟩:= (X.mark i).internal y|>.mp k; have hQ₁:0<k:=by
      by_contra! v; apply disjoint_left.mp (t (i-1)) w; rw [←ditch_mem,(X.ditch (i-1)).internal]; refine ⟨_,le_rfl, ?_⟩; change y 0=(X.ditch (i-1)).last; rw [ditch_last]; rw [Nat.eq_zero_of_le_zero v, rise_zero, X.mark_o] at Q; rw [sub_add_cancel]; exact Q
   have hQ₂:k< (X.mark i).n.val:=lt_of_le_of_ne g (fun f=> disjoint_left.mp (t i) w ((time_Zone ..).1 ⟨0,Nat.zero_le _, by rw [Q,f,Tunnel.rise_zero,X.ditch_o]; exact X.mark_last i⟩))
   apply (X.mark i).internal _ |>.mpr; exact inside_step ((Grid.delta_at y j 0).trans ((delta_comm ..).le.trans h)) k hQ₁ hQ₂ Q
 obtain ⟨o,g⟩:= Grid.inhabited_grove p; obtain ⟨i,v⟩:= X.cover o; have hi:= v.resolve_right (disjoint_left.mp (t _) g); refine ⟨i,fun k w=>?_⟩; suffices ∀ k, Branch.Origin (Grid.field 4 s) x o k→ k∈ X.band i from this k (Branch.rooted p o g k w); intro k z; induction z with|refl=> exact hi| tail _ w ih=> exact ht _ w.1 i ih _ w.2.1 ((Grid.delta_comm ..).le.trans w.2.2)
end YM.CF.BPress.Wealth
