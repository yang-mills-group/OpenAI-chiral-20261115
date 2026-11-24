import YM.CF.BProof.Mapping.Grid
import YM.CF.BProof.Angular.Janitor
import YM.CF.BProof.Angular.Avenue
import YM.CF.BProof.Angular.Vic

/- north Lam time ticks; flag allocation, even when band wraps. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Lattice Finset Function Filter Grid Circle Cube Angular Angular.Yard
open scoped Topology BigOperators Classical
variable {s: Side}(Y: Yard s)
namespace Posts
variable (i : Y.Index)(x: Per s)
def night (x:Per s):= post x -- placeholder next after cut at base
 where post (x:Per s):= owner Y.grid (atL Y.fromMark (cut Y.long+1)) x
abbrev hours:=cut Y.long+1
lemma first (i:Y.Index): origin Y.grid (atL Y.fromMark (hours Y)) i= atL (Y.u i) (hours Y):=by unfold atL origin u Strips.pole origin; abel
lemma session {a:ℕ}(h:a<Y.grid.count.val) : night Y (atL (atL (Y.u i) (hours Y)) a)=i:= by rw [← first]; exact owner_native Y.grid _ i h
lemma shift_before (a:ℕ) (p:a<hours Y) : night Y (atL (Y.u i) a)=i-1:=by
 let L:=Y.grid.count.val; let q:=hours Y; have hu:q≤ Y.long:= cut_lt Y.long Y.long_pos; have hp:q<L:=hu.trans_lt Y.long_lt; apply Eq.trans _ (session Y (i-1) (a:=L+a-q) (by omega)); have ht: atL (Y.u (i-1)) L=Y.u i:=by rw [atL,← show Y.grid.count.val=L from rfl,← show Y.long+Y.short=Y.grid.count.val from Y.total, Nat.cast_add, ← add_assoc, show Y.u _+(Y.long:Per s) = Y.v (i-1) from Y.last_pole _, show Y.v _+(Y.short:Per s) = Y.u (i-1+1) from Y.last_edge _,sub_add_cancel]
 congr 1; unfold atL hours at *; rw [←ht, add_assoc,← Nat.cast_add,add_assoc,←Nat.cast_add, show cut Y.long+1+(L+a-q)=L+a from ?_]; unfold q hours at *; omega -- tune
lemma shift_after {a:ℕ}(p:hours Y ≤ a)(h:a≤Y.long): night Y (atL (Y.u i) a)=i:= by
 apply Eq.trans _ (session Y i (a:=a-hours Y) (Nat.lt_of_le_of_lt (Nat.sub_le ..) (h.trans_lt Y.long_lt))); unfold atL; rw [add_assoc,←Nat.cast_add,Nat.add_sub_of_le p]
lemma band (h:Y.Band i x): night Y x=Y.location i (flag (Y.u i) x Y.long):= by
 unfold location; split
 · rename_i he; apply Eq.trans _ (shift_after Y i ((flag_true ..).1 he) h); rw [atL,add_along]
 next he=> apply Eq.trans _ (shift_before Y i (a:=along (Y.u i) x) ?_); rw [atL,add_along]; unfold hours; exact Nat.lt_succ_of_le ((flag_false ..).1 (Bool.eq_false_iff.mpr he)) -- tune
lemma gap (h:Y.Gap i x): night Y x=i:=by
 let a:=along (Y.v i) x; have hp:=Y.last_pole i; have hx:=Y.last_edge (i:=i); have ht:hours Y ≤ Y.long:= cut_lt Y.long Y.long_pos
 apply Eq.trans _ (session Y i (a:=Y.long+a-hours Y) (by have hz:= Y.total; have hp:0<hours Y:=Nat.zero_lt_succ _; change a≤ Y.short at h; omega)); rw [atL,atL,add_assoc,←Nat.cast_add,Nat.add_sub_of_le (show hours Y≤Y.long+a from by omega),Nat.cast_add,←add_assoc,show Y.u i+(Y.long:Per s)=Y.v i from hp, show Y.v i+(a:Per s)=x from add_along ..]
-- hot and cold small nD collar tags, stay gap for all vic
lemma vic {r:ℕ}(p:2*r+1<Y.long)(h:Y.Vic i r x): night Y x=i:=by
 rcases Y.vic_split i r x (by omega) h with h|h|h; rw [band Y i x h.2,location,if_pos ((flag_true ..).2 ?_)]
 · have hz:= Y.before_u i h.2; have hx:=h.1; unfold cut; omega
 · exact gap Y i x h
 rw [band Y (i+1) x h.2, location, (flag_false ..).2 (show along (Y.u (i+1)) x ≤ cut Y.long from by have := h.1; unfold cut; omega)]; simp -- tune
lemma neighbor (y:Per s)(k:ℕ)(h:δ x y ≤ k*Y.grid.count.val): δ (night Y x) (night Y y) ≤ k:= post_lip Y.grid _ _ _ k h
lemma vic_offset (x y:Site s)(h:Y.Vic i 0 (time x)){k}(u:separation x y≤ k): Y.Vic i k (time y):=by simpa only [zero_add] using Y.vic_trans i 0 (time x) (time y) k h ((time_jump x y).trans u) -- tune Y?
end Posts
end YM.CF.BProof.Mapping
