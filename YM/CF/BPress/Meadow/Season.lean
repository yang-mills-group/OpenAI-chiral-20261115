import YM.CF.BPress.Meadow.Hatch
import YM.CF.BPress.SupportN
import YM.CF.BPress.Wealth.Festival
/- Corridor need: copy depth and interpolation spend. In `lem:B-moX` we round the interior using the inherently tiled set within the full Mark. Activate only beyond `floor(n/5)`; use `/4` copy overlap in the construction. Since the purchase works for ANY origin, seam issues already paid including possibility Mark has endpoints off that r_XN grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Dial Grid Grid.Entity Delivery Lute.Kite MeasureTheory RG Wealth
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {s:Side}(W:Tunnel s)
abbrev endAt (e:Link s):Site s:= e.1+step e.2
abbrev corner (W:Tunnel s)(x:Site s):=(x 0-W.o).val
def distanceQ (i:ℕ):= min i (W.n.val-i)
def burial(x:Site s):=distanceQ W (corner W x)
def cloak(H:ℕ) := W.mem.filter fun x=> burial W x ≤H
namespace Tent
open Tunnel
variable {x y:Site s}{d r m:ℕ}
@[simp] lemma corner_co(x:Tri s)(u:d≤W.n.val):corner W (event (W.rise d) x)=d:=by unfold corner; rw [event_time,W.rise_val (Nat.le_succ_of_le u)]
lemma corners (p:x∈W.mem)(x':x 0=y 0) : y∈W.mem∧ burial W x=burial W y:=by
 have he:corner W x = corner W y:=by unfold corner; rw [x']
 exact ⟨arc_mem ..|>.mpr (show corner W y ≤ W.n.val from he ▸ (arc_mem ..|>.mp p)),congrArg (distanceQ W) he⟩ -- tune
lemma corner_rank (x:Site s)(p:x∈W.mem):corner W x≤ W.n.val:= (arc_mem ..).1 p
lemma corner_path (x:Site s):x 0=W.rise (corner W x):=time_eq ..
@[simp] lemma burial_rise {x:Site s}(u:d≤ W.n.val)(p:x 0=W.rise d): burial W x=distanceQ W d:=by rw [burial,corner,p,W.rise_val (Nat.le_succ_of_le u)]
lemma span (p:x∈ W.mem) (a:y∈halo r {x})(g:r≤ burial W x) : y∈W.mem∧ burial W y≤ burial W x+r:=by
 obtain ⟨t,v,u⟩:=halo_spec.mp a; rw [mem_singleton.mp v] at u; obtain ⟨k,h,f⟩:=step_exists _ _ r ((delta_at y x 0).trans (by rw [delta_comm]; exact u)); let n:= corner W x; let N:ℤ:= (n:ℤ)+k
 change r≤min n (W.n.val-n) at g; have he:= corner_rank W x p; change n≤W.n.val at he; have hx:0≤N∧ N.toNat≤W.n.val:=by unfold N; omega
 have ht:y 0=W.rise N.toNat:=by rw [f,(corner_path W x), Tunnel.rise,Tunnel.rise, ←Int.cast_natCast (R:= Per s) N.toNat,Int.toNat_of_nonneg hx.1,add_assoc W.o]; unfold N; push_cast; rfl -- tune
 refine ⟨(W.internal _).mpr ⟨_,hx.2,ht⟩, ?_⟩; rw [burial_rise W hx.2 ht]; change distanceQ W _ ≤ distanceQ W n + _; unfold N distanceQ; omega
lemma distance_step(i:ℕ): distanceQ W i ≤ distanceQ W (i+1)+1∧ distanceQ W (i+1)≤ distanceQ W i+1:=by unfold distanceQ; omega
lemma stepDeep (i:Link s)(p:i∈inside W.mem) : burial W i.1 ≤ burial W (endAt i)+1 ∧ burial W (endAt i)≤ burial W i.1+1:=by
 obtain ⟨t,u⟩:= inside_iff ..|>.mp p; rcases link_cases i with ⟨x,b⟩|b <;> rw [b] at p ⊢
 · rw [show burial W (fl (i.1 0) x).1=burial W (endAt (fl (i.1 0) x)) by apply (corners W (x:=(fl (i.1 0) x).1) (inside_iff ..|>.mp p).1 (y:=endAt (fl (i.1 0) x)) ?_).2; simp [fl,endAt,Ne.symm (Fin.succ_ne_zero x.2)]]; omega
 obtain ⟨k,f,e⟩:= (W.normal_in _).1 p; rw [e]; let x:=Fin.tail i.1; have hu:endAt (vl (W.rise k) x)=event (W.rise (k+1)) x:=by unfold endAt; rw [rise_succ]; exact event_up ..
 rw [burial_rise W f.le (show (vl (W.rise k) x).1 0 =_ from rfl),hu, burial_rise W f (event_time ..)]; exact distance_step W _
@[simp] lemma cloak_sub (r:ℕ):cloak W r⊆ W.mem:=filter_subset ..
@[simp] lemma cloak_mem (p:x∈W.mem) : x∈ cloak W r↔ burial W x≤ r:=by simp [cloak,p]
abbrev body (W: Tunnel s):= W.n.val/5
-- speed supports using extension only beyond `body`; includes ALL sites there plus interior margin if both incident.
abbrev ward (k:Tiling s) (W:Tunnel s):Prop:= cloakT k+1 ≤ body W ∧ body W+cloakT k≤ W.lips ∧ 4 ≤ W.n.val

variable {k:Tiling s}
lemma corridor(h:ward k W)(i:Link s)(v:i∈inside W.mem)(g:i∉inside (cloak W (body W))) : let S(t:Support s):= Lattice.halo (cloakT k) t; S {i.1}⊆ W.mem∧ S {endAt i} ⊆ W.mem:=by
 intro S; simp only [inside_iff] at v g; have m:= stepDeep W i (inside_iff ..|>.mpr v); rw [cloak_mem W v.1,cloak_mem W v.2] at g; change ¬(burial W i.1≤_∧burial W (endAt i) ≤_) at g
 constructor<;>intro x p; exact (span W v.1 p (by have u:=h.1; simp only [endAt] at *; omega)).1; exact (span W v.2 p (by have u:=h.1; simp only [endAt] at *; omega)).1
lemma pin_corridor(h:ward k W)(i:Link s)(v:i∈inside W.mem)(g:i∉inside (cloak W (body W))) (x:Site s)(p:x=i.1∨x=endAt i)(s:x∈cloak W (body W)) : halo (cloakT k) {x}⊆ cloak W W.lips:=by
 intro y u; have hp:=stepDeep W i v; have t:cloakT k≤burial W x:=by
    obtain ⟨a,b⟩:=inside_iff ..|>.mp v; rw [inside_iff,cloak_mem W a,cloak_mem W b] at g; have hm:= h.1; rcases p with p|p <;> simp only [p,endAt] at * <;> omega
 obtain ⟨a,b⟩:=inside_iff ..|>.mp v; have hx:= cloak_mem W (cloak_sub W _ s)|>.1 s; have hb :=h.2.1; refine mem_filter.mpr ?_; obtain ⟨l,T⟩:=span W (x:=x) (cloak_sub W _ s) u t; refine ⟨l,T.trans ?_⟩; omega
lemma hood(k r:Side) (t:r=k):r.val ≤ k.val:=t.le -- tune type
end Tent
end YM.CF.BPress.Meadow
