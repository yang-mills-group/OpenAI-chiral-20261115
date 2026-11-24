import YM.CF.BProof.Mapping.Profile

/- cardinal bill for mapcard; halos including dl-upgrades, padding after base.
Use images compress as inequality multiplied by Lc. output Reach for License. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.House
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable {s c: Side}(Y:Yard s)(g:Ratio c s)(S:Hall s)(T:Support s)
variable (C:ℕ)(p:Fund Y g S C)(r:ℕ)
abbrev StackQ := Deep.Stack Y T (Deep.D Y)
/-- helper map uses all sites, even in empty connected support inputs (extend). -/
def lunch (T:Support s) := Grid.collar (T.image (addr Y g)) 1
structure Seek : Prop where
  near : ∃ x∈T, ∃ i,Y.Vic i r (time x)
  path : Micro.Loc T
  depth : r < Deep.D Y
-- `term τ exponential size` abuse. price at α=const
abbrev fourBill (r:ℕ) := (2*r+1)^4
abbrev rate (b k C:ℕ) := 7^4 + 2* allowD b k C
structure Queue (r:ℕ) where
 Z : Grid.Sites (Season Y c)
 funds : Grid.Conn Z 1
 bound : Z.card*g.count.val ≤ fourBill r*(7^4*g.count.val + House.rate S.X.size S.k C*T.card)
 lunch : Grid.collar (House.lunch Y g T) r ⊆ Z
 antenna (i:Y.Index)(Q:Support s)(h:Q∈StackQ Y T i)(b:Bool) : ∃ L:Lesson S C Q, Grid.collar (aisles Y g L.Z (location Y i b)) r⊆Z
lemma shift_h (t:Seek Y T r)(i:Y.Index): ¬ T⊆Deep.IntS Y (Deep.D Y) i:=by
 obtain ⟨x,hx,j,h⟩:= t.near; intro hq; apply Deep.height Y (Deep.D Y) i r ((Deep.riseS ..).1 (hq hx)) t.depth _ h; have he:= t.depth; have := Deep.D_le Y; omega
include p
lemma contracts : g.count.val ≤ Y.grid.count.val:= p.block.trans ((show Deep.D Y≤Y.long by have :=Deep.D_le Y; omega).trans Y.long_lt.le)
lemma can (t:Seek Y T r)(u:ℕ) : Nonempty (Queue Y g S T C u):=by
 let W:= House.lunch Y g T; let Qt:=Season Y c
 let a:=g.count; let k:=g.count.val
 let V:=allowD S.X.size S.k C
 have hc(i:Y.Index)(b:Bool)(Q:Support s)(h:Q∈ StackQ Y T i): ∃ R : Grid.Sites Qt, Conn R 1∧ (∃ x∈ W,x∈ R)∧ R.card*k ≤ V*Q.card∧ ∃ F:Lesson S C Q,R=aisles Y g F.Z (location Y i b):=by
    have hx:=Deep.pricePart Y T (Deep.D Y) i h t.path (shift_h Y T r t i); obtain ⟨A⟩:= teach Y g S C p Q (Deep.brings Y T _ i Q h).2.2 (Deep.brings Y T _ i Q h).1 hx; exact ⟨_,aisles_conn Y g S C p Q A (location Y i b),aisles_meet Y g S i T C Q h A b,cap_aisles Y g S C p Q A hx _, A, rfl⟩ -- tune
 choose! R hR hq pR F hF using hc -- F not unique per side; choose! Lesson may lack Nonempty outside; adjust
 let D:= univ.biUnion fun i:Y.Index=> univ.biUnion fun b:Bool=> (StackQ Y T i).biUnion (R i b)
 let P(i:Y.Index)(b:Bool):= W∪(StackQ Y T i).biUnion (R i b)
 have hW:Conn W 1:= Grid.collar_conn _ _ (compression_conn _ g.count (contract Y g (contracts Y g S C p)) _ t.path)
 have hp : Conn (W∪D) 1 := by
    let I : Finset ((Y.Index×Bool)× Support s):=univ.filter fun x=>x.2∈ StackQ Y T x.1.1
    let f(x:(Y.Index×Bool)× Support s):= R x.1.1 x.1.2 x.2; have h : I.biUnion f=D:=by ext; simp [I,f,D]; grind -- tune
    rw [←h]; apply pile I hW f; exact fun i hi=> hR _ _ _ (mem_filter.mp hi).2; exact fun i hi=> hq _ _ _ (mem_filter.mp hi).2
 let Z:=Grid.collar (W∪ D) u; have hU: W.card*k ≤ 7^4*(T.card+k):= compression (addr Y g) a (contract Y g (contracts Y g S C p)) _ 1 t.path
 have hj(i:Y.Index)(b:Bool): ((StackQ Y T i).biUnion (R i b)).card*k≤ V*∑ S'∈StackQ Y T i,S'.card:=by apply le_trans (Nat.mul_le_mul_right _ card_biUnion_le); rw [sum_mul,mul_sum]; exact sum_le_sum (pR i b)
 have hk(i:Y.Index): (univ.biUnion fun b:Bool=> (StackQ Y T i).biUnion (R i b)).card*k≤2*V*∑ S'∈StackQ Y T i,S'.card:=by apply le_trans (Nat.mul_le_mul_right _ card_biUnion_le); rw [sum_mul,mul_assoc]; exact (sum_le_sum fun b _=> hj i b).trans_eq (by rw [sum_const]; simp) -- tune
 have hD:D.card*k ≤ (2*V)*T.card:= by
    apply le_trans (Nat.mul_le_mul_right _ card_biUnion_le); rw [sum_mul]; apply le_trans (sum_le_sum fun i _=> hk i); rw [← mul_sum]; gcongr; exact Deep.attending ..
 refine ⟨⟨Z,Grid.collar_conn _ u hp,?_,Grid.collar_le subset_union_left le_rfl,?_⟩⟩
 · apply le_trans (Nat.mul_le_mul_right _ (Grid.collar_volume ..)); change _*(2*u+1)^4*k ≤ _; rw [mul_comm (_:ℕ) ((2*u+1)^4), mul_assoc]; apply Nat.mul_le_mul_left; apply (Nat.mul_le_mul_right k (card_union_le ..)).trans; rw [add_mul]; apply (Nat.add_le_add hU hD).trans_eq; -- tune trans_eq le
   unfold rate V k; ring -- tune inequalities
 intro i Q h b; refine ⟨F i b Q h,Grid.collar_le ?_ le_rfl⟩; rw [← hF i b Q h]; exact fun x hx=> mem_union_right _ (mem_biUnion.mpr ⟨_,mem_univ i,mem_biUnion.mpr ⟨_,mem_univ b,mem_biUnion.mpr ⟨Q,h,hx⟩⟩⟩)
end YM.CF.BProof.Mapping.House
