import YM.CF.BPress.Meadow.Season
/- cert inside copy collar and extraction. F.frame left transforms universally. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Filter Finset NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Dial Grid Grid.Entity Delivery Lute.Kite MeasureTheory RG Net Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {s:Side}{T: Sheet.Atlas}{L y C C':ℝ}{b:ℕ}(W:Tunnel s)(F:Net s T L y C C' b) (U: Micro s)(p : Duo s) {k:Tiling s}
namespace Frame
open Tunnel
def haloM := W.book (fun n=> W.access p.1 p.2 n)
lemma halo_left {i:ℕ}(h:i≤W.lips): confine (W.rise i) (haloM W p)=p.1:=by rw [haloM,W.booked _ (le_trans h (W.collar_ends.1.trans (le_of_lt W.cut_lt))),access,if_pos (h.trans W.collar_ends.1)]
lemma halo_right {i:ℕ} (h:i≤ W.n.val)(q:W.lip ≤ i): confine (W.rise i) (haloM W p)=p.2:=by rw [haloM,W.booked _ h,access,if_neg (W.collar_ends.2.1.trans_le q).not_ge]
lemma halo_meas: Measurable (haloM W):= W.book_cont.measurable.comp (f:=fun p:Duo s=>fun n:ℕ=>W.access p.1 p.2 n) (measurable_pi_lambda _ (fun i=>by unfold access; split; exact measurable_fst; exact measurable_snd))
local notation "A"=> W.orient U
local notation "S"=> cloak W W.lips
abbrev amt(y:ℝ):= xi y+sigmaN y
structure Firm(W:Tunnel s)(F:Net s T L y C C' b)(U:Micro s)(p:Duo s):Prop where
 tail: 0<y
 loaded:T.Coasts y
 seats:p∈ T.pairs y (W.reads U)
 marked: markN F W U p≠0
 prior:4≤ W.n.val

variable (H:Firm W F U p)
include H
lemma inside_cost : chord.Close (gauge (haloM W p) A) 1 (Meadow.cloak W W.lips) (amt y):=by
 let q:= (T.pairs_ok y p (W.reads U) H.loaded).mp H.seats; intro e a c; have ha:e∈inside (cloak W W.lips):= inside_iff ..|>.mpr ⟨a,c⟩
 have ht:=Tent.cloak_sub W W.lips
 have hb :=inside_cov ht ha; let M:=haloM W p; let X:=gauge M A; rcases link_cases e with ⟨x,v⟩|v
 · rw [v] at ha hb ⊢; obtain ⟨i,p',u⟩:= W.tang_in x|>.1 hb; rw [u] at ha ⊢; let e':=fl (W.rise i) x; change chord (horizontal (W.rise i) X x) 1≤_; unfold X; rw [adj_gauge]; let α:=F.template W (W.reads U) p; have hv:= (F.isclose W p H.marked (xi_pos H.tail).le e' (inside_iff ..|>.1 (inside_cov ht ha)).1 ((inside_iff ..|>.1 (inside_cov ht ha)).2)); let B:= confine (W.rise i) M; apply (chord.triangle _ (adjust B (horizontal (W.rise i) α) x) _).trans; rw [adj_repair]; apply add_le_add (show chord (horizontal (W.rise i) (W.orient U) x) (horizontal (W.rise i) α x)≤xi y from hv); rw [chord.one,show horizontal _ α=F.tarH W (W.reads U) p i from F.readH W _ _ p'] -- pattern fix
   have hx:= (mem_filter.mp (show e'.1∈ S from (inside_iff ..|>.1 ha).1)).2; rw [Tent.burial_rise W p' (x:=e'.1) rfl] at hx -- tune
   by_cases h:i ≤ W.lips; rw [F.tar_o W _ _ h, show B=p.1 from halo_left W p h]; exact q.1.2 _; have hs:W.lip ≤ i:=by unfold distanceQ at hx; unfold Tunnel.lip; omega; -- tune new line
   rw [F.tar_last W _ _ hs, show B=p.2 from halo_right W p p' hs]; exact q.2.2 _
 rw [v] at ha hb ⊢; obtain ⟨i,k,f⟩:= W.normal_in _|>.1 hb; let v:=Fin.tail e.1; let z:=vl (W.rise i) v; rw [f] at ha ⊢; have hx:= (mem_filter.mp (show z.1 ∈ S from (inside_iff ..|>.1 ha).1)).2; have hy:= (mem_filter.mp (show endAt z∈ S from (inside_iff ..|>.1 ha).2)).2
 rw [Tent.burial_rise W k.le (show z.1 0=W.rise i from rfl)] at hx; rw [Tent.burial_rise W k (show endAt z 0=W.rise (i+1) by unfold endAt z; simp [vl])] at hy
 unfold distanceQ Tunnel.lips at hx hy; have h:=H.prior; change chord (BPress.normal (W.rise i) X v) 1 ≤_; unfold X; rw [vl_gauge,W.orient_uncut _ k (by unfold cut; omega), ←W.rise_succ i, show confine (W.rise i) _=confine (W.rise (i+1)) M from ?_]; swap
 · unfold M; by_cases t:i≤ W.cut
   · rw [halo_left,halo_left]; all_goals unfold Tunnel.lips; unfold cut at t; omega
   rw [halo_right _ _ k.le,halo_right _ _ k]; all_goals unfold lip; unfold lips; unfold cut at t; omega
 change chord (_*1*_ ) 1 ≤_; rw [mul_one, mul_inv_cancel,chord.refl]; unfold amt; have h:=H.tail; have t:=xi_pos h; have he:=inv_pos.mpr (heigh_pos y) -- search
 rw [sigma_price]; positivity
-- transforms M
omit H
lemma gauge_halo (a:Mach s): haloM W (p*(W.framesE a)⁻¹)= haloM W p*(W.branchM a)⁻¹:=by
 funext i; unfold haloM branchM book; simp only [Pi.mul_apply,Pi.inv_apply]; split_ifs <;> rename_i h
 · unfold branch access; split <;> rfl
 simp
lemma gauge_universe(a:Mach s): F.atlasG W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹)=F.atlasG W (W.reads U) p * (W.branchM a)⁻¹:=by
 have ht:= F.deck_a; funext i; unfold atlasG branchM book; simp only [Pi.mul_apply,Pi.inv_apply]; split_ifs; rw [F.deck_a]; rfl; simp
end Frame
end YM.CF.BPress.Meadow
