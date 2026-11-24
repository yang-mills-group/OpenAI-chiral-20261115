import YM.CF.BPress.Meadow.Fruit
-- Keep extensions using only readings of accepted support. Uniform B-moX
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Dial Grid Grid.Entity Delivery Lute.Kite MeasureTheory RG
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {s:Side} {k:Tiling s}(D:Entity k 4)(U: Micro s)(S T:Support s) (p:k.r=1)
-- preprocess support. MASK all outside data
abbrev matsN (k:Tiling s) (S: Support s):=univ.filter fun i:Entity k 4 => i.hull ⊆ S
def moss(U:Micro s) := fun i=> if i∈inside S then U i else 1
def crop (H:marks s):=fun x:Site s=>if x∈S then H x else Seed
@[simp] lemma mat_since : D∈matsN k S ↔ D.hull⊆ S:=by simp [matsN]
lemma moss_m : Measurable (moss S):= measurable_pi_lambda _ fun i=> by unfold moss; split; exact measurable_pi_apply _; exact measurable_const
lemma crop_m : Measurable (crop S):= measurable_pi_lambda _ fun i=>by unfold crop; split; exact measurable_pi_apply _; exact measurable_const
@[simp] lemma hullin(x: Site s): x∈D.hull ↔ D.contains x:=by simp [hull]
-- walls
lemma rooted (J:Entity k 4) (i:Axis) (u:i∈J.axes)(b:Bool): (J.wall i b).hull⊆ J.hull:=by
 intro x p; obtain ⟨z,v',h⟩:= (hullin (J.wall i b) x).mp p
 let R:= if b then k.b.val else 0; let v:=update z i R; have ht:J.Valid v:= by
    intro j; by_cases e:j=i; rw [e,if_pos u,show v i=R from update_self ..]; unfold R; split; rfl; omega
    unfold v; rw [update_of_ne e]; simpa [wall,e] using v' j
 have he:z i=0:= (J.wall i b).dim_off v' (notMem_erase _ _); refine (hullin J x).mpr ⟨v,ht,?_⟩; rw [← h]; funext j; unfold heart v R; by_cases e:j=i; subst j; cases b <;> simp [he,wall,Tiling.R]; cases b <;> simp [wall,e]
lemma graded(k:Tiling s): Graded (matsN k S):=fun i h j p b => by rw [mat_since]; exact (rooted _ _ p _).trans ((mat_since ..).mp h)
lemma hull_heart (a:Coord 4)(h:D.Valid a): D.heart a ∈ D.hull:= (hullin ..).mpr ⟨a,h,rfl⟩
include p
lemma tick_heart(a i):D.heart (tick a i)=D.heart a+step i:=by rw [D.step_eq,p, PNat.val_ofNat]; exact hop_one ..
lemma tick_inside(a i)(h:D.Valid (tick a i)):(D.heart a,i)∈inside D.hull:= (inside_iff ..).mpr ⟨hull_heart D _ (D.valid_tick h), ((tick_heart D p a i) ▸ hull_heart D _ h)⟩
omit D p in
lemma inside_cov {S T:Support s}(h:S⊆ T):inside S⊆inside T:=fun x p=>(inside_iff ..).mpr ⟨h ((inside_iff ..).mp p).1,h ((inside_iff ..).mp p).2⟩
include p
variable {S} {m : ℝ}
lemma valid_curvature (Q:D.hull ⊆ S)(h:Rings U S m): D.flat (moss S U) m:=by
 let e(a:Coord 4):=D.heart a; have ht(a i)(p':D.Valid (tick a i)):D.along (moss S U) a i=U (e a,i):= if_pos (inside_cov Q (tick_inside D p a i p'))
 have hx(a)(i j:Axis)(t:D.Valid a)(u:D.Valid (tick a i))(s:D.Valid (tick a j))(r:D.Valid (tick (tick a i) j))(f:i<j): tension U 1 1 (e a) i j ≤ m:=by
    rw [ζ]; refine h (i:=(e a,⟨(i,j),f⟩)) ?_ -- tune arg
    intro y g; rw [touched, square_corners] at g; simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at g; rcases g with l|l|l|l|l <;> subst y <;> apply Q
    · exact hull_heart D _ t
    · rw [← tick_heart D p a i]; exact hull_heart D _ u
    · rw [← tick_heart D p a i,← tick_heart D p (tick a i) j]; exact hull_heart D _ r
    · rw [← tick_heart D p a j]; exact hull_heart D _ s
    exact hull_heart D _ t
 intro a i j A B C H g; have hv:D.Valid (tick (tick a j) i):=tick_comm a i j ▸ H
 rw [ht a i B,ht a j C, ht (tick a i) j H, ht (tick a j) i hv]; suffices h: tension U 1 1 (e a) i j≤m by
    unfold e; rw [tick_heart D p a i,tick_heart D p a j]; unfold tension e at h; simpa only [line_one,hop_one] using h
 rcases lt_or_gt_of_ne g with f|f; exact hx _ _ _ A B C H f; rw [tension_sym]; exact hx _ _ _ A C B hv f
variable (H:marks s){v :ℝ}
lemma speed_normal {a i}(T:D.hull⊆ S)(h:D.Valid (tick a i)) : Zips.speed D (moss S U) H a i=urgent U (D.heart a,i) H:=by
 unfold speed Grid.Entity.along; rw [moss,if_pos (inside_cov T (tick_inside D p _ _ h)), tick_heart D p]; exact urgent_flip U (D.heart a,i) H
lemma hold (h:T⊆S)(t:D.hull ⊆ T)(f: Alert U T H (1/(k.b.val:ℝ))): Zips.Speed D (moss S U) (crop S H) 1:=by
 intro a i p'; let x:=D.heart a; have he: urgent U (x,i) H≤_:=(f _ (inside_cov t (tick_inside D p _ _ p'))); rw [speed_normal _ _ p _ (t.trans h) p']; change urgent U (x,i) _≤ _; unfold urgent crop; rw [if_pos (h (t (hull_heart D a (D.valid_tick p')))),if_pos (h (t ((inside_iff ..|>.mp (tick_inside D p a i p')).2)))]; exact he
end YM.CF.BPress.Meadow
