import YM.CF.DPress.FD.Warp.Canal
import YM.CF.BPress.Chord
import YM.CF.Cubes.Flag
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Cube Lat Scroll Tw Finset
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m:ℕ}{u:ℝ}
namespace Con
variable {f g:Reign n} {X:Pane n}{x y z:Seat n} {w:Lattice.Walk}
lemma passo (x:Seat n)(s:Step): separation x (x+s.vec)≤1:=by
 rw [separation_comm,separation,add_sub_cancel_left]; unfold Step.vec; split; rw [pdist_neg]; exact pdist_step _; exact pdist_step _
private lemma stepE (s:Step)(x:Seat n)(p:x∈Space z l)(t:(x+s.vec:Seat n)∈Space z l)(h:Must l u X z f):group.chord (s.read (Lattice.gauge f X) x) ≤ cost l u:=by
 obtain ⟨i,h'|h'⟩:=s; · exact h.2 (x,i) (Finset.insert_subset p (Finset.singleton_subset_iff.mpr t))
 unfold Step.read; rw [if_pos rfl,group.chord_inv]; have he: x-step i∈Space z l:= (by change x+-step i∈ Space z l at t; simpa only [sub_eq_add_neg] using t); apply h.2; simp only [Skye.ends, insert_subset_iff, singleton_subset_iff]; exact ⟨he,by change x-step i+step i∈Space z l; rw [sub_add_cancel]; exact p⟩ -- t defeq?
private lemma leg (h:Must l u X z f) (p: separation z x+w.length ≤ globe l):group.chord (travel (Lattice.gauge f X) x w)≤w.length*cost l u:=by
 induction w generalizing x with
 | nil=> simp [travel]
 | cons a w ih=>
    have hp : separation z (x+a.vec)+w.length≤ globe l:=by have ht:=passo x a; have he:= separation_triangle z x (x+a.vec); rw [List.length_cons] at p; omega
    refine (group.chord_triangle (a.read (Lattice.gauge f X) x) (travel (Lattice.gauge f X) (x+a.vec) w)).trans ((add_le_add (stepE a x ?_ ?_ h) (ih hp)).trans_eq ?_)
    · apply (cellP ..).2; omega
    · apply (cellP ..).2; omega
    simp; ring
lemma metricB (x y:E): dist x y=group.colorScale * BPress.chord x y:=by rw [BPress.chord.scale_mul]; exact dist_eq_norm (fund x) (fund y)
lemma carryU (h:Must l u X z f) (p: separation z x+w.length ≤ globe l): dist (f x * travel X x w) (f (stop x w)) ≤ group.colorScale * ((w.length:ℝ)*cost l u):=by
 rw [metricB]; apply mul_le_mul_of_nonneg_left _ group.colorScale_pos.le; unfold BPress.chord; exact (by rw [←travel_gauge]; exact leg h p)
lemma dist_l (x y z:E): dist (x*y) (x*z)=dist y z:=by rw [metricB,BPress.chord.left,metricB y z]
lemma dist_r (x y z:E): dist (y*x) (z*x)=dist y z:=by rw [metricB,BPress.chord.right,metricB y z]
lemma dist_i(x y:E):dist x⁻¹ y⁻¹=dist x y:=by rw [metricB,BPress.chord.inv,metricB x y]
abbrev Treasure(l m:ℕ)(u:ℝ):Prop:= group.colorScale * ((100*(l:ℝ)+1)*cost l u) ≤ 1/(m:ℝ)
lemma offer (p:0≤ u) (t:Treasure l m u) : group.colorScale * cost l u ≤ 1/(m:ℝ):=by
 refine le_trans ?_ t; apply mul_le_mul_of_nonneg_left _ group.colorScale_pos.le; exact le_mul_of_one_le_left (cost_pos p) (le_add_of_nonneg_left (by positivity))
lemma transit (p:0 ≤ u) (κ:Treasure l m u)(h:Must l u X x f)(q:Must l u X y g)(a:close l x y)(b:close l y z) : dist (f y * g z) (f z)≤ 1/(m:ℝ):=by
 let w:=Cube.march y z 1; let t:=w.length; have ht:t≤40*l:= (march_len y z 1 ((separation_comm ..).trans_le b)).trans_eq (by unfold s10; omega)
 let P:=travel X y w; have he(wE r:Reign n): r=r:=rfl; let B:=group.colorScale * ((t:ℝ)*cost l u); have hp:dist (f y * P) (f z) ≤ B:=by
    conv_lhs=> rhs; arg 1; rw [← Cube.arrive y z 1];
    apply carryU h; change separation x y+t≤ _; unfold close s10 at a; unfold globe; omega
 have hz:dist P (g z)≤ B:=by have hy:= carryU (x:=y) (w:=w) q (by change separation y y+t≤110*l; rw [separation_self]; omega); unfold w at hy; rw [q.1,one_mul,Cube.arrive] at hy; exact hy -- semicolon nested
 apply (dist_triangle _ (f y * P) _).trans -- orientation query
 rw [dist_l]; refine (add_le_add ((dist_comm ..).trans_le hz) hp).trans ?_; refine le_trans ?_ κ; have hx:(t:ℝ) ≤ 40*l:=by exact_mod_cast ht
 unfold B; rw [←mul_add,←add_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith only [hx,(Nat.cast_nonneg (α:=ℝ) l)]) (cost_pos p)) group.colorScale_pos.le
-- small after scale. orientation masks can take u smaller any positive.
lemma treasure_earned(l:ℕ)(p:0<m){w:ℝ}(h:0<w):∃ g:ℝ,0<g∧g≤ w ∧ Treasure l m g:=by
 let C:= group.colorScale * ((100*(l:ℝ)+1)*4*(1+globe l)); have hp:0<C:=by unfold C; have h:= group.colorScale_pos; positivity
 let a:ℝ:=1/(m:ℝ)/C; have he:0<a:=by unfold a; positivity
 refine ⟨min a w,lt_min he h,min_le_right ..,?_⟩; unfold Treasure cost; refine Eq.trans_le (b:= min a w*C) (by unfold C; ring) ((le_div_iff₀ hp).1 (min_le_left a w))
end Con
end YM.CF.DPress.FD
