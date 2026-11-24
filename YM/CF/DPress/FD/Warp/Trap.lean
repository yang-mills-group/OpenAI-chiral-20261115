import YM.CF.DPress.FD.Warp.Track
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row Wilson
open Cube (More assembly)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
variable {a:ℝ}{T:Trophy n l u} {I:Type*}[Fintype I] {V:Vision (More n) r I} (U:Plan V l m)(P:Leader T m 5 a) (x:I) (η μ:Cotton n)(X:Pane n){i:Seat n}{s:Axis}
local notation "W"=> pat U x
local notation "Y"=>realF U P x η X
-- good edge estimate. If the row contributes at the left end, it has close(frame) cost for the right link at the adjacent end too. need scale l positive. then pay weight variation.
lemma edge_z {D E:Key}{t w:ℝ}(h:E∈ Row.tilt)(p:0 ≤ t)(u:t≤1) (a b:ℝ)(hp:dist t w ≤ a)(v:dist D E≤ b):dist (t • D) (w • E) ≤ a*rad+b:=by
 apply (dist_triangle _ (t • E) _).trans; rw [add_comm (dist _ _),dist_smul₀, Real.norm_of_nonneg p,dist_eq_norm,←sub_smul,norm_smul,←dist_eq_norm]; exact add_le_add (mul_le_mul hp (Row.age h) (norm_nonneg _) (dist_nonneg.trans hp)) ((mul_le_of_le_one_left dist_nonneg u).trans v)
lemma premium (h:baseP ≤ a)(v:0<l)(p:0<m)(t:0≤u)(κ:Treasure l m u)(hi:Grade l u X (W i))(hj:Grade l u X (W (i+step s))) : dist (sail (Y i) (X (i,s))) (Y (i+step s)) ≤ rate a/(m:ℝ):=by
 let j:= i+step s; let xi:=U.β x i; let xj:=U.β x j; let S:=X (i,s); have he:0 ≤ a:=base_p.trans h; have hz:0 < (m:ℝ):= (by exact_mod_cast p); have h0:0 ≤ rate a/(m:ℝ):=by unfold rate; positivity
 have hp: separation i j ≤ 1:= Work.E01.sep_step_le i s; have hg: δR xi xj ≤ 2/(m:ℝ):=div_le_div_of_nonneg_right (by exact_mod_cast U.cost x i j hp) hz.le
 unfold realF; rw [if_pos hi, if_pos hj]; refine (dist_pi_le_iff h0).2 ?_; rintro (k|k); swap; · change dist ((0:Key)*_) 0≤_; rw [zero_mul,dist_self]; exact h0
 let A(y):= T.G η k X y; let F:= fund (A i*S); let V:=fund (A j);
 change dist ((roadmap xi k • fund (A i))* fund S) (roadmap xj k • V) ≤ _; rw [Algebra.smul_mul_assoc,← fund_mul]; have ht: dist (roadmap xi k) (roadmap xj k) ≤ 2/(m:ℝ):= (nearT xi xj p k).trans hg; have hb:(2/(m:ℝ))*rad+1/(m:ℝ) ≤ rate a/(m:ℝ):=by
    rw [div_mul_eq_mul_div,← add_div]; refine div_le_div_of_nonneg_right ?_ hz.le; unfold rate; unfold baseP at h; linarith only [h]
 by_cases y:k∈ W i
 · refine (edge_z (plant (A j)) (money ..).1 (money ..).2 _ _ ht ?_).trans hb
   have hy: close l k i:= pathR U x rfl y; unfold close s10 at hy; have he:= carryU (w:=[posDir s]) (x:=i) (T.bill η k X (hi k y)) (by simp only [List.length_singleton]; unfold globe; omega); change dist (fund (T.G η k X i*S)) (fund (T.G η k X j)) ≤ _; rw [spin_cost]; refine le_trans (show dist _ _≤ group.colorScale * cost l u from ?_) (offer t κ)
   simpa only [List.length_singleton,Nat.cast_one,one_mul,travel,mul_one,Step.pos_read,stop,Step.vec_pos] using he
 rw [show roadmap xi k=0 from rm_dim xi k y] at *; rw [zero_smul,dist_zero_left,norm_smul,Real.norm_of_nonneg (money ..).1]; exact le_trans (b:= (2/(m:ℝ))*rad+1/(m:ℝ)) (by rw [dist_zero_left,Real.norm_of_nonneg (money ..).1] at ht; unfold V; rw [Row.bloom]; apply le_trans (mul_le_mul_of_nonneg_right ht alive.le); exact le_add_of_nonneg_right (by positivity)) hb -- tune rw wildcard
end Turf
end YM.CF.DPress.FD
