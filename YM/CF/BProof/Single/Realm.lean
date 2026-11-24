import YM.CF.BProof.Single.Sheet
/-! Congruence speed on Stamp fields. Carries any H on these cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter NormedSpace Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint SU.Pair
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s:Side}{U:Bkg s}{Q:Site s→Stamp}{δ:ℝ}
def Speed (U:Bkg s)(H:Site s→Stamp)(r:ℝ):Prop:=∀ (x:Site s)(i:Axis), ‖motion (U (x,i)) (H (x+step i)) - H x‖≤r
namespace Speed
variable (h:Speed U Q δ)
include h
lemma weaker {r:ℝ}(e:δ≤r): Speed U Q r:=fun x i=>(h x i).trans e
lemma pos : 0 ≤ δ:= (norm_nonneg _).trans (h 0 0)
lemma stepV (d:Step)(x:Site s): ‖motion (d.read U x) (Q (x+d.vec)) - Q x‖≤ δ:=by
 obtain ⟨i,q|q⟩:=d; exact h ..; unfold Step.read; simp only [Step.vec,Step.used,ite_true]; rw [← motion_frame (U (x-step i,i)),← motion_seq,mul_inv_cancel,motion_one,norm_sub_rev]; convert h (x-step i) i using 1; rw [sub_add_cancel]; rw [← sub_eq_add_neg]; rfl
lemma stroll (w:Walk)(x:Site s): ‖motion (travel U x w) (Q (stop x w)) - Q x‖ ≤ w.length*δ:=by
 induction w generalizing x with
 | nil=> simp [travel,stop,motion_one]
 | cons a w ih=>
    unfold travel stop; rw [motion_seq]; refine (norm_sub_le_norm_sub_add_norm_sub _ (motion (a.read U x) (Q (x+a.vec))) _).trans ?_; push_cast; rw [motion_frame]; exact (add_le_add (ih _) (h.stepV a x)).trans_eq (by rw [List.length_cons]; push_cast; ring)
lemma transport (g:Site s→ E): Speed (gauge g U) (fun z=> motion (g z) (Q z)) δ:=by
 intro x i; let L:=g (x+step i); unfold Lattice.gauge; rw [← motion_seq,inv_mul_cancel_right,motion_seq,motion_frame]; exact h ..
end Speed
lemma mark_stop (o x:Site s): stop o (markD o x)=x:=by
 nth_rw 1 [← wrap_lift o]; rw [← wrap_stop_cover, ← add_zero (lift o),stop_trans]; simp only [markD,route_end,map_add,wrap_lift]; abel
lemma mark_cost (o x:Site s)(w:ℕ)(h:x∈bay (terr s) o w): (markD o x).length≤4*w:=by
 apply route_size; intro i; have hx: separation x o≤w:=by rw [separation_comm]; exact (bay_mem _).mp h
 simpa using (component_le (x-o) i).trans hx
lemma hue_staff (h:Speed U Q δ)(o x:Site s)(w:ℕ)(g:x∈bay (terr s) o w): ‖motion (hue U o x) (Q x)-Q o‖ ≤ 4*(w:ℝ)*δ:=by
 have ht:= h.stroll (markD o x) o; rw [mark_stop] at ht; exact ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast mark_cost o x w g) h.pos)
-- buy on blown window: operator-profile + stamp. No global choices of gauge on subsequent estimates.
lemma hue_wall (U:Bkg s)(o: Site s){k:ℕ}(e:2*k+2<s.val){d:ℝ}(h:0≤d)(g:Guard U d) (i:Lattice.Edge (Site s))(p:i∈leaks (bay (terr s) o k)): scenery (gauge (hue U o) U i) 1 ≤priceF k d:= by
 rw [scenery,brand_one]; exact gauge_light o i.1 i.2 k (mem_filter.mp p).2.1 (mem_filter.mp p).2.2 e U d h g
end YM.CF.BProof.Spin
