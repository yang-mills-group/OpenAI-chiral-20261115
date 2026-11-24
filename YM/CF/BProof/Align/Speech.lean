import YM.CF.BProof.Align.Board
/-! Compress with a uniform bound based on c. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I] {A P Q:Op I}{c:ℝ}{x:Ket I}
lemma behind (p:IsStarProjection P)(a:IsStarProjection A)(h:c • P ≤ P*(1-A)*P)(v:c≤1) (X:Ket I) : ‖acts P (acts A X)‖^2 ≤ (1-c)*‖X‖^2:=by
 let w:=P*A; have he : w*star w=P*A*P:=by unfold w; rw [star_mul,a.isSelfAdjoint,p.isSelfAdjoint, ←mul_assoc, mul_assoc P A A,a.isIdempotentElem]
 have ht : w*star w ≤ (1-c) • (1:Op I):=by
    rw [he]; refine le_trans (b:=(1-c) • P) ?_ (smul_le_smul_of_nonneg_left (sub_nonneg.mp p.one_sub.nonneg) (sub_nonneg.mpr v))
    rw [mul_sub,mul_one,sub_mul,p.isIdempotentElem] at h; rw [sub_smul,one_smul]; exact le_sub_comm.mp h -- tune
 have hz : ‖w‖^2≤1-c:= (by have hx:= betweenNorm (sub_nonneg.mpr v) (mul_star_self_nonneg w) ht; simpa only [CStarRing.norm_self_mul_star,pow_two] using hx)
 rw [←act_mul]; exact (pow_le_pow_left₀ (norm_nonneg _) (actuary w X) _).trans ((mul_pow ..).trans_le (mul_le_mul_of_nonneg_right hz (sq_nonneg _)))
-- remove duplicate
namespace Board
variable (b: Board A P Q c)
include b
lemma clipNorm : ‖clip A P‖ ≤ c⁻¹ :=by
 rw [clip, norm_star,send]; refine (norm_mul_le ..).trans ?_; rw [norm_star]; have he := (norm_mul_le ..).trans (mul_le_one₀ (b.a.norm_le A) (norm_nonneg _) (b.p.norm_le P)); exact (mul_le_of_le_one_right (norm_nonneg _) he).trans (invNorm b.nice b.doorB)
lemma clip_x : clip A P * (P*wedgeP A P)=wedgeP A P:=by
 rw [show P*wedgeP A P=P*A from ?_,←mul_assoc, b.clipIn]; swap
 · have h:=congrArg star b.shadow; rw [star_mul,star_mul,b.a.isSelfAdjoint,b.p.isSelfAdjoint,b.drawn.isSelfAdjoint] at h; exact h
 let L:=P; rw [←b.clipIn,mul_assoc,b.wedgePformed]; unfold clip send; rw [star_mul,star_star,b.child.frameI.star_eq] -- tune
lemma avail (h:acts (wedgeP A P) x=x): c*‖x‖≤ ‖acts P x‖:=by
 have he: ‖acts (clip A P) (acts P x)‖ ≤ c⁻¹*‖acts P x‖ := (actuary ..).trans (mul_le_mul_of_nonneg_right b.clipNorm (norm_nonneg _)); have ht:acts (clip A P) (acts P x)=x:=by
    calc _=acts (clip A P) (acts P (acts (wedgeP A P) x)):=by rw [h]
         _ = _:= by rw [← act_mul P,← act_mul,b.clip_x,h] -- indent
 rw [ht,mul_comm, ← div_eq_mul_inv] at he; rw [mul_comm]; exact (le_div_iff₀ b.nice).mp he
lemma grain (h:acts (wedgeQ A P) x=x) : c*‖x‖^2≤‖acts (space P Q) x‖^2:=by
 have he:= splitOrth x (upCut b.p b.q b.pq); have ht:= behind b.q b.leaves b.loftHole b.bare x; rw [h] at ht; rw [act_add,show acts P x=0 from (by nth_rw 1 [← h]; rw [← act_mul,b.rimLeft,act_zero]), zero_add] at he; unfold space; linarith
lemma gramMil (h:acts (wedgeQ A P) x=x): c*‖x‖ ≤ ‖acts (space P Q) x‖:=by
 have hp:=b.nice; refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 ?_; rw [mul_pow]; exact (mul_le_mul_of_nonneg_right (show c^2≤c from by nlinarith only [hp, b.bare, mul_le_mul_of_nonneg_left b.bare hp.le]) (sq_nonneg _)).trans (b.grain h) -- tune
end Board
end YM.CF.BProof.Align
