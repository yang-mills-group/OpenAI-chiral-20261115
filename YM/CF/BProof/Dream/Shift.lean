import YM.CF.BProof.Dream.Stage
/-! Amended side depth read through `R_H`. Ensure actual candidate agrees at v=0,2, and
at γ=1 it agrees for all v. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Function Metric Extension.Mar Mag Cube Tenant Branch Fock Dial SU Tulip Lat Spin Complex
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {t s : ℝ}(i:Fin 5)
def factorQ (s t:ℝ):= 1-(1-s)*second t+(1-s)*tertiary t
lemma fQ_p(x t:ℝ)(p:x∈Zone): factorQ x t ∈ Zone:=by
 obtain ⟨p,u⟩:=p; by_cases h:t≤1; · have he: second t∈Zone:=easeZ _; obtain ⟨ht,hq⟩:=he; unfold factorQ; rw [ter_down (by linarith),mul_zero,add_zero]; constructor <;> nlinarith
 have he : tertiary t∈Zone:= easeZ _; obtain ⟨ha,hb⟩:=he; unfold factorQ; rw [second_up (by linarith),mul_one]; constructor <;> nlinarith
lemma fQ_s : ContDiff ℝ ∞ (Function.uncurry factorQ):= ((contDiff_const.sub ((contDiff_const.sub contDiff_fst).mul (secondS.comp contDiff_snd)))).add ((contDiff_const.sub contDiff_fst).mul (terS.comp contDiff_snd))
def side (t:ℝ) : Stamp := motion (locus i) (BM 1 t)
def amend (s t:ℝ): Stamp:= side i t+ (Gig i (factorQ s t)-BBz i)
lemma amend0 (s:ℝ)(p:t≤1/2): amend i s t= side i t:=by unfold amend factorQ; rw [second_down p,ter_down (by linarith),mul_zero,sub_zero,add_zero,Gig_1,sub_self,add_zero]
lemma amend_late(s:ℝ)(h:1/2≤t): amend i s t=Gig i (factorQ s t):=by unfold amend side; rw [BM_1 (by linarith),←BBz_eq]; abel
lemma amend1 (t:ℝ):amend i 1 t=side i t:= by unfold amend factorQ; rw [sub_self,zero_mul,zero_mul, sub_zero,add_zero,Gig_1,sub_self,add_zero]
lemma TG_side (v:ℝ): TG i 1 v=amend i 0 v:=by
 by_cases p:v≤1/2; rw [amend0 i _ p,TG,(scene i).earlyN v p,threes_motion,side,BM,one_mul]
 · rw [amend_late _ _ (by linarith),factorQ, sub_zero,one_mul,one_mul,Gig]; by_cases h:v≤1; rw [ter_down (by linarith),add_zero,TG,(scene i).midN v (by linarith) h]; rw [second_up (by linarith),sub_self,zero_add,TG,(scene i).tallN v (by linarith)] -- tune indentation
lemma amend_top (s:ℝ)(h:7/4≤t):amend i s t=BBz i:=by rw [amend_late _ _ (by linarith),factorQ,second_up (by linarith),ter_up h,mul_one,sub_add_cancel,Gig_1]
lemma amend_flat (v:ℝ)(h:7/8≤v)(u:v≤5/4): amend i 0 v=BB:= by rw [← TG_side,TG,(scene i).bT _ v h u]; rfl
lemma amend_z (s t:ℝ) : amend 0 s t= BM 1 t:=by unfold amend side; rw [show locus 0=1 from (by simp [locus]), motion_one,Gig_z,BBz_zero,sub_self,add_zero,id_eq]
lemma amend_s : ContDiff ℝ ∞ (Function.uncurry (amend i)):= (moldS contDiff_const (BM_s.comp (contDiff_const.prodMk contDiff_snd))).add (((Gig_s i).comp fQ_s).sub contDiff_const) -- tune A invalid def
lemma amend_seal (s t:ℝ): SealH (amend i s t):=by by_cases p:t≤1/2; rw [amend0 i _ p]; exact seal_move _ (BM_seal ..); rw [amend_late _ _ (by linarith)]; exact sealG ..
-- applied with frame h (notation price orient G= h^(-1)). Fuse at γ=1
-- correction Δ= h⁻¹ z.
def rosy (g:E)(s t:ℝ) := motion (g*center i) (amend i s t)
lemma rosy_fuse (g:E)(t:ℝ): rosy i g 1 t= motion g (BM 1 t):=by rw [rosy,amend1,side,← motion_seq,show g* center i * locus i=g from (by unfold locus; group)]
lemma rosy0P (g:E)(s:ℝ)(h:t≤1/2): rosy i g s t=motion g (BM 1 t):=by rw [rosy,amend0 _ _ h,side,← motion_seq,show g* center i * locus i=g from (by unfold locus; group)]
lemma rosy0 (g:E)(s:ℝ): rosy i g s 0=Pair.fullM (turn g apex.val):=by rw [rosy0P _ _ _ (by norm_num), BM_x, compass]
lemma rosyT (g:E)(s:ℝ)(h:7/4≤t): rosy i g s t=motion g BB:=by rw [rosy,amend_top _ _ h,BBz_eq, ←motion_seq,show g* center i * locus i=g from (by unfold locus; group)]
lemma rosyG(s t:ℝ):rosy i (locus i) s t=amend i s t:=by rw [rosy, show locus i*center i=1 from inv_mul_cancel _,motion_one,id_eq]
lemma rosy_s (g:E): ContDiff ℝ ∞ (Function.uncurry (rosy i g)):= moldS contDiff_const (amend_s _)
lemma rosy_seal (g:E)(s t:ℝ): SealH (rosy i g s t):= seal_move _ (amend_seal ..)
end YM.CF.BProof.Dream
