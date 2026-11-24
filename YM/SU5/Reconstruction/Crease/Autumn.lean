import YM.SU5.Reconstruction.Crease.Garden
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Moth
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame Opera Multiplier
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H D K: Hilbert} (C:Clasp K H D)(θ:ℝ)(p:θ∈twilight)(A:K.Op)
local notation "W"=>C.Cabin
local notation "P"=>C.angle
local notation "R"=>(1-C.angle:K.Op)
local notation "e"=> fareGate C
noncomputable def clover (b:Bool)(t:ℝ): K.Op:=(e b)^2 * W (-t)
local notation "FR"=> clover C
local notation "iA"=>C.motion
local notation "r"=>reel iA
local notation "z"=>Opera.spin θ
local notation "S"=> wage C
variable (x y:K)
include p
lemma fruition : (∫ t:ℝ,cup θ t*(inner ℂ (FR false t x) (A (FR true t y)) + z*inner ℂ (FR true t x) (A (FR false t y))))= inner ℂ (P (R x)) (A (P (R y))) := by
 let F' (n:ℕ)(t:ℝ):= cup θ t*(inner ℂ (r (S n) t false x) (A (r (S n) t true y)) + z*inner ℂ (r (S n) t true x) (A (r (S n) t false y)))
 have hp(n:ℕ): ∫ t,F' n t= inner ℂ (royal iA (S n) x) (A (royal iA (S n) y)):= finbot iA θ p (S n) (fun s=> wage_price C s n) A x y -- tune
 have k(n:ℕ)(t:ℝ)(b:Bool)(x:K): ‖r (S n) t b x‖ ≤‖x‖:= ((r (S n) t b).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (here ..))
 let M:= ‖x‖*(‖A‖*‖y‖); have h(t:ℝ)(i:ℕ)(b b':Bool): ‖inner ℂ (r (S i) t b x) (A (r (S i) t b' y))‖ ≤ M:=by unfold M; refine (norm_inner_le_norm ..).trans (mul_le_mul (k _ _ _ _) ((A.le_opNorm _).trans ?_) (norm_nonneg _) (norm_nonneg _)); gcongr; apply k
 refine tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (F:=F') (fun t=> ‖cup θ t‖*(M+‖z‖*M)) (fun n=> by unfold F'; fun_prop) ((redeem θ p).norm.mul_const _) ?_ ?_) ?_ -- order?
 · intro n; refine Eventually.of_forall fun t=>?_ ; unfold F'; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact (norm_add_le ..).trans (add_le_add (h _ _ _ _) (by rw [norm_mul]; gcongr; apply h))
 · exact Eventually.of_forall fun t=> tendsto_const_nhds.mul (((wave C x t false).inner (A.continuous.continuousAt.tendsto.comp (wave C y t true))).add (tendsto_const_nhds.mul ((wave C x t true).inner (A.continuous.continuousAt.tendsto.comp (wave C y t false)))))
 simp_rw [hp]; exact (glowPath C x).inner (A.continuous.continuousAt.tendsto.comp (glowPath C y))
def hive (p q : K)(x:ℝ) := inner ℂ ((P*R) p) ((W x * A * W (-x)) ((P*R) q))
-- assumes spool.Full direction. for all B=PR ports.
lemma transit {N:K.Op}(h:∀ p q:K,inner ℂ (P (R p)) (N (P (R q)))=inner ℂ (R (R p)) (A (P (P q)))+z*inner ℂ (P (P p)) (A (R (R q)))):
 (∫ t:ℝ,cup θ t*hive C N x y t)=inner ℂ ((P*R) x) (A ((P*R) y)):= by
 have ph(t:ℝ) : hive C N x y t= inner ℂ (FR false t x) (A (FR true t y))+z*inner ℂ (FR true t x) (A (FR false t y)):=by
    have hn(w:K): W (-t) (P (R w))= P (R (W (-t) w)):= Eq.symm (DFunLike.congr_fun ((C.oneCabin (show Commute (P * R) P from (Commute.refl P).mul_left ((Commute.one_left _).sub_left (Commute.refl P))) (-t)).eq) w)
    unfold hive; simp only [mul_apply_eq_comp]; rw [← adjoint_inner_left (W t), show (W t).adjoint = W (-t) from C.Cabin_cross t,hn,hn,h]; simp [clover,fareGate,sq,mul_apply_eq_comp]; -- tune
 simp_rw [ph]; exact fruition C θ p A x y
end YM.BridgeClub.Moth
