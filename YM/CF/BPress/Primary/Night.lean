import YM.CF.BPress.Primary.Noon
/-! primary output actual.* Input primary costs from Keeper. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Brace Spire
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Voice Noon
variable {B m:Side}{A D C X Q P:Pledge}{U:Driver (CSide m B)} {a d k q p r b:ℝ}{G:Duet m B}{I:Pec.Pride (CSide m B)}
-- this record chosen once for every sensible horizon. later issue θSpin.P. T.q lower price.S 
structure Stellar (U:Driver (CSide m B))(P Q:Pledge)(I:Pec.Pride (CSide m B)) where
 arm : Book U P I
 voice : Hymn m B U.d U.p
 -- Q assigned later; keep Q implicit? do keep
variable (J: Stellar U P Q I)(u:Wish U A D C)
namespace Stellar
variable (T:Tenor (More (CSide m B))) (x y:U.Pose)
def myCost := J.arm.bud T + hit J.voice T
abbrev publicF(t:Tenor (More (CSide m B)))(x:U.Pose):= J.arm.ballad u t x-hot_H J.voice t x -- field score
variable (H:Solo J.voice G k Q.rate Q.price)
include H
lemma cost_0: Cash scaffold (J.myCost) (min P.rate Q.rate) (P.price+Q.price) := Cash.plus (J.arm.h.purchases.chill (min_le_left ..)) ((h_budget H).chill (min_le_right ..)) -- tune myCost unification
lemma rows_t (t:Tenor (More (CSide m B)))(p:J.myCost t≠0):Grove (Grid.field 4 (More (CSide m B))) t.2∧ t.1∈ t.2:=by
 by_cases h:J.arm.bud t=0; · rw [myCost,h,zero_add] at p; exact (heat_ta H t p).symm
 exact ⟨(J.arm.h.handles ..).conduct h,J.arm.h.pins h⟩
include u
lemma budget0: ‖J.publicF u T x‖≤ J.myCost T:= (norm_sub_le ..).trans (add_le_add (J.arm.stock_ballad u _ _) (hit_n x H T)) -- wrong hot
lemma knownL : Measurable (J.publicF u T):= (J.arm.stock_m u _).sub (Noon.hot_m H T)
lemma stable_c (p:Along T.2 x.val y.val): J.publicF u T x=J.publicF u T y:=by
 let F:= J.arm.ballad u T; apply congrArg₂ (·-·) _ (hot_read x H T p); apply sub_eq_zero.mp; apply norm_eq_zero.mp; refine le_antisymm ((J.arm.stock_k u _ x y).trans ?_) (norm_nonneg _); rw [show U.Beta.eval T.2 x y=0 from p.price0,mul_zero] -- tune
lemma gauge_m (g:Mach (More (CSide m B))): J.publicF u T (moveW x u g)= J.publicF u T x:= congrArg₂ (·-·) (J.arm.stock_g u T x g) (hot_hold x H T g u)
lemma cost0 (Y:Shell.plot q U.p U.d r k)(t:Slow 1 (hook y.val.X) q)(Δ: y.val.G=1)(P:Shell T.2 y.val.X x.val.G x.val.X b)(g:0<b)(e:b≤r)(s:U.Beta.eval T.2 x y ≤ a)(K:b ≤ a): ‖J.publicF u T x-J.publicF u T y‖≤ J.myCost T*a:=by
 unfold publicF myCost; rw [sub_sub_sub_comm,add_mul]; exact (norm_sub_le ..).trans (add_le_add ((J.arm.stock_k u T x y).trans (mul_le_mul_of_nonneg_left s (J.arm.h.purchases.pos T))) ((hot_variation x H T Y y Δ t P g e).trans (mul_le_mul_of_nonneg_left K ((h_budget H).pos T)))) -- tune order hot_variation.check
lemma burst (X:Pledge)(g:Grant X A (payA A D C) (stream 1) (Sight.price U.h) U.v U.ε quota): ∑ p,J.publicF u p x= stark x-Pec.pigment I x.val.G - Spire.zen (Spire.hum m B G x.val.G x.val.X):= by unfold publicF; rw [sum_sub_distrib, J.arm.story_sum u x g, hot_total x H] -- tune
lemma billzR (i:Site (More (CSide m B))): ∑ p:Support (More _),(J.publicF u (i,p) x).re=(town I x i).re:=by simp_rw [publicF,Complex.sub_re, hot_imag (x:=x),sub_zero]; exact J.arm.story_real u _ _ -- tune holds? binder order
end Stellar
end YM.CF.BPress.Primary
