import YM.CF.BProof.Trek.Agenda
/-! Fixed budgets after D, independent of R_F, L_c, orientation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c f:Side}{u v:ℝ}
-- Ramp
namespace Rise
-- choose smooth piece f= ease over required thresholds. Preserves comparison at end. Lipschitz extension can take clamped argument.
def clt (x:ℝ):= max 0 (min 1 x)
lemma clt_z (x:ℝ): clt x∈ Zone:=⟨le_max_left ..,max_le zero_le_one (min_le_left ..)⟩
lemma ease_clt(x:ℝ): ease (clt x)=ease x:=by
 unfold clt; by_cases h:x<0
 · rw [min_eq_right (by linarith), max_eq_left h.le,ease_zero,ease_low x (by linarith)]
 by_cases u:1≤ x
 · rw [min_eq_left u,max_eq_right zero_le_one,ease_one,ease_up x (by linarith)]
 rw [min_eq_right (by linarith),max_eq_right (by linarith)]
lemma clt_le(x y:ℝ): |clt x-clt y|≤|x-y|:=by unfold clt; grind

def easeD(u j x:ℕ):ℝ:= ease ((x-(u:ℝ))/j)
lemma easeD_zone(u j x:ℕ): easeD u j x∈Zone:= easeZ _
lemma enter(u j:ℕ)(x:ℕ)(h:x≤u)(p:0<j): easeD u j x=0:=by apply ease_low; rw [div_le_iff₀ (Nat.cast_pos.mpr p)]; linarith only [show (x:ℝ)≤u from Nat.cast_le.mpr h, show 0<(j:ℝ) from Nat.cast_pos.mpr p] -- tune
lemma exit(u j:ℕ)(x:ℕ)(h:u+j≤x)(p:0<j): easeD u j x=1:=by apply ease_up; rw [le_div_iff₀ (Nat.cast_pos.mpr p)]; linarith only [show (u:ℝ)+j≤x by exact_mod_cast h, show 0<(j:ℝ) from Nat.cast_pos.mpr p]
lemma easeD_bill (u j x y:ℕ)(p:0<j) (a: x ≤ y+1)(b:y≤x+1): |easeD u j x-easeD u j y| ≤ rateH/(j:ℝ):=by
 let f (x:ℕ):ℝ:=((x:ℝ)-↑u)/(j:ℝ); have hr:0<(j:ℝ):=Nat.cast_pos.mpr p; change |ease (f x)-ease (f y)| ≤ _; rw [←ease_clt, ← ease_clt (x:=f y)]; apply le_trans (expenses.easeW _ (clt_z _) _ (clt_z _)); rw [Real.dist_eq]; apply le_trans (mul_le_mul_of_nonneg_left (clt_le ..) rate_p.le); rw [show rateH/(j:ℝ)=rateH*(1/(j:ℝ)) from by ring]; apply mul_le_mul_of_nonneg_left _ rate_p.le; unfold f; rw [← sub_div,sub_sub_sub_cancel_right,abs_div,abs_of_pos hr]; apply div_le_div_of_nonneg_right _ hr.le; rw [abs_le]; constructor <;> linarith [show (x:ℝ)≤(y:ℝ)+1 by exact_mod_cast a,show (y:ℝ)≤(x:ℝ)+1 by exact_mod_cast b]
end Rise

structure Sized (t:ℕ) (r:Side) where
 stepQ:ℕ
 up : 0<stepQ
 blockY:ℕ
 beginU : t+stepQ<blockY
 taperW:ℕ
 taperP : 0<taperW
 nearM:ℕ
 near : blockY+(2*r.val+1+taperW)≤nearM
namespace Sized
variable {t:ℕ}{r:Side}(C:Sized t r)
abbrev extent := t+C.stepQ
abbrev activate := 2*r.val+1
-- activate does not depend C? bind? always use Shift
abbrev extentT := 2*r.val+1+C.taperW
end Sized
variable (Y:Yard s)
variable {t:ℕ}(H:Herald u v)(C:Sized t H.whole)
-- shape includes radius on Wheel. small gap already independent. levels verifying
structure Sound (C:Sized t H.whole)(d:ℝ): Prop where
 fields : 0<d
 LH : 6*xm*d+rateH/Y.short ≤ v
 LB : 6*xm*d+rateH*(rateH/C.stepQ) ≤ v
 SX : 3*xm*d+rateH/Y.short ≤ H.good
 tap : rateH*2*(rateH/C.taperW)≤ v
-- 'd' measures chord U/ frame. supply after geometry y choice; exists C and such d given admissible aperture.
structure Pad (Y:Yard s)(H:Herald u v)(C:Sized t H.whole)(k:ℕ):Prop where
 long : 20*C.nearM+20 ≤ Y.long
 high : k ≥ C.nearM+10
namespace Pad
variable {Y H C}{k:ℕ}(P:Pad Y H C k)
include P
lemma nearP : t + C.stepQ < C.nearM:= C.beginU.trans_le ((by have ht:=C.near; exact le_trans (by omega : C.blockY≤ C.blockY+(2*H.whole.val+1+C.taperW)) ht))
lemma slim : 2*C.nearM+1<Y.long:=by have :=P.long; omega
lemma suff {x:ℕ}(h:x≤ C.blockY) : 2*x+1<Y.long:=by have hp:=P.slim; have he:=C.near; omega
lemma stip : 2*C.extent+3 < Y.long:=by have :=P.slim; have he:= P.nearP; unfold Sized.extent; omega
lemma reach_l : t≤ C.nearM := Nat.le_trans (by omega : t≤t+C.stepQ) P.nearP.le
end Pad
end YM.CF.BProof.Trek
