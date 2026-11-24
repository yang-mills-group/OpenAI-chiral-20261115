import YM.SU5.Reconstruction.Crease.Diagonal
import YM.SU5.Reconstruction.Crease.Harvest
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame OS Semigroup Real Club
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {a b:Axis}(p:b ≠ a)(u:ℝ)
local notation "U"=> move a b
include p
lemma poles (x:E4)(e:Scope a b x): Scope a b (U u x):=by
 have hp:= abs_lt.mp (show |x a| < x b from e); obtain ⟨h,h'⟩:=hp
 have hx: x a+ x b>0:= by linarith
 have hu: x b-x a>0:= sub_pos.mpr h'
 unfold Scope; rw [eye_high p,eye_low p, cosh_eq,sinh_eq,abs_lt];
 constructor<;> nlinarith [exp_pos u,exp_pos (-u)]
lemma dances (x y:E4): U u (x+y)=U u x+U u y:= by
 ext1 i; rcases eq_or_ne i a with h|h; · rw [h]; simp only [PiLp.add_apply,eye_high p]; ring
 rcases eq_or_ne i b with v|v
 · rw [v]; simp only [PiLp.add_apply,eye_low p]; ring
 rw [PiLp.add_apply,others _ _ _ h v,others _ _ _ h v,others _ _ _ h v]; rfl
lemma dance_neg (x:E4): U u (-x)= -U u x:= by
 ext1 i; rw [PiLp.neg_apply]; by_cases h:i=a∨i=b
 · rcases h with e|h
   · rw [e]; simp only [eye_high p,PiLp.neg_apply]; ring
   rw [h]; simp only [eye_low p,PiLp.neg_apply]; ring
 have ht:= not_or.mp h; rw [others _ _ _ ht.1 ht.2,others _ _ _ ht.1 ht.2]; rfl
lemma outdance (x:E4): U u (U (-u) x)=x:=by
 ext1 i; rcases eq_or_ne i a with d|d; · rw [d]; simp only [eye_high p,eye_low p, cosh_neg,sinh_neg]; linear_combination x a * cosh_sq_sub_sinh_sq u
 rcases eq_or_ne i b with h|h; · rw [h]; simp only [eye_high p,eye_low p, cosh_neg,sinh_neg]; linear_combination x b * cosh_sq_sub_sinh_sq u
 rw [others _ _ _ d h,others _ _ _ d h]
variable (a b)
def curtains (z:Bool): Set E4:= if z then Wedge a b else Counter a b
variable {a b}
lemma danceBy (z:Bool)(x:E4)(t:x∈curtains a b z): U u x∈curtains a b z:=by
 cases z; exact (by change Scope a b (-U u x); rw [← dance_neg p]; exact poles p u (-x) t); exact poles p u x t
lemma eitherShift (z:Bool)(x:E4): U u '' ((fun y=> y+x) '' curtains a b z)= (fun y=> y+U u x) '' curtains a b z:= by
 apply Subset.antisymm; · rintro _ ⟨_,⟨y,t,rfl⟩,rfl⟩; exact ⟨U u y,danceBy p u z _ t,(dances p u y x).symm⟩
 rintro _ ⟨y,t,rfl⟩; exact ⟨_,⟨U (-u) y,danceBy p (-u) _ _ t,rfl⟩,by change U u (U (-u) y+x)=_; rw [dances p,outdance p]⟩
variable {H D K:Hilbert}(C:Clasp K H D)
local notation "e"=> Picket.boost C u
noncomputable def ascend (A:H.Op):H.Op:= Picket.boost C u * A* star (Picket.boost C u) -- use order (u)
local notation "ξ"=> ascend u C
omit p
lemma pondLevel (A:H.Op): ascend u C A= Club.pond C (-u/π) A:= by unfold ascend Picket.boost pond; rw [(C.left_credentials _).2.1]
include p
lemma motionFrame (S:OS.Semigroup H a)(k:∀ v:E4,e*trans S v= trans S (U u v)*e)(x:E4) (A:H.Op): ξ (parcelUp S x A)= parcelUp S (U u x) (ξ A):= by
 have ht: trans S (-x)*star e=star e*trans S (-U u x):= by
    have hv:= congrArg star (k x); simp only [star_mul,trans_star S] at hv; exact hv
 unfold ascend parcelUp; calc
  _= (e*trans S x) *A * (trans S (-x)*star e):= by simp only [mul_assoc] -- trans notation
  _ = _:= by rw [k,ht]; simp only [mul_assoc]
end YM.BridgeClub
