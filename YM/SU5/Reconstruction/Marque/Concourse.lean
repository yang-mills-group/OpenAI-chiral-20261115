import YM.SU5.Reconstruction.Marque.Charts
import YM.SU5.Reconstruction.Crease.Thicket
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Matrix Real Complex
open scoped Matrix MatrixGroups Topology InnerProductSpace Classical
variable (g h:Two) (x y:E4)
local notation "ρ"=>Motion
macro "sway" : tactic=> `(tactic| (simp [-ofReal_cosh,-ofReal_sinh,-ofReal_exp, Motion,remit,out,herm,Matrix.mul_apply, Matrix.conjTranspose_apply,pin,val,Complex.mul_re, Complex.mul_im, Fin.sum_univ_two]))
lemma basinMotion (x:E4): BridgeClub.turn clock 2 x= -ρ Basin x := by
 unfold Basin Pole; ext1 i; fin_cases i <;> rw [BridgeClub.turn_at] <;> sway <;> norm_num [clock,show (0:Axis)≠3 from by decide,show (1:Axis)≠3 from by decide] -- tune
lemma basis_motion (u:ℂˣ) : ∀ (x:E4), x∈BridgeClub.Wedge clock 2 ↔ Motion (Pole u) x∈ BridgeClub.Wedge clock 2:= by
 -- diagonals via complex
 intro x
 let p:= Motion (Pole u) x; change |x 3|<x 2↔ |p 3|<p 2
 let a:ℂ:= (u:ℂ); let b:= ((u:ℂ)⁻¹)
 have hz: 0<Complex.normSq a:= Complex.normSq_pos.mpr (Units.ne_zero u)
 have hv: 0<Complex.normSq b:= Complex.normSq_pos.mpr (inv_ne_zero (Units.ne_zero u))
 have h0:p 3+p 2=normSq a*(x 3+x 2):= by
     have hk:=congrFun (congrFun (atMotion (Pole u) x) 0) 0; change herm p 0 0=_ at hk
     suffices h0:(↑(p 3+p 2):ℂ)= ↑(normSq a*(x 3+x 2)) by exact_mod_cast h0
     push_cast; rw [← Complex.mul_conj a]; convert hk using 1 <;> simp [remit,Pole,Matrix.mul_apply,Fin.sum_univ_two,pin,val,herm,a] <;> ring
 have h1:p 3-p 2=normSq b*(x 3-x 2):= by
     have hk:=congrFun (congrFun (atMotion (Pole u) x) 1) 1; change herm p 1 1=_ at hk
     suffices h0:(↑(p 3-p 2):ℂ)= ↑(normSq b*(x 3-x 2)) by exact_mod_cast h0
     push_cast; rw [← Complex.mul_conj b]; convert hk using 1 <;> simp [remit,Pole,Matrix.mul_apply,Fin.sum_univ_two,pin,val,herm,b] <;> ring
 rw [show (|p 3|<p 2) ↔ 0 < p 3+p 2 ∧ p 3-p 2 < 0 from (by rw[abs_lt];constructor <;> rintro ⟨h,g⟩<;>constructor<;> linarith),h0,h1,mul_pos_iff_of_pos_left hz, show normSq b*(x 3-x 2)<0↔ x 3-x 2<0 from (by nth_rw 1 [← mul_zero (normSq b)]; rw [mul_lt_mul_iff_right₀ hv]),abs_lt]; constructor <;> rintro ⟨h,g⟩<;>constructor<;> linarith
lemma turnMotion : x∈BridgeClub.Wedge clock 2 ↔ Motion turn x∈ BridgeClub.Counter clock 2:= by
 unfold turn; change _ ↔ |(-Motion _ x) 3|<(-Motion _ x) 2; have hv: -(x 3)= -x 3:=rfl -- dummy
 simp only [BridgeClub.Wedge,BridgeClub.Scope,Set.mem_setOf_eq]; sway; simp [clock]; ring_nf
-- boost spin
variable (t:ℝ) (u v:SpaceAxis)
lemma motionX :Motion (Zip t)=Picket.move clock 0 (2*t):=by
 funext x; have he:= Real.cosh_sq_sub_sinh_sq t
 have ht:(↑(rich t):ℂ)⁻¹=(Real.exp (-t):ℝ):=by rw [Real.exp_neg,ofReal_inv]; rfl
 have hv:Real.exp t≠0:=(Real.exp_pos t).ne'
 apply PiLp.ext; intro i; fin_cases i
 · change (Motion _ x) 0=Picket.move clock 0 (2*t) x 0; rw [Picket.eye_low (b:=0) (show (0:Axis)≠clock from by decide)]; unfold Zip Tope; sway; unfold clock; rw [show 2*t=t+t by ring, Real.cosh_add,Real.sinh_add]; ring
 · change (Motion _ x) 1=Picket.move clock 0 (2*t) x 1; rw [Picket.others _ _ _ (by decide) (by decide)]; unfold Zip Tope; sway <;> linear_combination (x 1)*he
 · change (Motion _ x) 2=Picket.move clock 0 (2*t) x 2; rw [Picket.others _ _ _ (by decide) (by decide)]; unfold Zip Tope; sway <;> linear_combination (x 2)*he
 · change (Motion _ x) 3=Picket.move clock 0 (2*t) x clock; rw [Picket.eye_high (b:=0) (show (0:Axis)≠clock from by decide)]; unfold Zip Tope; sway; unfold clock; rw [show 2*t=t+t by ring, Real.cosh_add,Real.sinh_add]; ring
lemma motionY :Motion (Yell t)=Picket.move clock 1 (2*t):=by
 funext x; have he:= Real.cosh_sq_sub_sinh_sq t
 have ht:(↑(rich t):ℂ)⁻¹=(Real.exp (-t):ℝ):=by rw [Real.exp_neg,ofReal_inv]; rfl
 have hv:Real.exp t≠0:=(Real.exp_pos t).ne'
 apply PiLp.ext; intro i; fin_cases i
 · change (Motion _ x) 0=Picket.move clock 1 (2*t) x 0; rw [Picket.others _ _ _ (by decide) (by decide)]; unfold Yell Tope; sway <;> linear_combination (x 0)*he
 · change (Motion _ x) 1=Picket.move clock 1 (2*t) x 1; rw [Picket.eye_low (b:=1) (show (1:Axis)≠clock from by decide)]; unfold Yell Tope; sway; unfold clock; rw [show 2*t=t+t by ring, Real.cosh_add,Real.sinh_add]; ring
 · change (Motion _ x) 2=Picket.move clock 1 (2*t) x 2; rw [Picket.others _ _ _ (by decide) (by decide)]; unfold Yell Tope; sway <;> linear_combination (x 2)*he
 · change (Motion _ x) 3=Picket.move clock 1 (2*t) x clock; rw [Picket.eye_high (b:=1) (show (1:Axis)≠clock from by decide)]; unfold Yell Tope; sway; unfold clock; rw [show 2*t=t+t by ring, Real.cosh_add,Real.sinh_add]; ring
lemma motionZ :Motion (Tuning t)=Picket.move clock 2 (2*t):=by
 funext x; have he:= Real.cosh_sq_sub_sinh_sq t
 have ht:(↑(rich t):ℂ)⁻¹=(Real.exp (-t):ℝ):=by rw [Real.exp_neg,ofReal_inv]; rfl
 have hv:Real.exp t≠0:=(Real.exp_pos t).ne'
 apply PiLp.ext; intro i; fin_cases i
 · change (Motion _ x) 0=Picket.move clock 2 (2*t) x 0; rw [Picket.others _ _ _ (by decide) (by decide)]; unfold Tuning Pole; sway <;> field_simp <;> ring
 · change (Motion _ x) 1=Picket.move clock 2 (2*t) x 1; rw [Picket.others _ _ _ (by decide) (by decide)]; unfold Tuning Pole; sway <;> field_simp <;> ring
 · change (Motion _ x) 2=Picket.move clock 2 (2*t) x 2; rw [Picket.eye_low (b:=2) (show (2:Axis)≠clock from by decide)]; unfold Tuning Pole; sway; rw [Real.cosh_eq,Real.sinh_eq]; simp only [show 2*t=t+t by ring,Real.exp_add, neg_add_rev,Real.exp_neg]; simp [clock, -ofReal_exp]; field_simp; ring
 · change (Motion _ x) 3=Picket.move clock 2 (2*t) x clock; rw [Picket.eye_high (b:=2) (show (2:Axis)≠clock from by decide)]; unfold Tuning Pole; sway; rw [Real.cosh_eq,Real.sinh_eq]; simp only [show 2*t=t+t by ring,Real.exp_add, neg_add_rev,Real.exp_neg]; simp [clock, -ofReal_exp]; field_simp; ring
end YM.Marque.Flow
