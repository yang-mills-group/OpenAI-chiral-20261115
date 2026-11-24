import YM.SU5.Reconstruction.Crease.Pollen
import YM.SU5.Reconstruction.Crease.Foothold
import YM.SU5.Reconstruction.Trap.Dusk
/-! # Quartz. Facts on the log calculus of our authenticated Boost -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Clasp
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace
open Multiplier
variable {K H D:Hilbert}(C:Clasp K H D)
/-- Reverse the Wakeman clock pair: this will be needed in the new bilateral budget. -/
noncomputable def Back : Clasp K D H:=⟨C.r,C.l,C.k,C.j,C.q,C.p,(add_comm ..|>.trans C.frame)⟩
local notation "B"=> C.Back
@[simp] lemma Back_again : C.Back.Back=C:=rfl
@[simp] lemma Back_l: C.Back.l=C.r:=rfl
@[simp] lemma Back_r: C.Back.r=C.l:=rfl
@[simp] lemma Back_Left: C.Back.Left=C.Right:=rfl
@[simp] lemma Back_Right: C.Back.Right=C.Left:=rfl
@[simp] lemma Back_look: C.Back.look=C.look.symm:=rfl
lemma Back_angle: C.Back.angle=1-C.angle:= C.complement
lemma roof_compl : Registers C.motion (fun x => (↑(1-C.realF x) : ℂ)) (1-C.angle):= by
 convert (Registers.one C.motion).sub C.angle_reads using 1
 ext1 x; push_cast; rfl -- tune
local notation "A"=> C.angle
local notation "P"=> C.motion
local notation "f"=> C.realF
local notation "I"=> spectrum ℂ C.angle
noncomputable def crystal (x:spectrum ℂ C.angle):ℝ:=Real.log ((1-C.realF x)/C.realF x)
local notation "κ"=> C.crystal
@[fun_prop] lemma crystal_m : Measurable C.crystal:= by unfold crystal; fun_prop
lemma crystalline (u:ℝ): C.Cabin u= concern C.motion C.crystal u:=by
 unfold concern Cabin crystal river Chirp.sing sound; congr 1; ext1 x; unfold comp; ring_nf
lemma Back_log (x:I)(_h:f x∈ Ioo (0:ℝ) 1)(u:ℝ): river u (1-C.realF x)= river (-u) (C.realF x):=by
 let b:= f x; unfold river Chirp.sing
 have k: (1-(1-b))/(1-b)= ((1-b)/b)⁻¹ := by rw [inv_div]; congr 1; ring
 simp only [← show b=f x from rfl,k,Real.log_inv]; congr 1; push_cast; ring
lemma Back_Cabin (u:ℝ): C.Back.Cabin u=C.Cabin (-u):=by
 let g(x:I):=1-f x; let V:=(C.Back).motion
 have hg:Measurable g:= measurable_const.sub C.measurable_realF; have he:Tag g:=⟨hg,1,zero_le_one,fun x=>by rw[Real.norm_eq_abs,abs_le]; unfold g; constructor<;> linarith [(price C x).1,(price C x).2]⟩
 have p:= compare_at P V (1:K.Op) g ((C.Back).realF) hg (C.Back).measurable_realF he (C.Back).tagF C.roof_compl (C.Back).angle_reads (show (1:K.Op)*(1-A)= ((C.Back).angle)*1 by simp only [Back_angle,one_mul,mul_one]) (river u) (river_price u)
 change order _ _= C.Cabin _; rw [show order V (river u ∘ ((C.Back).realF))= order P (river u ∘ g) from (by change (1:K.Op)*_= _*1 at p; simpa only [one_mul,mul_one] using p.symm)] -- tune pattern
 apply (order_reads P ((river_price u).port g hg)).single
 refine (Cabin_reads C _).agrees ((river_price u).port g hg) (fun x => (C.inOpen x).mono (fun z q=>?_))
 exact (Back_log C z q u).symm
noncomputable def clarity (t:ℝ):ℂ:= (↑((1+Real.exp t)⁻¹:ℝ):ℂ)
lemma clarity_at (x:I)(h:f x∈ Ioo (0:ℝ) 1): clarity (κ x)= f x:=by
 obtain ⟨p,v⟩:= h; unfold clarity crystal; rw [Real.exp_log (div_pos (sub_pos.mpr v) p)]; congr 1; field_simp; ring
lemma clarity_pays: Tag clarity:= by
 refine ⟨by unfold clarity; fun_prop,1,zero_le_one,?_⟩; intro p; unfold clarity; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by linarith [Real.exp_pos p]) -- maybe
lemma reins (T:K.Op)(h:∀ u:ℝ,Commute T (C.Cabin u)):Commute T C.angle:=by
 have p:= ballot P P T κ κ C.crystal_m C.crystal_m (fun u=> by rw [←crystalline]; exact (h u).eq) clarity clarity_pays
 have j: A= order P (clarity ∘ κ):=takes_order P (C.angle_reads.agrees ((clarity_pays).port κ C.crystal_m) (fun x => (C.inOpen x).mono (fun t h=> ((C.clarity_at t h).symm)))) -- tune
 rw [commute_iff_eq,j]; exact p
lemma border_price : C.Right.conjStarAlgEquiv (1-C.angle) = C.Back.plume:= by rw[C.Back.portAngle,Back_angle,Back_Left]
lemma carryLook(u:ℝ): C.look.conjStarAlgEquiv (C.cLeft u)=C.Back.cLeft (-u):=by
 unfold cLeft; rw [Back_Left,Back_Cabin,neg_neg]; ext1 x; obtain ⟨x,rfl⟩:= C.Right.surjective x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,look]
lemma carryBoost(u:ℝ): C.look.conjStarAlgEquiv (Picket.boost C u)= Picket.boost C.Back (-u):= by
 unfold Picket.boost; rw[carryLook,neg_neg,neg_div,neg_neg] -- tune
/- rocket uses complemented P in the same H' for opposite rank in b -/
end YM.CrossedFrame.Clasp
