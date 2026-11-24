import YM.SU5.Reconstruction.Trap.Shade
/-!
# Mobius crossing
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K H D:Hilbert}
namespace Clasp
open Multiplier Chirp
variable (C:Clasp K H D)
local notation "I" => spectrum ℂ C.angle
local notation "A"=> C.angle
local notation "Aᵛ"=> (1-C.angle)
local notation "Ω"=> C.motion
local notation "f₀" => C.realF
noncomputable def slope (c x:ℝ) := x+(c*c)*(1-x)
noncomputable def colt (c x:ℝ) := x/slope c x
variable (c:ℝ)
noncomputable def foxtrot:K.Op := A+((c*c:ℝ):ℂ) • Aᵛ
local notation "T" => C.foxtrot c
noncomputable def south:K.Op:= order C.motion (fun x=> (colt c (C.realF x):ℂ))
local notation "F" => C.south c
variable (p:0<c)
lemma slope_reads : Registers C.motion (fun x=>(slope c (C.realF x):ℂ)) (C.foxtrot c):= by
 convert C.angle_reads.add (((Registers.one Ω).sub C.angle_reads).scale ((c*c:ℝ):ℂ)) using 1
 funext y; change (slope c _ :ℂ)= _ + ((_:ℝ):ℂ)*(1- (C.realF y:ℂ)); unfold slope; push_cast; rfl
 rfl
include p
lemma slope_price (x:ℝ)(b:x∈Icc (0:ℝ) 1): 0<slope c x ∧ x≤ slope c x:= by
 unfold slope; have hc:0≤(c*c)*(1-x):= mul_nonneg (by positivity) (sub_nonneg.mpr b.2)
 refine ⟨?_,le_add_of_nonneg_right hc⟩; rcases eq_or_lt_of_le b.1 with v|k; · rw [←v]; simp; positivity
 linarith
lemma colt_tame : Tag (fun x=> colt c (C.realF x)):= by
 refine ⟨by unfold colt slope; fun_prop,1,zero_le_one,?_⟩; intro x
 obtain ⟨y,v⟩:=slope_price c p _ (price C x); let w:=price C x|>.1
 unfold colt; rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg w y.le)]; exact div_le_one_of_le₀ v y.le
lemma south_reads : Registers C.motion (fun x=>(colt c (C.realF x):ℂ)) (C.south c):= by
 apply order_reads; obtain ⟨b,v,r⟩:=(colt_tame C c p).bound; refine ⟨Complex.continuous_ofReal.measurable.comp (colt_tame C c p).meas,b,v,?_⟩
 intro x; rw [Complex.norm_real]; exact r x
lemma south_income: C.south c * C.foxtrot c=A:=by
 apply ((south_reads C c p).times (slope_reads C c)).single
 rw [show ((fun x=> (colt c (C.realF x):ℂ))*(fun x=>(slope c (C.realF x):ℂ)))= (fun x=> (C.realF x:ℂ)) from funext (fun x:I=> ( ?_ : (colt c (C.realF x):ℂ)*(slope c (C.realF x):ℂ)=(C.realF x:ℂ))) ]; exact C.angle_reads
 norm_cast; exact div_mul_cancel₀ _ (slope_price c p (f₀ x) (price C x)|>.1.ne')
omit p
variable {P:H.Op}{Q:D.Op} {U:H.Op}{V:D.Op}{c}
local notation "W"=> C.bring U (V*Mint Q c)
local notation "S"=> peel W
local notation "Z"=> C.bring P Q
local notation "B"=> (Mint (C.bring P Q) c)
local notation "L"=> C.bring P Q
variable (h:ScalePass C P Q U V c)
local notation "Y"=> halfway C h
include h
lemma top_budget : star (halfway C h)* A *halfway C h * (C.bring P Q)=(south C c)*C.bring P Q:=by
 -- use W*W comm Z then inject cancel
 have z:= C.groupProj h.lap h.rap h.dialog
 have he: Commute A Z:= (C.capProj h.lap h.rap h.dialog).1
 let M:=(W).adjoint.comp W; have hm: Commute M Z := by unfold M; rw [← peel_sq W]; exact ((WZ_comm C h).symm.mul_left (WZ_comm C h|>.symm))
 have hu: Commute Aᵛ B:=(Commute.one_left _).sub_left (C.yrate h).symm
 refine dense_cancel M ((polar_dense («A»:=M) ?_ ?_)) (f:=star Y*A*Y*Z ) (g:= (C.south c)*Z) ?_
 · exact IsSelfAdjoint.of_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive M).2 ((W).isPositive_adjoint_comp_self))
 · exact ((W).adjoint_comp_self_injective_iff).mpr (C.routeU h).1
 have hk:M* Z = (C.foxtrot c)* Z:=by
   rw [show M=A+B*Aᵛ*B from (C.W_square h), ←hu.eq, mul_assoc Aᵛ,Mint.fuse c c z]; unfold foxtrot; rw [add_mul,add_mul,mul_assoc Aᵛ, Mint.exact_s z,Algebra.smul_mul_assoc,Algebra.mul_smul_comm] -- may need parentheses
 change _*M=_*M; rw [mul_assoc (star Y*A*Y),←hm.eq,←mul_assoc, C.pointing h, mul_assoc F,←hm.eq,hk, ←mul_assoc,C.south_income c h.pos] -- direction
lemma low_budget: star (halfway C h)* A* halfway C h * (1-Z) = A* (1-Z):= by
 have z:= C.groupProj h.lap h.rap h.dialog
 have hu:= C.yrate h; have hb:B*(1-Z)=1-Z:= by rw [mul_sub,mul_one,Mint.exact_s z]; unfold Mint; abel
 have hm:(W).adjoint.comp W*(1-Z)=1-Z:= by
   rw [C.W_square h, add_mul,mul_assoc (B*Aᵛ), hb, show B*Aᵛ=Aᵛ*B from ((Commute.one_right B).sub_right hu).eq, mul_assoc Aᵛ,hb]; noncomm_ring
   -- sub_right order tune
 nth_rw 1 [←hm]; rw [←mul_assoc,C.pointing h]
lemma interlaced : (Y*Z)*C.south c= C.angle*(Y*Z) := by
 have p: star Y*A*Y*Z=F*Z:= C.top_budget h
 have hY:= C.unit_arc h; have hz:= C.groupProj h.lap h.rap h.dialog
 have hF: IsSelfAdjoint F:=(south_reads C c h.pos).adjoint.single (by convert south_reads C c h.pos using 1; funext x; simp) -- tune
 have hx: Commute (star Y * A *Y) Z:= by
   apply Commute.mul_left _ hY.symm; refine Commute.mul_left ?_ ((C.capProj h.lap h.rap h.dialog).1); exact (Commute.star_right (by rw [hz.2.star_eq]; exact hY)).symm -- tune
 have hut: star (star Y*A*Y)=star Y*A*Y:= (IsSelfAdjoint.of_nonneg (star_left_conjugate_nonneg (C.angle_pos) _))
 have hQ:=congrArg star p; rw [star_mul, star_mul F, hz.2.star_eq,hut,hF,←hx.eq] at hQ
 rw [mul_assoc, ← hQ]; change Y * (star Y*A*Y*Z)=_; simp_rw [mul_assoc]; rw [←mul_assoc Y, (paysHalf C h).2,one_mul]
lemma interlaced' : (Y*(1-Z))*A= A*(Y*(1-Z)) := by
 have he : Z*A=A*Z:= (capProj C h.lap h.rap h.dialog).1.eq.symm
 rw [mul_assoc, sub_mul, one_mul,he, ← (show A*(1-Z) =A-A*Z from by rw [mul_sub,mul_one]),← C.low_budget h]; simp_rw [mul_assoc]; rw [←mul_assoc Y, (paysHalf C h).2,one_mul]
end Clasp
end YM.CrossedFrame
