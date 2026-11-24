import YM.SU5.Reconstruction.Trap.High
/-!
# actual modular equation

No Wick of candidate FIELD contents yet; but polar buys this in our reconstruction H.
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
variable {P:H.Op}{Q:D.Op} {U:H.Op}{V:D.Op}{c:ℝ} (h:ScalePass C P Q U V c)
variable (u:ℝ)
local notation "W"=> C.bring U (V*Mint Q c)
local notation "Z"=> C.bring P Q
local notation "F"=> C.Cabin u
local notation "E"=> sing u (c*c)
local notation "L" => C.Left.toContinuousLinearEquiv.toContinuousLinearMap
local notation "Y"=> halfway C h
-- commutes light-zero controls projections individually, derive spin relation for ALL U's passing that way.
include h
lemma fact (x:I)(p:f₀ x∈ Ioo (0:ℝ) 1): river u (colt c (C.realF x)) = sing u (c*c) * river u (C.realF x) := by
 let t:= f₀ x; have ht:0<t:=p.1
 unfold river; rw [show ((1:ℝ)-colt c t)/colt c t=(c*c)*((1-t)/t) from ?_, voices u (c*c) ((1-t)/t) (mul_pos h.pos h.pos) (div_pos (sub_pos.mpr p.2) ht)] -- tune occurrence t
 unfold colt; have p1:=slope_price c h.pos (f₀ x) (price C x)|>.1; change 0<slope c t at p1; field_simp; unfold slope; ring_nf -- field_simp needs t & p1 unfolding
lemma decade : Commute (C.Cabin u) (C.bring P Q):=(C.oneCabin ((capProj C h.lap h.rap h.dialog).1).symm u).symm
lemma weather : Cabin C u * (halfway C h*Z)= (halfway C h*Z)* (sing u (c*c) • Cabin C u) := by
 have p:=colt_tame C c h.pos
 have he: order Ω (river u ∘ (fun x=> colt c (f₀ x))) = sing u (c*c) • Cabin C u:= by
   let q:= (river_price u).port (fun x=> colt c (f₀ x)) p.meas
   refine Registers.single (order_reads _ q) (((C.Cabin_reads u).scale _).agrees q (fun x=>?_)); apply (C.inOpen x).mono; intro x hx; exact (C.fact h u x hx).symm
 let b:= Y*Z; have hz:= compare_at Ω Ω b _ _ p.meas C.measurable_realF p C.tagF (south_reads C c h.pos) C.angle_reads (C.interlaced h) _ (river_price u)
 rw [he] at hz; exact hz.symm
lemma beforeZ : Commute (halfway C h*(1-Z)) F := C.oneCabin (interlaced' C h) u -- arg implicit T
lemma lamp : Y*(1-Z)+E • (Y*Z)= F*Y*star F := by
 have p:= weather C h u; rw [Algebra.mul_smul_comm] at p
 have hp:= C.beforeZ h u; change _*_ = _*_ at hp; let k:= Y*Z; let o:= Y*(1-Z);
 have he: o+k=Y:= by unfold o k; rw [←mul_add]; simp
 have t (a:K.Op): a*F*star F=a:= by rw [mul_assoc,(C.Cabin_pays u).2,mul_one] -- syntax F op
 calc
   _ = o*F*star F+(E • k)*F*star F := by rw [t,t]
   _ = F*Y*star F:= by nth_rw 1 [← he]; rw [mul_add, add_mul]; unfold o k; rw [hp, p, Algebra.smul_mul_assoc E _ F] -- tune
-- Action in j & k, and V (independent of φ). Use for all directions.
noncomputable def cLeft (u:ℝ) : H.Op := C.Left.conjStarAlgEquiv (C.Cabin u)
noncomputable def cRight (u:ℝ) : D.Op := C.Right.conjStarAlgEquiv (C.Cabin u)
-- time continuity
omit h in
lemma scheduleLeft (x:H): Continuous (fun t=> C.cLeft t x) := by
 unfold cLeft; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; exact C.Left.continuous.comp (C.cabin_strong _)
omit h in
lemma groupLeft (k:ℝ): cLeft C u * cLeft C k=C.cLeft (u+k):= by unfold cLeft;rw [←map_mul,Cabin_time]
omit h in
lemma left_credentials : cLeft C 0=1 ∧ star (C.cLeft u)=C.cLeft (-u) ∧ Pays (C.cLeft u):= by
 unfold cLeft; rw [Cabin_zero,map_one,← map_star, C.Cabin_cross]; simp only [true_and]
 unfold Pays; rw [← map_star]; exact ⟨by rw [←map_mul,(C.Cabin_pays u).1,map_one],by rw [← map_mul,(C.Cabin_pays u).2,map_one]⟩
omit h in
private lemma transports {M:H.Op}{B:K.Op}(v:M.comp L=(L).comp B):C.Left.conjStarAlgEquiv B=M := by
 ext1 x; obtain ⟨x,rfl⟩:=C.Left.surjective x; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact DFunLike.congr_fun v.symm x
lemma tag_left : C.Left.conjStarAlgEquiv (C.bring P Q)= P:= C.transports ((capProj C h.lap h.rap h.dialog).2.1).symm
lemma ship_left : C.Left.conjStarAlgEquiv Y=U:= C.transports (halftime C h).1.symm
lemma passage : cLeft C u *U * star (cLeft C u)= U*(1-P)+ sing u (c*c) • (U*P) := by
 have t:= congrArg C.Left.conjStarAlgEquiv (lamp C h u); unfold cLeft; simp only [map_star,map_smul,map_mul,map_add,map_sub,map_one,C.tag_left h,C.ship_left h] at t; exact t.symm
lemma hourComm: Commute (cLeft C u) P := C.tag_left h ▸ ((decade C h u).map (LinearIsometryEquiv.conjStarAlgEquiv C.Left).toStarAlgHom)
end Clasp
end YM.CrossedFrame
