import YM.SU5.Regis.Curators
/-! # Parking Etches. Gluing & placing their sites. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule
open Gleam Matrix Next.SectorChange Next.SectorChange.Gaussian
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {n:Side}{G:Gauge}{I J L:Type*}
namespace Etch
abbrev toWalk (o:Cover):Walk:= route 0 o 1
abbrev entrust (o:Cover)(x:Slot) : Slot := {x with walk:= (toWalk o) ++ x.walk}
private lemma stop_c (w: Walk)(x y:Cover): stop (x+y) w=x + stop y w:=by induction w generalizing y with| nil=> rfl| cons i l ih=> rw [stop,stop,add_assoc,ih]
lemma consume (x:Slot)(o:Cover): (entrust o x).offset=o+x.offset:=by
 change stop _ (_++_)= _; rw [stop_append, toWalk, route_end]; nth_rw 1 [← add_zero o]; exact stop_c ..
lemma toPoint (x:Slot)(o:Cover)(b:Site n):slotFace (entrust o x) b= slotFace x (wrap n o+b):=by unfold slotFace; rw [consume,map_add,add_comm _ (wrap n x.offset), add_assoc]
lemma consume_at (o:Cover)(U:Config G n)(x:Slot) : (entrust o x).atSite U 0 = G.adjoint (travel U 0 (toWalk o)) (x.atSite U (wrap n o)):=by
 rw [atSite_path,atSite_path,show (entrust o x).walk= _ ++ _ from rfl, travel_append, toPoint,add_zero,show stop (0:Site n) (toWalk o)=wrap n o from (by rw [← map_zero (wrap n),←wrap_stop_cover, toWalk,route_end]),G.adjoint_mul]
variable [Fintype I][Fintype J][Fintype L](A: Etch G I)(B:Etch G J)
abbrev here (ρ:ℝ)(x:Config G n):=A.palette ρ 1 0 x
lemma here_eq (ρ:ℝ)(x:Config G n): A.here ρ x=A.f (fun i=>ρ • (A.slot i).atSite x 0):=by unfold here palette; rw [pull_id]; rfl
lemma pose_curve(L:I→Slot)(s:Signed)(u v:I→G.Color): ‖(fun i=>skewSig G (L i) s • u i)-(fun i=>skewSig G (L i) s • v i)‖≤ ‖u-v‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> (show ‖skewSig G _ _ • u i - skewSig G _ _ • v i‖≤_ from (by rw [← smul_sub,norm_smul,Real.norm_eq_abs, skewSq, one_mul]; exact norm_le_pi_norm (u-v) i))
def pose (s:Signed)(x:Cover):Etch G I where
 slot i:= entrust x (skewSlot G (A.slot i) s)
 f y:= A.f (fun i=> skewSig G (A.slot i) s • y i)
 diff:= A.diff.comp (contDiff_pi.mpr (fun i=> by fun_prop))
 arc:= A.arc
 bound y:= A.bound _
 favor:= A.favor
 steady:= LipschitzWith.of_dist_le_mul fun u v=> by
    refine (A.steady.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity)); rw [dist_eq_norm,dist_eq_norm]; apply pose_curve
 move x y:=by
    rw [← A.move x (fun i=> skewSig G (A.slot i) s • y i)]; simp
lemma posed_p (s:Signed)(x:Cover)(ρ:ℝ)(U:Config G n): (A.pose s x).here ρ U=A.palette ρ s (wrap n x) U:=by
 let i:= travel U 0 (toWalk x); let p(j:I):=skewSlot G (A.slot j) s
 rw [here_eq,A.pin]; let f(j):=(p j).atSite U (wrap n x); let g(j:I):= skewSig G (A.slot j) s
 change A.f (fun j=> g j • ρ • (entrust x (p j)).atSite U 0) = A.f (fun j=>ρ • g j • f j)
 rw [←A.move i (fun j=>ρ • g j • f j)]; apply congrArg A.f; funext i; rw [consume_at,map_smul,map_smul]; exact smul_comm ..
lemma posed_s(s:Signed)(x:Cover)(ρ:ℝ)(q:Clip)(y:Altar G n): (A.pose s x).sketch q ρ 0 y=A.chalk q ρ s (wrap n x) y:=by
 unfold sketch chalk; apply congrArg A.f; funext i; change skewSig G _ _ • ρ • river q (slotFace (entrust x _) _) y=_; rw [toPoint,add_zero, smul_comm]

private lemma distN (a:J→ L)(u v:L→ G.Color):dist (fun j=>u (a j)) (fun j=>v (a j))≤ dist u v:=by
 rw [dist_eq_norm, dist_eq_norm]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> norm_le_pi_norm (u-v) (a j)
-- combine heterogeneous. scale included in buffet.
def radial (A:Etch G I) (B:Etch G J) : Etch G (I⊕J) where
 slot:= Sum.elim A.slot B.slot
 f x:= A.f (fun i=> x (.inl i)) * B.f (fun i=> x (.inr i))
 arc:= A.arc * B.arc
 bound x:= by rw [abs_mul]; exact mul_le_mul (A.bound _) (B.bound _) (abs_nonneg _) A.arc_non
 diff:=(A.diff.comp (f:=fun x: I⊕J→ G.Color=>fun i=> x (.inl i)) (contDiff_pi.mpr (fun i=> by fun_prop)) |>.mul (B.diff.comp (f:=fun x: I⊕J→ G.Color=>fun i=> x (.inr i)) (contDiff_pi.mpr (fun i=> by fun_prop)))) -- named comp args? left f not g
 favor:= A.favor*⟨B.arc,B.arc_non⟩+ B.favor*⟨A.arc,A.arc_non⟩
 steady:= LipschitzWith.of_dist_le_mul fun x y=> by
    let u:= fun x:I⊕J→G.Color=> A.f (fun i=> x (.inl i)); let v:=fun x:I⊕J→G.Color=> B.f (fun i=> x (.inr i)); let d:=dist x y
    have he:dist (u x) (u y)≤ (A.favor:ℝ)*d:=(A.steady.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (distN Sum.inl x y) (by positivity))
    have ht:dist (v x) (v y)≤ (B.favor:ℝ)*d:=(B.steady.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (distN Sum.inr x y) (by positivity))
    change dist (u x*v x) (u y*v y) ≤ _; apply (dist_triangle _ (u y*v x) _).trans; rw [Real.dist_eq,Real.dist_eq,← sub_mul,← mul_sub, abs_mul,abs_mul,← Real.dist_eq,← Real.dist_eq]; push_cast
    refine (add_le_add (mul_le_mul he (B.bound _) (abs_nonneg _) (mul_nonneg (by positivity) (dist_nonneg))) (mul_le_mul (A.bound _) ht (dist_nonneg) A.arc_non)).trans_eq ?_; change _ = ((A.favor:ℝ)*B.arc+(B.favor:ℝ)*A.arc)*d; ring -- dist
 move x y:=by rw [A.move x (fun i=>y (.inl i)),B.move x (fun i=>y (.inr i))]

lemma radial_h(ρ:ℝ)(U:Config G n): (A.radial B).here ρ U=A.here ρ U*B.here ρ U:=rfl
lemma radial_s (ρ:ℝ)(q:Clip)(x:Altar G n): (A.radial B).sketch q ρ 0 x=A.sketch q ρ 0 x* B.sketch q ρ 0 x:=rfl
-- linear sums of same shape, arbitrary real coeff.
variable (V:J→ Etch G I)(t:J→ℝ)
def salix : Etch G (J×I) where
 slot i:= (V i.1).slot i.2
 f x:= ∑ i:J, t i*(V i).f (fun j=>x (i,j))
 arc:= ∑ i, |t i| * (V i).arc
 bound x:= (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=> by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((V i).bound _) (abs_nonneg _)))
 diff:= ContDiff.sum (fun i _=> by
    let x: (J×I→G.Color)→ (I→G.Color):= fun X j => X (i,j); have hp:ContDiff ℝ 1 x:= contDiff_pi.mpr (fun i=> by unfold x; fun_prop)
    change ContDiff ℝ 1 (fun y=> _* (V i).f (x y)); exact contDiff_const.mul ((V i).diff.comp hp))
 favor:= ∑ i, ‖t i‖₊*(V i).favor
 steady:= LipschitzWith.of_dist_le_mul fun x y=> by
    rw [Real.dist_eq,← sum_sub_distrib]; simp only [← mul_sub,NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm,Real.norm_eq_abs, sum_mul] -- coe
    refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=>?_)); rw [abs_mul,← Real.dist_eq,mul_assoc]; exact mul_le_mul_of_nonneg_left (((V i).steady.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (distN (fun j=>(i,j)) x y) (by positivity))) (abs_nonneg _)
 move x y:=sum_congr rfl (fun i _=> congrArg (t i* ·) ((V i).move x _))
lemma salix_h (ρ:ℝ)(U:Config G n): (salix V t).here ρ U=∑ i:J,t i*(V i).here ρ U:=rfl
lemma salix_s (ρ:ℝ)(q:Clip)(x:Altar G n): (salix V t).sketch q ρ 0 x=∑ i:J, t i*(V i).sketch q ρ 0 x:=rfl
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.Etch.posed_s
#print axioms YM.Regis.Head.Etch.salix_h
#print axioms YM.Regis.Head.Etch.radial_s
