import GaugeFieldConstruction.CrateRT
import GaugeFieldConstruction.StyriaRel.YM.Fields.System
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# Retarded Ward identity for derivative fields.
 Derives from stress of THE registered Spin actions on test point excitations; inherit
 hatch expenditures through differentiation. Do not assume vanishing of the contact
 introduced at positive gap by the hatch cost. It VANISHES in the sum by a hatch replacement on
 test functions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
namespace StressLaw
local notation "DD_(" i ")"=> DmoveRT i
lemma commute_shifts (i j:Axis)(f:Test4): DmoveRT i (DmoveRT j f)= DmoveRT j (DmoveRT i f):=by
 let A:= fderiv ℝ f
 have he : ContDiff ℝ 2 f:= f.smooth 2
 ext1 x
 have hp:=he.fderiv_right (m:=1) (by norm_num) |>.differentiable (by norm_num) x
 have h(i j): DmoveRT i (DmoveRT j f) x= fderiv ℝ A x (basis i) (basis j):=by
    let J:=ContinuousLinearMap.apply ℝ ℂ (basis j); have hy: ⇑(DmoveRT j f)= J ∘ A:=funext fun y=>ΦsΛKnownL (basis j) f y
    rw[DmoveRT,ΦsΛKnownL,hy, (J.hasFDerivAt.comp x hp.hasFDerivAt).fderiv]; rfl
 rw[h,h]; exact he.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _
lemma hatch_shift (b:Test4) (h:Axis→Test4)(q:HatchRT b h) (j:Axis): HatchRT (b+DmoveRT j b) (fun i=>h i+DmoveRT j (h i)):=by
 have he(f:Test4)(p:HasCompactSupport ⇑f): HasCompactSupport ⇑(f+DmoveRT j f):= p.add (show IsCompact (tsupport (DmoveRT j f)) from p.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _))
 refine ⟨he _ q.cb,fun i=> he _ (q.ch i),?_,?_,?_⟩
 · filter_upwards [q.always,q.always.fderiv (𝕜:=ℝ)] with x u hx
   change b x + ΦshiftΛ _ _ x=1; rw [ΦsΛKnownL]; rw [hx]; have hX:(1:E4→ℂ)=fun x=> (1:ℂ):=rfl; simp [hX]; exact u
 · intro i x p vw; let a:= q.grow i x p vw
   filter_upwards [a,a.fderiv (𝕜:=ℝ)] with t z k
   change (h i+DmoveRT j (h i)) t= _; simp only [add_apply,z,map_add]; rw [commute_shifts i j b]; refine congrArg ((DmoveRT i b t)+·) ?_; rw [DmoveRT,ΦsΛKnownL,k]; exact (ΦsΛKnownL ..).symm
 intro i x p vw; let a:=q.fade i x p vw
 filter_upwards [a,a.fderiv (𝕜:=ℝ)] with t u k; change h i t + ΦshiftΛ _ _ _ = 0; rw [ΦsΛKnownL,k]; simp; exact u
lemma shifted_ir (b b':Test4)(f:Joint n): χTestRT k (b+b') f= χTestRT k b f+χTestRT k b' f:=by ext1 x; obtain ⟨a,rfl⟩:= (κMoverRT k).surjective x; simp only [add_apply]; rw [priceIRT,priceIRT,priceIRT]; exact add_mul ..
lemma successor_price (j:Axis)(b:Test4)(f:Joint n): DriftΛL (NSF.Points.direction k.succ j) (χTestRT k b f) = χTestRT k b (DriftΛL (NSF.Points.direction k j) f) - χTestRT k (DmoveRT j b) f:=by
 ext1 x; let K:=κMoverRT k; obtain ⟨⟨u,y⟩,rfl⟩:= K.surjective x; let d:=basis j; let Z:= NSF.Points.direction k j; let D:=NSF.Points.direction k.succ j; let e:=-d
 rw [DriftΛKnownL]
 have ht: K (e,Z)=D:=by
    unfold K; rw [motionKnownRT]; ext1 i; cases i using Fin.succAboveCases k.castSucc with
    | x => simp [Z,D,Points.direction,e,d,addXRT,tDiffRT k] 
    | p i=>
      by_cases q:i=k
      · simp [q,e,d,Z,D,Points.direction,insertSelfRT]
      have y: k.castSucc.succAbove i≠ k.succ:= by rw[← tNextRT k]; exact fun y=> q (Fin.succAbove_right_injective y)
      simp [Z,D,Points.direction,q,y,addXRT]
 let U(z:E4×Points n):= b z.1*f z.2
 let H:=χTestRT k b; have he: (H f) ∘ K=U:= funext fun x=> priceIRT ..
 have hx:=((H f).smooth 1).differentiable (by simp) (K (u,y))|>.hasFDerivAt
 have p:= hx.comp (u,y) (K.hasFDerivAt); rw [he] at p
 have hy:= p.unique ((HasFDerivAt.comp (f:=Prod.fst) (u,y) ((b.smooth 1).differentiable (by simp) u|>.hasFDerivAt) hasFDerivAt_fst).mul (HasFDerivAt.comp (f:=Prod.snd) (u,y) ((f.smooth 1).differentiable (by simp) y|>.hasFDerivAt) hasFDerivAt_snd))
 unfold D at ht; rw [←ht]; change (fderiv ℝ (H f) (K (u,y)) ∘L K.toContinuousLinearMap) (e,Z)= _; rw [hy]
 simp only [add_apply, smul_apply,ContinuousLinearMap.comp_apply,sub_apply]; unfold K; rw [priceIRT,priceIRT,DmoveRT,ΦsΛKnownL,DriftΛKnownL]; simp [mul_comm,e,d]; abel

-- sums exact at all pitches x; no regularity beyond this assumption on THE realized stress contour
variable (Y:Distn (Points n))(v:Axis→Distn (Points (n+1)))(ζ:ℂ)
def wageUnit : Prop:= ∀ (f:Joint n)(b:Test4)(h:Axis→Test4), HatchRT b h → ζ • ∑ i:Axis,v i (χTestRT k (h i) f)= Y f
variable (p:wageUnit k Y v ζ)
include p
lemma wage_derivation (j:Axis): wageUnit k (Y ∘L DriftΛL (NSF.Points.direction k j))
    (fun i=> v i ∘L DriftΛL (NSF.Points.direction k.succ j)) ζ:=by
 intro f b h e; let H':= fun i=> h i + DmoveRT j (h i); have y:=p f (b+DmoveRT j b) H' (hatch_shift b h e j); unfold H' at y; simp_rw [shifted_ir,map_add] at y; rw [sum_add_distrib,smul_add] at y; rw [p f b h e] at y
 simp_rw [ContinuousLinearMap.comp_apply, successor_price,map_sub]; rw [sum_sub_distrib,smul_sub,p _ b h e]; rw [show ζ • ∑ x,(v x) ((χTestRT k (DD_(j) (h x))) f)=0 from add_left_cancel (y.trans (add_zero _).symm),sub_zero]

#print axioms wage_derivation
end StressLaw
end YM.NSF.Boundary
end
