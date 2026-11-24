import GaugeFieldConstruction.StyriaRel.YM.Work.C15
-- Rigorous probe of one cumulative suffix shift at all real base points, Lemma 137 cone. No relative volume constants; work on absolute Points.
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary.Ferry
open YM.Boundary Work Work.C15
open Function MeasureTheory Filter Set Distribution Probe
open scoped Topology InnerProductSpace Classical ContDiff
variable {n:ℕ}
noncomputable def skirt (j:ℕ)(x:E4):Points n:=points fun i=> if j ≤ i.val then x else 0
@[simp] lemma skirt_apply (j:ℕ)(x:E4)(i:Fin n):skirt j x i= if j ≤ i.val then x else 0:=rfl
@[fun_prop] lemma skirt_ct(j:ℕ):Continuous (skirt (n:=n) j):= by unfold skirt points; refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i : Fin n => ?_)); by_cases h:j ≤ i.val <;> simp [h] <;> fun_prop
noncomputable def vane (j:ℕ): Points n →L[ℝ] E4:= LinearMap.toContinuousLinearMap
 {toFun:=fun p=> suffixP p j
  map_add':=by intro a b; unfold suffixP; rw[←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; split<;>simp_all
  map_smul':=by intro a b; dsimp only[RingHom.id_apply]; unfold suffixP; rw[Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_; split<;>simp_all}
@[simp] lemma vane_at (j:ℕ)(x:Points n): vane j x=suffixP x j:=rfl
lemma skirt_push (j:ℕ)(p:Points n)(x:E4):Probe.plane p (skirt j x)=Probe.plane x (vane j p):=by
 rw[Probe.plane_dot x]; unfold Probe.plane; congr 3
 rw[vane_at,suffixP,sum_inner,PiLp.inner_apply]; refine Finset.sum_congr rfl fun i _=>?_; rw[skirt_apply]; split_ifs<;>simp
noncomputable def pliss (j:ℕ)(f:Test4)(g:Joint n):Joint n:= ↑(pref E4) • (SchwartzMap.smulLeftCLM ℂ (⇑f∘vane j) g:Joint n) -- type annotate
lemma pliss_at (j:ℕ)(f:Test4)(g:Joint n)(x:Points n): pliss j f g x=(pref E4 • f (vane j x)) *g x:=by
 have he:HasTemperateGrowth (⇑f ∘ (vane j:Points n→L[ℝ]E4)):= f.hasTemperateGrowth.comp (ContinuousLinearMap.hasTemperateGrowth _)
 simp [pliss, SchwartzMap.smulLeftCLM_apply_apply he,Complex.real_smul, mul_assoc]
lemma pliss_conn (j:ℕ)(f:Test4)(g:Joint n)(x:Points n):
 (∫ b, hat g (x-skirt j b)*hat f b) = hat (pliss j f g) x:=by
 let X(b:E4)(p:Points n):= Probe.plane p (-(x-skirt j b))*g p*hat f b
 have hx:Continuous (uncurry X):= by unfold uncurry X Probe.plane; fun_prop
 have hi:Integrable (uncurry X) (volume.prod volume):=by
    refine ((hat f).integrable.norm.mul_prod g.integrable.norm).mono' hx.aestronglyMeasurable (ae_of_all _ fun p=>?_); simp [uncurry,X,mul_comm]
 calc
    _ = ∫ b,∫ p,X b p :=by simp_rw [hat_eq g]; simp_rw [X,integral_mul_const]
    _ = ∫ p,∫ b,X b p := integral_integral_swap hi
    _ = _:=by
       rw[hat_eq]; refine integral_congr_ae (ae_of_all _ fun p=>?_)
       have hu b:X b p= Probe.plane p (-x)*g p*(Probe.plane b (vane j p)*hat f b):=by
          dsimp only[X]; rw[show -(x-skirt j b) = -x+skirt j b by abel, Probe.plane_add,skirt_push]; ring
       simp_rw[hu,integral_const_mul,positiveFourier,pliss_at]; ring
#print axioms pliss_conn
end YM.NSF.Boundary.Ferry
end
