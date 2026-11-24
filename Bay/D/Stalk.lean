import Bay.D.Foret
import Bay.D.Blink
import Bay.Alcove
import Zephyr.Chern.Bends
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical

namespace D

open Zephyr.Chern
def plum(t:ℝ):=SU.group.plog (SU.group.mat (arc t))
@[simp] lemma plum_z : plum 0=0:=by simp [plum,arc_zero]
open scoped Matrix.Norms.Frobenius in
lemma plum_at : DifferentiableAt ℝ plum 0:=by
 have h:Differentiable ℝ (fun t:ℝ=>Matrix.diagonal (fun i=>Complex.exp (Complex.I * dye.val i * t)) : ℝ → SU.group.Mat):=
    (Matrix.diagonalLinearMap SU.F ℝ ℂ).toContinuousLinearMap.differentiable.comp
      (show Differentiable ℝ (fun t:ℝ=>fun i=>Complex.exp (Complex.I*dye.val i*t)) by fun_prop)
 have he : DifferentiableAt ℝ (fun t:ℝ=>SU.group.mat (arc t)) 0:=
   (h 0).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t=>congrArg Prod.snd (brand_arc t)))
 exact DifferentiableAt.comp _ (by rw[arc_zero,SU.group.mat_one];exact SU.group.plog_diff.differentiableAt (by norm_num)) he

end D
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

open Zephyr.Chern Extra.Iteration.Channel

/-- Tangent of Cartan subgroup in payment coordinates. -/
def yolk := deriv plum 0
variable {N:Side}{o:Seat N}
def shear (X:StemA N):Lag N:=fun i=> X ((bondBody _).symm i) • yolk
def skew (X:StemA N)(t:ℝ):Lag N:=fun i=> plum (X ((bondBody _).symm i)*t)
lemma sheared(X:StemA N):HasDerivAt (skew X) (shear X) 0:=by
 apply hasDerivAt_pi.mpr
 intro i; let v:= X ((bondBody _).symm i)
 have h : HasDerivAt (fun t:ℝ=>v*t) v 0 := by simpa using (hasDerivAt_id' 0).const_mul v
 have j: HasDerivAt plum yolk ((fun t:ℝ=>v*t) 0):=by simp only [mul_zero]; exact plum_at.hasDerivAt
 exact j.scomp _ h
@[simp] lemma skew0(X:StemA N):skew X 0=0:=by funext i;simp [skew]
lemma traced(X:StemA N):∀ᶠ t:ℝ in 𝓝 0, represent (skew X t)=petals X t:=by
 have h(i:Edge (Seat N)): Tendsto (fun t:ℝ=>petals X t i) (𝓝 0) (𝓝 1):=
    by simpa [petal_idle,Function.comp_def] using ((continuous_apply i).comp (cont_petal X)).tendsto 0
 filter_upwards [eventually_all.mpr fun i=> (h i).eventually group.plog_right] with t g
 funext i; rw [Work.F03.represent_link]
 change group.lieExp (skew X t (bondBody _ i))=_
 unfold skew; rw [Equiv.symm_apply_apply]; exact g i

variable {n:Side}
def seltzer (n:Side) : fieldDir group n 1 →ₗ[ℝ] (Cella n→ℝ) :=
    LinearMap.pi (fun i=> (EuclideanSpace.projₗ i).comp (canal univ)) -- proj
lemma sip (x:fieldDir group n 1): seltzer n x = brine x :=funext fun _=>if_pos (mem_univ _)

variable {p:BudgetPoint}{f:Pane N→ℂ}{A:Icey (Cella (More N))}{c:ℂ}{r M:ℝ}{k:ℕ}
lemma stalk
   (q:Skin p o k r M f c A)(h:0<r) (X:StemA N)
   (u:Bud (f ∘ Zephyr.Chern.petals X)):
   bud (f ∘ Zephyr.Chern.petals X) 1=0 ∧
   bud (f ∘ Zephyr.Chern.petals X) 2=splash A (brine (shear X)):=by
 let W(t:ℝ):=skew X t
 let T:=𝓝[>] (0:ℝ)
 have hh:Tendsto (fun t:ℝ=> t⁻¹ • W t) T (𝓝 (shear X)):=by
   simpa only [zero_add,skew0,sub_zero] using (hasDerivAt_iff_tendsto_slope_zero.mp (sheared X)).mono_left (nhdsGT_le_nhdsNE _)
 have hj:Tendsto (fun t:ℝ=> M*‖W t‖*‖t⁻¹ • W t‖^2) T (𝓝 0):=by
   have hv:= (sheared X).continuousAt.tendsto
   rw[skew0 X] at hv -- rewrites ?
   simpa using ((hv.mono_left nhdsWithin_le_nhds).norm.const_mul M).mul (hh.norm.pow 2)

 let g(t:ℝ):= splash A (brine (t⁻¹ • W t))
 have he(t):g t = t⁻¹^2 • splash A (brine (W t)):=by
    unfold g splash
    rw [←sip,map_smul,sip, swirl_xyScale,sq]
 have a0: f (Zephyr.Chern.petals X 0) = c:=by rw[petal_idle,q.wakes h]
 have ha:Tendsto (fun t:ℝ=> t⁻¹^2 • (f (Zephyr.Chern.petals X t)-c)-g t) T (𝓝 0):=by
   refine squeeze_zero_norm' ?_ hj
   have hr:= (sheared X).continuousAt.norm.eventually (ge_mem_nhds (show ‖skew X 0‖< r by simpa using h))
   filter_upwards [eventually_nhdsWithin_of_eventually_nhds ((litAngle o p X).and ((traced X).and hr))]
     with t d
   have e:=q.turns d.1 d.2.2 (by rw[d.2.1];exact fun _ _ _=>rfl)
   rw[he,←smul_sub,norm_smul,←sub_add_eq_sub_sub]
   refine (mul_le_mul_of_nonneg_left e (norm_nonneg _)).trans_eq ?_
   rw[norm_smul,norm_pow]; unfold W; ring
 have hd:Tendsto g T (𝓝 (splash A (brine (shear X)))):=by
    have hl:Continuous (fun x:Lag N=> splash A (seltzer _ x)):=by
       change Continuous (fun x:Lag N=> splash A ((seltzer _).toContinuousLinearMap x)); unfold splash swirl; fun_prop
    simp_rw[sip] at hl
    exact (hl.tendsto _).comp hh
 apply bingo u; rw [show (f ∘ Zephyr.Chern.petals X) 0=c from a0]

 simpa only [T,Function.comp_apply,sub_add_cancel,zero_add] using ha.add hd
