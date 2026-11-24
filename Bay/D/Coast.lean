import Bay.D.Purr
import Bay.D.Genoa
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
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group

variable {I J:Type*}[Fintype I][Fintype J]{s:Finset I}{A:Icey I}
lemma wave_lip {e u b:ℝ}(g:Rake s e A)
    (t:0≤u)(l:0≤b)
    (x y:J→I→ℝ)
    (hx:∀i∈s,∀j,|x j i|≤u)(hy:∀i∈s,∀j,|y j i|≤u)
    (h:∀i∈s, ∑j:J, |x j i -y j i|≤b):
 ∑j,‖splash A (x j)-splash A (y j)‖≤(2*u*b)*e:=by
 let d j i k:= |x j i*x j k-y j i*y j k|
 have hp(j:J):‖splash A (x j)-splash A (y j)‖≤∑i,∑k,d j i k*‖A i k‖:=by
     simp_rw[splash,swirl, ←sum_sub_distrib,←sub_smul]
     exact (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans_eq (sum_congr rfl fun k _=>norm_smul ..))
 have hu(i k:I)(f:i∈s)(m:k∈s):(∑j,d j i k)≤2*u*b:=by
     apply le_trans (b:=∑j,(|x j i-y j i| *u+ u*|x j k-y j k|))
     · refine sum_le_sum fun j _=>?_
       unfold d;rw [show x j i*x j k-y j i*y j k=(x j i-y j i)*x j k+y j i*(x j k-y j k) from by ring]

       apply (abs_add_le ..).trans;rw[abs_mul,abs_mul]
       gcongr
       · exact hx _ m _
       exact hy _ f _
     rw [sum_add_distrib,←sum_mul,←mul_sum]
     refine (add_le_add (mul_le_mul_of_nonneg_right (h _ f) t) (mul_le_mul_of_nonneg_left (h _ m) t)).trans_eq ?_; ring
 refine (sum_le_sum (s:=univ) (fun j _=>hp j)).trans (le_trans ?_ (mul_le_mul_of_nonneg_left g.fee (by positivity)))
 unfold swill; rw [sum_comm,mul_sum]; refine sum_le_sum fun i _=>?_
 rw [sum_comm, mul_sum]; refine sum_le_sum fun k _=>?_
 rw[←sum_mul]
 by_cases hz:A i k=0
 · simp[hz]
 have f:=g.fits _ _ hz
 exact mul_le_mul_of_nonneg_right (hu _ _ f.1 f.2) (norm_nonneg _)

lemma wave_crest {e u K:ℝ}(g:Rake s e A)(x:I→ℝ)(t:0≤u)
 (p:∀i∈s, |x i|≤u): ‖splash A x-splash A (pur K ∘ x)‖≤e*2*u^4/K^2:=by
 have a(i:I)(h:i∈s): |(pur K ∘ x) i|≤u:= (pur_clip ..).trans (p _ h)
 have h:= wave_lip g t (show 0≤u^3/K^2 by positivity)
    (fun _:Fin 1=>x) (fun _:Fin 1=>pur K ∘ x) (fun i m _=>p i m) (fun i m _=> a i m) (fun i m=>by
      simp only [Fin.sum_univ_one,abs_sub_comm (x i)]

      exact (pur_bent (x i)).trans (by gcongr; exact p _ m))
 rw [Fin.sum_univ_one] at h
 exact h.trans_eq (by ring)

variable {n:Side}
abbrev delta(q:Clip)(ρ:ℝ)(g:Kite n)(x:Dock n):Cella n→ℝ:=ρ • sea q g x
abbrev quay(q:Clip)(ρ K:ℝ)(A:Icey (Cella n))(g:Kite n)(x:Dock n):ℂ:=
 splash A (pur K ∘ delta q ρ g x)
abbrev shoal(q:Clip)(ρ:ℝ)(A:Icey (Cella n))(g:Kite n)(x:Dock n):ℂ:=
 splash A (delta q ρ g x)
-- power quantitative
def ratioC(q:Clip):ℝ:= 2*(rays q 2)*(Fintype.card Signed:ℝ)
lemma ratioC_p(q:Clip):0≤ratioC q:=by unfold ratioC Etch.rays; positivity
variable {s:Finset (Cella n)}{A:Icey (Cella n)} {e K:ℝ}
variable (q:Clip)(ρ:ℝ)
lemma quay_height(g:Kite n)(x: Dock n)(h:Rake s e A)(u:0<K):
 ‖quay q ρ K A g x‖≤ e*K^2:=by
 rw[mul_comm,sq]; exact h.fee_swirl u.le u.le (fun _ _=>pur_max _ u) (fun _ _=>pur_max _ u)
lemma quay_smooth(K:ℝ)(A:Icey (Cella n))(g:Kite n):
 ContDiff ℝ 1 (quay q ρ K A g):=by
 have h(i:Cella n): ContDiff ℝ 1 (fun x=>pur K (delta q ρ g x i)) :=
         (pur_smooth K).comp (contDiff_const.mul (sea_smooth g i q))

 exact ContDiff.sum fun i _=>ContDiff.sum fun j _=> ((h i).mul (h j)).smul contDiff_const
lemma quay_charge
    (h:|ρ|≤2)(v:Rake s e A)(u:0<K)
    (o:Site n)(gs:I→Kite n)
    (p:Injective (fun i=>(gs i).rise o))
    (x y:Dock n):
 ∑i:I, ‖quay q ρ K A (gs i) x-quay q ρ K A (gs i) y‖≤
    e*ratioC q*K*Real.sqrt (Fintype.card I)*‖x-y‖:=by
 have l : 0≤Etch.rays q ρ:=by unfold Etch.rays; positivity
 have g:Etch.rays q ρ≤Etch.rays q 2:=by unfold Etch.rays;rw[abs_of_nonneg (by norm_num : (0:ℝ)≤2)];gcongr
 have l₂:=l.trans g
 let b:=Etch.rays q 2*((Fintype.card Signed:ℝ)*Real.sqrt (Fintype.card I)*‖x-y‖)
 rw [show e*ratioC q*K*Real.sqrt (Fintype.card I)*‖x-y‖=(2*K*b)*e from ?_] -- missing left
 apply wave_lip v u.le (by unfold b; positivity)
     (fun i=>pur K ∘ delta q ρ (gs i) x) (fun i=>pur K ∘ delta q ρ (gs i) y)
     (fun _ _ _=>pur_max _ u) (fun _ _ _=>pur_max _ u)
 intro j _
 unfold b; refine le_trans ?_ (mul_le_mul g (celia j o gs p (x-y)) (sum_nonneg (fun i _=>norm_nonneg _)) l₂)
 rw[mul_sum]; refine sum_le_sum fun i _=> (pur_lip _ _ K).trans ?_
 change |ρ*_ -ρ*_|≤_

 rw [←mul_sub,sea_minus]
 exact sea_le _ _ _ _ _
 unfold ratioC b; ring
end YM.CF.Bay.D
