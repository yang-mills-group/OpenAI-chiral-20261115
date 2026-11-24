import Merino.Plume.Drift
import Merino.Hem.Agate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}


open Hem
/-- Apply angular pseudoscalar projector at origin, then pose at b:Cover,
linear (flavor tautological on this piece). c=clearM on use. -/
def chaste (b:Cover)(c:ℝ)(f:LinksC→ℂ)(x:LinksC):=
  (c:ℂ)*∑s:Signed,(ramp s:ℂ)*f (snow s b (detX s) x)

variable {f g:LinksC→ℂ}(b:Cover)(c:ℝ){L:ℝ}
lemma chaste_bound (p:∀x,‖f x‖≤L) (x:LinksC):‖chaste b c f x‖≤|c| *L:=by
 rw [chaste,norm_mul,Complex.norm_real,Real.norm_eq_abs]
 apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
 have h : ∀ s:Signed, ‖(ramp s:ℂ)*f (snow s b (detX s) x)‖ ≤ |ramp s| *L:=fun s=>by
   rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
   exact mul_le_mul_of_nonneg_left (p _) (abs_nonneg _)
 exact (norm_sum_le ..).trans ((sum_le_sum (fun s _=> h s)).trans_eq (by rw [← Finset.sum_mul, ramp_abs,one_mul]))

lemma chaste_sub (f g:LinksC→ℂ)(x):chaste b c (f-g) x=chaste b c f x-chaste b c g x:=by
 simp only [chaste,Pi.sub_apply,mul_sub,sum_sub_distrib]


lemma Swan.rampC (p:Swan (Lattice.box m) L f):Swan (vale m b) (|c| *L) (chaste b c f):=by
 refine ⟨measurable_const.mul (Finset.measurable_sum univ fun s _=>measurable_const.mul (p.hill s b (detX s)).reads),
   fun x y v=>congrArg (fun z=> (c:ℂ)*z) (sum_congr rfl fun s _=>congrArg ((ramp s:ℂ) * ·)
      ((p.hill s _ _).region x y v)),fun k x=>congrArg (fun z=>(c:ℂ)*z) (sum_congr rfl fun s _=>
       congrArg ((ramp s:ℂ)* ·) ((p.hill s b _).sang k x)),chaste_bound b c p.bound⟩

lemma Plump.rampC {F:ℕ→LinksC→ℂ}(p:Plump (Lattice.box m) L F f):
  Plump (vale m b) (|c| *L) (chaste b c ∘ F) (chaste b c f):=by
 refine ⟨fun i=>(p.1 i).rampC b c,fun e v=>?_⟩
 let d:=e/(|c|+1);have h:0<d:=div_pos v (by positivity)
 have t:|c| *d ≤ e:=by have g:d*(|c|+1)=e:=div_mul_cancel₀ _ (by positivity);linarith
 filter_upwards [p.2 d h] with i u x
 rw [dist_eq_norm,Function.comp_apply,←chaste_sub]
 exact (chaste_bound b c (L:=d) (f:=F i-f) (fun y=>by rw [Pi.sub_apply,←dist_eq_norm];exact u _) x).trans t


lemma chaste_period(n:Side)(f:LinksC→ℂ)(x:Pane n):
 chaste b c f (onC n x)=
   (c:ℂ)*pstar (f∘onC n)
        (Lattice.pull 1 (wrap (More n) b) x):=by
 simp only [chaste,pstar,purl,Function.comp_apply,revoke,slush]
 congr 1
 refine sum_congr rfl fun i _=>?_
 rw [pull_pull]
 change _=_*f (onC n (polarT (detX i) ∘ Lattice.pull (1*i) (affine 1 (wrap (More n) b)
    ((assembly n).root 0)) x))
 rw [map_zero,one_mul]
 simp only [affine,Signed.act_one,zero_add]

end YM.CF.Merino.Plume
