import Mathlib.Analysis.Complex.RealDeriv
import WinterX.Camera
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Compass
open Function Set Metric Filter Complex MeasureTheory Finset
open scoped Topology
open Mew
variable {E E':Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E][CompleteSpace E][NormedAddCommGroup E'][NormedSpace ℂ E'][NormedSpace ℝ E'][IsScalarTower ℝ ℂ E'][CompleteSpace E']
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
lemma has_axis (Q:ℂ→E)(e:E)(h:HasDerivAt Q e 0): HasDerivAt (fun x:ℝ=>Q (x:ℂ)) e 0:=by
 let F:ℂ→L[ℝ]E:=((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) e).restrictScalars ℝ)
 have h': HasFDerivAt Q F 0 := h.hasFDerivAt.restrictScalars ℝ
 let W:= Complex.ofRealCLM
 have u: HasDerivAt (Q ∘ W) (F (W 1)) 0:=(by have hb:W 0=0:=map_zero W; exact (hb.symm ▸ h').comp_hasDerivAt (0:ℝ) (W.hasDerivAt))
 rw [show F (W 1)=e from (show _=_ from (by change ((1:ℝ):ℂ) • e =_; rw [Complex.ofReal_one,one_smul]))] at u; exact u
lemma slicing (f:Key I→E)(p:River f)(i:I):HasDerivAt (fun x:ℝ=> f (Function.update 0 i (x:ℂ))) (tipI f [i]) 0:=has_axis _ _ (mitt p roots i)
lemma turnG (f:Key I→E)(p:River f)(i:I)(g:Key J→E')(u:River g)(j:J)(C:E→L[ℝ] E')(φ:ℝ)(w:φ*φ=1)
    (hv:∀ x:ℝ,‖x‖≤1→ g (update (0:Key J) j (φ*x:ℝ))= C (f (update (0:Key I) i (x:ℂ)))): tipI g [j]= φ • C (tipI f [i]):=by
 let H:= fun x:ℝ=> g (update (0:Key J) j (x:ℂ)); let F:=fun x:ℝ=> f (update (0:Key I) i (x:ℂ)); let k:=fun x:ℝ=>φ*x
 have h0:k 0=0:=mul_zero φ; have h:HasDerivAt k φ 0:=by simpa [k] using (hasDerivAt_id (0:ℝ)).const_mul φ
 have A:HasDerivAt (H ∘ k) (φ • tipI g [j]) 0:=(h0.symm ▸ slicing g u j).scomp _ h
 have B:HasDerivAt (C ∘ F) (C (tipI f [i])) 0:=C.hasFDerivAt.comp_hasDerivAt _ (slicing f p i)
 have q: C ∘ F =ᶠ[𝓝 0] H ∘ k:= Filter.mem_of_superset (ball_mem_nhds _ one_pos) fun x t=>(hv x (mem_ball_zero_iff.mp t).le).symm
 calc
 tipI g [j]=φ •(φ • tipI g [j]):=(Eq.symm ((smul_smul ..).trans (by rw [w,one_smul])))
 _ = φ • C (tipI f [i]):= congrArg _ (A.unique (B.congr_of_eventuallyEq q.symm))
#check turnG
end YM.CF.Compass
