import GaugeFieldConstruction.AgilaM
import GaugeFieldConstruction.Ambria
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I M E:Type}[Fintype I][LinearOrder I]
-- key calculus even at contacts.Axis.H.K. Domain for $v need$ disjoint tested tip list.
section
variable [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable (S:List I)(k:I)(f g:Key I→ E)(t:List I)(v:∀ i∈ S,i∉ t)
-- generalized restricted transfer from analytic readers
include v
private lemma ler (e:∀ i∈hill I,(∀ j∈S,i j=0)→f i=g i):tipI f t=tipI g t:=by
 induction S generalizing f g with
 | nil=> exact lace_C _ (fun x k=> e x k (by simp)) roots
 | cons j s ih=>
    rw [←tip_V (f:=f) j t (v _ (by simp)),←tip_V (f:=g) j t (v _ (by simp))]; refine ih (f∘dune j) (g∘dune j) (fun i k=>v _ (by simp[k])) (fun i p v=>e _ (dune_P j p) (by
       intro y q; by_cases h:y=j
       · rw [h,dune,update_self]
       rw[dune,update_of_ne h,v y ((List.mem_cons.mp q).resolve_left h)]))
lemma lead_cut (hp:River f)(hg:River g)(w:k∉t)(u:k∉S)(μ:ℂ) (e:∀ x∈hill I,(∀ i∈ S,x i=0) → f x=(x k * μ) • lance g S x) :tipI f (k::t)= μ • tipI g (S++t):=by
 let l:=lance g S; have h:=laced hg S
 have he(z)(p:z∈hill I)(q:∀ i∈ S,z i=0): cutI f k z= μ • lance g S (dune k z):=by
    have w0: (fun w=> f (update z k w)) =ᶠ[𝓝 (0:ℂ)] (fun w=> w • (μ • l (update z k w))):=by
       filter_upwards [Metric.ball_mem_nhds (0:ℂ) zero_lt_one] with w wh; rw[e (update z k w) (fill_I p _ (ball_subset_closedBall wh)) (fun i hi=>by rw[update_of_ne (fun v:i=k=> u (v▸hi)),q i hi]),update_self,mul_smul]
    have T:= (mitt hp p k); have t:= (mitt (h.scale μ) p k)
    have hZ:= (hasDerivAt_id' (0:ℂ)).smul t
    exact T.unique ((hZ.congr_of_eventuallyEq w0).congr_deriv (by simp [dune]))
 have hR:=ler S _ _ t v he; rw [show tipI f (k::t)=tipI (fun x=> μ • lance g S (dune k x)) t from hR,show tipI (fun x=> μ • lance g S (dune k x)) t= μ • tipI ((lance g S)∘dune k) t from tip_C ((laced hg S).stay k) μ t,tip_V k t w]
 suffices hx:∀ S:List I,∀ g:Key I→E,tipI (lance g S) t= tipI g (S++t) by rw [hx]
 intro S; induction S with
 | nil=> exact fun _=>rfl
 | cons i S ih=> exact fun g=>ih (cutI g i)
-- if t disjoint f.h.Comp.Vector old blankK p supplied by induction. no cross.With leftover reserved.
omit v
lemma tip_nurse (h: River f) (p:k ∉ t)(e:f∘dune k=g∘dune k) : tipI f t=tipI g t:=by rw[←tip_V (f:=f) k _ p,←tip_V (f:=g) k _ p,e]
lemma tip_charity (h:River f) (e:f∘dune k=f) : tipI f (k::t) = 0:=by
 have hx(x:Key I)(v:x∈hill I): cutI f k x=0:=by
    rw[←(mitt h v k).deriv]; have he(i:ℂ):f (update x k i)= f (update x k 0):=by
       apply Eq.trans (congrFun e (update x k i)|>.symm); rw [comp_apply,dune,update_idem]
    rw[funext he,deriv_const]
 apply (lace_C t (show Set.EqOn (cutI f k) (fun _=>0) _ from fun i v=> hx i v) roots).trans; exact tip_0 _
end
section
open Grotto
variable {α:Type}[Fintype α]{n:Side}{L:I→ Site n}[NormedCommRing M][NormedAlgebra ℂ M][CompleteSpace M]
variable (f g r:Key I→ M)(σ:I→ Site n)
variable (u:Kin σ f (g+r))(S:List I)(v:r=r)
-- ℂ linear.River for h from Kin rhs.Tip_K exactly selector. no need include all k probes.
include u
lemma onRich (S:List I)(k:I)(μ:ℂ)(w:River g)(e:∀ x∈hill I,(∀ i∈S,x i=0)→ r x=(x k * μ) • lance g S x) (h : g ∘ dune k=g) (q:k∉ S) (t:List I)(hu:ψS σ (k::t))(p:∀ i∈ S,i∉t): tipI f (k::t)= μ • tipI g (S++t):=by
 have hp:River r:=by
    rw [show r=g+r + (-1:ℂ) • g from Eq.symm (by rw [neg_one_smul,add_comm g r, add_neg_cancel_right])]; exact dub_V u.2 (w.scale _)
 rw [u.3 _ hu, show tipI (g+r) _=_ from tip_A w hp _, tip_charity k g t w h,zero_add]; exact lead_cut S k _ g t p hp w (List.nodup_cons.mp (List.Nodup.of_map σ hu)).1 q _ e
lemma onRest (k:I)(w:River g)(e:∀ x: Key I,r (dune k x)=0)(t: List I)(p:k∉t)(hu:ψS σ t): tipI f t=tipI g t:=by
 rw [u.3 _ hu]; apply tip_nurse k _ g t u.2 p; funext x; rw [comp_apply,Pi.add_apply,e,add_zero]; rfl
end
end Iona
end YM.CF.Scree.Ing
end
