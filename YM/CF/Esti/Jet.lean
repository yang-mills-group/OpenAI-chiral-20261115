import YM.CF.Esti.Rix
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){A B:Stores S}{r v:ℕ}
open CF.Jet
variable {M:Type*}[NormedAddCommGroup M][NormedSpace ℝ M]{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{x:M}{i:ℝ}{n:ℕ}
abbrev cliff(b:Bool)(C:Chi)(v:ℝ):ℝ:=if b then C.read v else 1-C.read v
lemma cliff_s (C:Chi)(b:Bool): ContDiff ℝ ∞ (cliff b C):=by cases b; exact contDiff_const.sub C.smooth; exact C.smooth
lemma range_c (C:Chi)(b:Bool)(i:ℝ): cliff b C i∈ Set.Icc (0:ℝ) 1:=by cases b; exact ⟨sub_nonneg.mpr (C.range _).2,sub_le_self _ (C.range _).1⟩; exact C.range _
lemma cost_χ(q:Chi)(b:Bool)(n:ℕ):∃ C:ℝ, 1≤C∧∀ x:ℝ, Allows n (cliff b q) x C :=by
 let f:=cliff b q; let z:= Set.Icc (1:ℝ) 4
 -- ContDiff finite need compact
 have hp : ContDiff ℝ (n:ℕ∞ω) f:= (cliff_s q b).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
 choose c HH using fun i:Fin (n+1)=> (show IsCompact z from isCompact_Icc).exists_bound_of_continuousOn (hp.continuous_iteratedFDeriv (m:=i.val) (by have he:=i.isLt; exact_mod_cast (show i.val ≤ n by omega))).continuousOn
 let C:= 1+∑ i,|c i|; have hx:1 ≤ C:=le_add_of_nonneg_right (sum_nonneg fun i _=> abs_nonneg _)
 have hl(i:Fin (n+1)): c i≤ C:= (le_abs_self _).trans ((single_le_sum (f:=fun i=> |c i|) (fun i _=>abs_nonneg _) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
 refine ⟨C,hx,fun x=>?_⟩; by_cases k:x∈z
 · refine ⟨hp.contDiffAt,fun i l=> ?_⟩; exact (HH ⟨i,Nat.lt_add_one_iff.mpr l⟩ x k).trans (hl _)
 have H : f=ᶠ[𝓝 x] (fun _=> f x):=by
    rcases show x<1 ∨ 4<x by have hx:¬ (1 ≤ x ∧ x ≤ 4):=k; grind with l|l
    · filter_upwards [gt_mem_nhds l] with v p; have h:v≤1:=le_of_lt (Set.mem_Iio.mp p); cases b <;> simp [f,cliff,q.to_one v h, q.to_one x l.le]
    filter_upwards [lt_mem_nhds l] with v p; have h:4 ≤ v:=le_of_lt (Set.mem_Ioi.mp p); cases b <;> simp [f,cliff,q.to_zero v h, q.to_zero x l.le]
 exact (allows_const x (v:=f x) ((Real.norm_of_nonneg (range_c ..|>.1)).trans_le ((range_c q b x).2.trans hx))).germ H.symm
lemma point_r {f:ℝ→ℝ}(h:ContDiff ℝ (n:ℕ∞ω) f)(v:i∈ closure (interior {x|f x=0})): Allows n f i 0:=by
 let W:= interior {x|f x=0}; refine ⟨h.contDiffAt,fun j t=>?_⟩
 have hx : ∀ k∈ W, Allows n f k 0:=by
    intro k he; exact (allows_const (v:=(0:ℝ)) k (by simp)).germ (by filter_upwards [isOpen_interior.mem_nhds he] with y z; exact Eq.symm (Set.mem_setOf.mp (interior_subset z: y ∈ {x| f x=0}): _ = _))
 exact (closure_minimal (fun i p => (hx i p).norm_le j t) (isClosed_le (h.continuous_iteratedFDeriv (Nat.cast_le.mpr t)).norm continuous_const)) v
lemma steep (q:Chi)(b:Bool)(n:ℕ)(i:ℝ)(h:cliff b q i=0):Allows n (cliff b q) i 0:=by
 refine point_r ((cliff_s q b).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))) ?_; set X:= {x:ℝ|cliff b q x=0}; cases b
 · refine closure_mono (s:= Set.Iio i) (interior_maximal ?_ isOpen_Iio) (by simp); intro x hx; apply le_antisymm (h ▸ (show 1- _ ≤ cliff false q i from sub_le_sub_left (q.mono (Set.mem_Iio.mp hx).le) 1)) (range_c q false _).1 -- tune
 refine closure_mono (s:=Set.Ioi i) (interior_maximal ?_ isOpen_Ioi) (by simp); intro y p; exact le_antisymm ((q.mono (Set.mem_Ioi.mp p).le).trans_eq h) (q.range _).1
-- need bounded for has exp derivatives
lemma mori(C:Chi)(b:Bool){v:M→ℝ}{K:ℝ}(p:Allows n v x K)(h:cliff b C (v x)=0): Allows n (cliff b C ∘ v) x 0:=by simpa only [Function.comp_def,composeCost, mul_zero,zero_mul] using ((steep C b n _ h).comp p)
def Zed(n:ℕ)(f:M→E)(u:M):Prop:= f u=0 → Allows n f u 0
variable {f g:M→ℝ}{K C Q:ℝ}
lemma zed(q:Chi)(b:Bool)(f:M→ℝ)(h:Allows n f x C):Zed n (cliff b q ∘ f) x:=fun t=> mori q b h t
lemma sigP(g:M→ℝ)(p:0<g x):Zed n g x:= fun t=>False.elim (p.ne' t)
def zest(n:ℕ):ℝ:= 1+(2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℝ‖
lemma zpos(n:ℕ):1 ≤ zest n:=le_add_of_nonneg_right (by positivity)
lemma allot (p:Allows n f x K)(q:Allows n g x C): Allows n (fun w=> f w*g w) x (zest n*K*C):=((p.bilinear (ContinuousLinearMap.mul ℝ ℝ) q le_rfl).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) p.nonneg) q.nonneg)) -- tune
lemma fern (p:Allows n f x K)(q:Allows n g x C)(k:Zed n f x)(u:Zed n g x): Zed n (fun w=>f w*g w) x:=by
 intro hp; rcases mul_eq_zero.mp hp with h|h
 · exact (show zest n*0*C=0 by ring) ▸ allot (k h) q
 exact (show zest n*K*0=0 by ring) ▸ allot p (u h)
lemma fuel{I:Type*} [DecidableEq I](S:Finset I)(f:I→ M→ℝ)(p:∀ i∈ S, Allows n (f i) x K ∧ Zed n (f i) x): Allows n (fun w=>∏ i∈S,f i w) x ((zest n*K)^S.card)∧ Zed n (fun w=>∏ i∈S,f i w) x:=by
 induction S using Finset.induction_on with
 | empty=> simp only [prod_empty,card_empty,pow_zero]; exact ⟨allows_const x (by simp),sigP _ (by norm_num)⟩
 | insert i s v ih=>
    obtain ⟨l,t⟩:= ih fun i h=>p i (mem_insert_of_mem h); obtain ⟨h,h'⟩:=p _ (mem_insert_self ..); simp_rw [prod_insert v,card_insert_of_notMem v,pow_succ']; exact ⟨allot h l,fern h l h' t⟩
lemma light_c(g:M→ℝ)(p:Allows n g x K)(C:ℝ)(h:g x ≤ C) : Allows n (Real.exp ∘ g) x ((n.factorial:ℝ)*Real.exp C * (1+K)^n) :=by
 refine Allows.comp (f:=g) ?_ p; refine ⟨Real.contDiff_exp.contDiffAt,fun i t=>?_⟩; rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp,Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr h
lemma lit_u (h:Zed n f x)(p:Allows n f x Q){A:ℝ}(u:Allows n g x K)(hy:f x ≠ 0 → g x ≤ C): Allows n (fun i=> f i * Real.exp (g i)) x (zest n*Q*((n.factorial:ℝ)*Real.exp C*(1+K)^n)):=by
 by_cases l:f x=0
 · apply (allot (h l) (light_c g u (g x) le_rfl)).mono; have hx:=zpos n; have hl:=u.nonneg; have hv:=p.nonneg; rw [mul_zero,zero_mul]; positivity
 exact allot p (light_c g u _ (hy l))
end YM.CF.Esti
