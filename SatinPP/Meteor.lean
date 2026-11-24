import SatinPP.Steel
import SatinThinJetsPrism
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option maxRecDepth 3500
set_option quotPrecheck false
noncomputable section

namespace YM.Quays
open Function Set Filter Metric Topology MeasureTheory InnerProductSpace
open scoped Topology BigOperators InnerProductSpace ComplexOrder Classical NNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open OS Semigroup
variable {X:Hilbert}{j:Axis}{S:OS.Semigroup X j}{n:ℕ}{c:ℝ}{A:Stamp X}

lemma eq_inside {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
  {f g:ℂ→E} (p:AnalyticOnNhd ℂ f inside)(q:AnalyticOnNhd ℂ g inside)
  (e:∀ t:ℝ,0<t→f t=g t):
  EqOn f g inside:=by
 let F':=Complex.ofReal
 refine p.eqOn_of_preconnected_of_frequently_eq q
   (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0 |>.isPreconnected)
   (z₀:=F' 1) (show (0:ℝ)<1 from zero_lt_one) ?_
 intro h
 have t:Tendsto F' (𝓝[>] (1:ℝ)) (𝓝[≠] (F' 1)):=by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact Eventually.mono self_mem_nhdsWithin fun i p w=> (mem_Ioi.mp p).ne' (Complex.ofReal_injective w)
 obtain ⟨k,v,q⟩:= ((t.eventually h).and self_mem_nhdsWithin).exists
 exact v (e k (zero_lt_one.trans (mem_Ioi.mp q)))

variable (Ω:X)
def Vac (A:Stamp X)(Y:ℂ→X) := ∀ u v:ℝ,0<u→0<v→A u v Ω=Y u

open ContinuousLinearMap (apply)
variable {z w:ℂ}(T:Paid S n c A){Y:ℂ→X}(p:AnalyticOnNhd ℂ Y inside)(t:Vac Ω A Y)
include T p t
lemma lift_vac (a:z∈inside)(b:w∈inside):paint S A z w Ω=Y z:=by
 let L:X.Op→L[ℂ]X:= (apply ℂ X.space) Ω
 let R:= paint S A
 have h(v:ℝ)(u:0<v): EqOn (fun x=>L (R x v)) Y inside:=by
   refine eq_inside (fun x y=>(L.analyticAt _).comp (f:=fun x=>R x v) (analyticAt_paint T (f:=id) (g:=fun _=> (v:ℂ)) y (show (v:ℂ)∈inside from u) analyticAt_id analyticAt_const)) p ?_
   intro s a
   unfold R; rw [paint_real T a u]
   exact t s v a u
 have i: AnalyticOnNhd ℂ (fun x=> L (R z x)) inside:=fun x y=>(L.analyticAt _).comp
      (f:=fun x=>R z x) (analyticAt_paint T (f:=fun _=>z) (g:=id) a y analyticAt_const analyticAt_id)
 exact eq_inside i analyticOnNhd_const (fun u hv=>h u hv a) b


lemma flick_vac: Vac Ω (flicks S A) (deriv Y):=by
 intro u v hu hv
 have a : (u:ℂ)∈inside:= hu
 have b : (v:ℂ)∈inside:= hv
 let L:X.Op→L[ℂ]X:= (apply ℂ X.space) Ω
 let f(d:ℂ):= L (paint S A (u+d) (↑v-d))
 have h:HasDerivAt (fun z=>Y (u+z)) (deriv Y u) 0:=by
   have e : HasDerivAt (fun z:ℂ=>(u:ℂ)+z) 1 0:=(hasDerivAt_id' _).const_add _
   have h: HasDerivAt Y (deriv Y u) ((u:ℂ)+0):=by rw [add_zero]; exact (p u a).differentiableAt.hasDerivAt
   exact (h.scomp _ e).congr_deriv (one_smul ..)
 refine HasDerivAt.unique
   (show HasDerivAt f ((flicks S A u v) Ω) 0 from L.hasFDerivAt.comp_hasDerivAt _ (hasFlick T a b))
   (h.congr_of_eventuallyEq ?_)
 filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually
        (open_inside.mem_nhds (show (u:ℂ)+0∈inside from by simpa using a)),
    (continuous_const.sub continuous_id).continuousAt.eventually
        (open_inside.mem_nhds (show (v:ℂ)-0∈inside from by simpa using b))] with z hu hv
 exact lift_vac Ω T p t hu hv

omit T p t
variable (S)

/-- Exact property used in the Wick prescription. m may depend
on the stamp (also on the jet). -/
def Sold (A:Stamp X) : Prop:=∃ m c,Paid S m c A

variable {S}
lemma reindex_cost {m:ℕ}(T:Paid S n c A)(a:n ≤ m): Paid S m c A:=
 ⟨T.pos,T.fits,fun h u=> (T.le h u).trans <|
    div_le_div_of_nonneg_left T.pos.le (pow_pos h _) (pow_le_pow_of_le_one h.le u a)⟩

lemma Sold.zero (S:OS.Semigroup X j):Sold S (0:Stamp X):=
   ⟨0,1,zero_lt_one,fun a b h t=>(map_zero _).symm,fun a b=>by simp⟩
lemma Sold.smul (p:Sold S A)(z:ℂ): Sold S (z • A):=by
 obtain ⟨n,c,T⟩:=p; have h:= T.pos
 refine ⟨n,(‖z‖+1)*c,by positivity,?_,?_⟩
 · intro u v s t a b p q; simp only [map_smul,Pi.smul_apply,T.fits a b p q]
 intro u a d
 rw [Pi.smul_apply,Pi.smul_apply,norm_smul,mul_div_assoc]
 exact mul_le_mul (le_add_of_nonneg_right zero_le_one) (T.le a d) (norm_nonneg _) (by positivity)
lemma Sold.add {B:Stamp X}(p:Sold S A)(q:Sold S B):Sold S (A+B):=by
 obtain ⟨l,c,T⟩:=p; obtain ⟨m,d,Y⟩:=q
 have H:=reindex_cost T (le_max_left _ m)
 have R:=reindex_cost Y (le_max_right l _)


 refine ⟨max l m,c+d, add_pos T.pos Y.pos,fun a b p q=> ?_, fun a p=>?_⟩
 · simp only [Pi.add_apply,map_add,T.fits a b p q,Y.fits a b p q]
 rw [add_div]; exact (norm_add_le ..).trans (add_le_add (H.le a p) (R.le a p))

lemma Sold.sum {ι:Type}(I:Finset ι)(B:ι→Stamp X)(p:∀ i, Sold S (B i)): Sold S (∑ i∈I,B i):=by
 induction I using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact .zero ..
 | insert i J h ih=> rw [Finset.sum_insert h]; exact .add (p i) ih

lemma Sold.turn(p:Sold S A):Sold S (Turn A):=by obtain ⟨_,_,T⟩:=p; exact ⟨_,_,T.turn⟩

lemma Sold.der (p:Sold S A):Sold S (flicks S A):=by
 obtain ⟨n,c,T⟩:=p; exact ⟨_,_,paid_flick T⟩

open SatinJets

variable (S)
def scratches (n:ℕ)(A:Stamp X):Stamp X:= ((flicks S)^[n]) A
/-- literal time derivatives on singular field (no external spatial
or temporal translation in the jet's definition at this width). -/
def surfaces (P:Prism)(A:Stamp X): Stamp X:=
    ∑ i∈P.support, P i • scratches S (i+1) A


variable {S}
lemma succ_flick (n:ℕ): scratches S (n+1) A=flicks S (scratches S n A):=
 Function.iterate_succ_apply' ..

lemma Sold.scratched (p:Sold S A): ∀n, Sold S (scratches S n A)
| 0=>p
| n+1=>by rw [succ_flick]; exact Sold.der (Sold.scratched p n)
lemma Sold.surfaced (p:Sold S A)(P:Prism): Sold S (surfaces S P A):= Sold.sum _ _ fun _=>
   (p.scratched _).smul _

variable {Y':ℝ→X}(V: Positive S Y')(h:Sold S A)
  (b:∀ u v,0<u→0<v→ A u v Ω=Y' u)

include V h b
lemma scratched_vac:∀ i, Vac Ω (scratches S i A) (jet S Y' i)
| 0=> fun u v a c=>by
    rw [show scratches S 0 A=A from rfl,b u v a c,jet,iteratedDeriv_zero]
    exact (lifted_heat S Y' V a).symm
| i+1=>by
    rw [succ_flick,jet_up]
    obtain ⟨p,y,T⟩:= h.scratched i
    exact flick_vac Ω T (jet_analytic S Y' V i) (scratched_vac i)

lemma surfaced (P:Prism)(u v:ℝ)(a:0<u)(d:0<v):
    surfaces S P A u v Ω = prism S Y' P u:=by
    simp only [prism_ret,surfaces,Finset.sum_apply, Pi.smul_apply,
      sum_apply,smul_apply]
    exact Finset.sum_congr rfl fun _ _=> congrArg (_ • ·) (scratched_vac Ω V h b _ u v a d)

end YM.Quays

