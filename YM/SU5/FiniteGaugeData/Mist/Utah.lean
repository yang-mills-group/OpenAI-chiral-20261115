import YM.SU5.FiniteGaugeData.Mist.Kodiak
import YM.Heat.Duration
/-! # PVM diagnostics on the reconstructed translation clock
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
namespace Utah
variable {H V:Hilbert}{a:Axis}(P:OS.Semigroup H a)(Q:OS.Semigroup V a)
variable (A : H→L[ℂ] V)(p:∀ x:ℝ≥0,A.comp (P.E x) = (Q.E x).comp A)
open OS.Semigroup
include p
lemma acrossF (z:ℂ)(t:z∈inside): A.comp (P.F z) = (Q.F z).comp A:=by
 ext1 y; let g(z:ℂ):= A (P.F z y); let f(z:ℂ):= Q.F z (A y)
 have he:AnalyticOnNhd ℂ g inside:= fun z hz=> A.analyticAt _|>.comp ((ContinuousLinearMap.apply ℂ H.space y).analyticAt _|>.comp (P.localHeat z hz))
 have hu:AnalyticOnNhd ℂ f inside:= fun z hz=>(ContinuousLinearMap.apply ℂ V.space (A y)).analyticAt _|>.comp (Q.localHeat z hz)
 have ht(u:ℝ≥0)(v:0<u): g (OS.Semigroup.duration u)=f (OS.Semigroup.duration u):=by unfold f g; rw [P.roots_heat v,Q.roots_heat v]; exact DFunLike.congr_fun (p u) y
 have hx:Set.EqOn g f inside:= he.eqOn_of_preconnected_of_frequently_eq hu (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (z₀:=(OS.Semigroup.duration 1:ℂ)) (dur.mpr zero_lt_one) (by
    intro hn; have hp:Tendsto OS.Semigroup.duration (𝓝[>] (1:ℝ≥0)) (𝓝[≠] (OS.Semigroup.duration 1)):= by
       apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
       filter_upwards [self_mem_nhdsWithin] with i p; exact fun t=> (Set.mem_Ioi.mp p).ne' (Subtype.ext (Complex.ofReal_injective t))
    obtain ⟨i,t,q⟩:= ((hp.eventually hn).and self_mem_nhdsWithin).exists; exact t (ht _ (lt_trans zero_lt_one (Set.mem_Ioi.mp q))))
 exact hx t
lemma intervenes (x:ℝ): A.comp (P.edge x)=(Q.edge x).comp A:= by
 ext1 y; refine (P.whole 1).induction ?_ (isClosed_eq (ContinuousLinearMap.continuous (A.comp _)) (ContinuousLinearMap.continuous ((Q.edge x).comp A))) y
 rintro _ ⟨w,rfl⟩; change A (P.edge x (P.E 1 w))=Q.edge x (A (P.E 1 w)); rw [P.high,show A (P.E 1 w)=Q.E 1 (A w) from DFunLike.congr_fun (p 1) w,Q.high]; exact DFunLike.congr_fun (acrossF P Q A p _ (OS.Semigroup.length.mpr zero_lt_one)) w
omit p
open OS
abbrev Vac (x:ℝ)(b:Axis)(p:b ≠ a): OS.Cross a:= ⟨x • basis b,by change x*basis b a=0; simp [basis, Ne.symm p]⟩
lemma yup (u:OS.Cross a) : OS.Semigroup.SEP a u=u:=Subtype.ext (by change u.val-_•_=u.val; rw [show u.val a=0 from u.property, zero_smul, sub_zero])
lemma vacancy (x:OS.Cross a): P.unit.translation x.val=P.U x:= by unfold OS.Semigroup.unit; dsimp only; rw [yup,show x.val a=0 from x.property,P.birth]; rfl
lemma warmV (t:ℝ): P.unit.translation (t • basis a)=P.edge t:=by
 have ht : SEP a (t • basis a)=0 := Subtype.ext (show (t:ℝ) • basis a-_=_ by simp)
 unfold unit; simp [ht,P.uZero]
lemma unique (x:H.space): (∀ z:E4,P.unit.translation z x=x) ↔ (∀ z:ℝ,P.edge z x=x) ∧ (∀ b:Axis,∀ h:b≠a,∀ v:ℝ,P.U (Utah.Vac v b h) x=x) :=by
 constructor; · intro p; exact ⟨fun z=>warmV P z ▸ p _,fun _ h v=> (vacancy P (Utah.Vac v _ h)) ▸ p _⟩ -- ▸ direction check
 rintro ⟨t,p⟩ q; have ht(b:Axis):P.unit.translation (q b • basis b) x=x:=by
    by_cases h:b=a; · subst b; rw [warmV]; exact t _
    rw [show P.unit.translation (q b • basis b)=_ from vacancy P (Utah.Vac (q b) b h)]; exact p b h _
 have he(c:Finset Axis):P.unit.translation (∑ b∈ c, q b • basis b) x=x:=by induction c using Finset.induction with
    | empty=> rw [sum_empty,P.unit.origin]; rfl
    | insert i s v h=> rw [sum_insert v,← P.unit.sends,ContinuousLinearMap.comp_apply,h,ht]
 rw [show P.unit.translation q=P.unit.translation (∑ b:Axis,q b • basis b) from congrArg _ ?_]; exact he _
 ext i; simp [basis,Finset.sum_apply,Pi.single_apply] -- notation
end Utah
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
