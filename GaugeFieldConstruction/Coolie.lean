import GaugeFieldConstruction.Heliac
import YM.Push.RELAY_MARK.Wilson
/- echo variations without cut-tie assumptions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
local notation "GS"=>SU.group
open F03
open Push.Mark
variable (o:Site n) (q:Clip) (e:Axis) (f:PlaqAxes) (p:BudgetPoint)
-- State differentiable-to-one-flow. disjoint call suffices.
variable (X: G.Color)(g:Config G n→E)(F:Config G n)
lemma one_link(t:ℝ) : turnLink (o,e) X t F= increment F (t • at_E o e X):=by
 funext i; by_cases h:i=(o,e) <;> simp [h,RG.increment,at_E,turnLink, Function.update_of_ne]
lemma stared(h:ContDiffAt ℝ ω (g ∘ increment F) 0): HasDerivAt (fun t:ℝ=> g (turnLink (o,e) X t F)) (hue_T g F (at_E o e X)) 0:=by
 simp_rw [one_link]; exact Push.side (g ∘ increment F) (h.differentiableAt (by simp)) (at_E o e X)
lemma offsite(f:Face (Per n))(v:f∉ slab o)(t:ℝ): faceValue (turnLink (o,e) X t F) f= faceValue F f:=by
 refine face_local f _ _ ?_; intro i h _; exact turn_away _ _ _ (show i≠ (o,e) by intro p; rw [p] at h; exact v ((slab_q _).mpr h))
lemma dorm_read (A:Config SU.group n)(g:SU.group.Color):hue_T (ding_B (n:=n) q) A (at_E o e g)=hue_T (Dorm o q) A (at_E o e g):=by
 let E:=fun Z=> ∑ i∈ univ \ slab o, Score q (Z:Config SU.group n) i
 let Q:= ding_B (n:=n) q; let V:= Dorm o q; let P(t:ℝ):=turnLink (o,e) g t A; have he(t):Q (P t)= E A+V (P t):=by
    rw [show E A= E (P t) from ?_]; exact (sum_sdiff (f:=Score q (P t)) (subset_univ _)).symm -- name
    apply sum_congr rfl; intro i h; apply congrArg (coinF q); exact (offsite o e g A i (mem_sdiff.mp h|>.2) t).symm
 apply HasDerivAt.unique (stared o e g Q A (ding_π ..)); change HasDerivAt (fun t=> Q (P t)) _ _; simp_rw [he]; exact (stared o e g V A (dorm_π o A q)).const_add _
lemma turn_open : IsClosed {F:Config G n| flags t F=∅}:=by
 let Q:=fun i:Face (Per n)=> {F:Config G n| faire G F i≤t}; rw [show {F:Config G n|flags t F=∅}= ⋂ i:Face (Per n),Q i from ?_]; apply isClosed_iInter; intro i; exact isClosed_le ((G.continuous_chord).comp (continuous_travel ..)) continuous_const -- name
 ext A; simp only [Set.mem_setOf_eq,Set.mem_iInter]; constructor
 · intro h i; by_contra l; have hp: t< G.chord (faceValue A i):= lt_of_not_ge l; have hz: i.1∈ flags t A:= (flags_spec ..).mpr ⟨_,anchor_visit _,hp⟩; simp [h] at hz
 intro h; rw [eq_empty_iff_forall_notMem]; intro x k; obtain ⟨i,g,v⟩:= (flags_spec ..).mp k; exact (h i : faire G A i ≤ t).not_gt v
lemma sooty (A:Config G n)(i:Face (Per n))(h:flags t A=∅):faire G A i≤t:=by
 by_contra l; have hp: t< G.chord (faceValue A i):= lt_of_not_ge l; have ht:i.1 ∈ flags t A:= (flags_spec ..).mpr ⟨_,anchor_visit _,hp⟩; rw [h] at ht; exact notMem_empty _ ht
lemma turn_see (i:Edge (Site n)) : Continuous (fun t:ℝ=> turnLink i X t F):=by
 apply continuous_pi; intro j; by_cases h:j=i; subst j; simp_rw [turn_here]; fun_prop
 simp_rw [turn_away F X _ h]; exact continuous_const
lemma hotel_tie (t:0<r)(i:Face (Per n))(h:i ∈ slab o)(f:Config G n)(w:faire G f i=r) : Turret o r f=0∧fderiv ℝ (Turret o r ∘ increment f) 0=0:=by
 let k(q:Config G n):= 1-(faire G q i^2/r^2)^2; have hz: k f=0:=by unfold k; rw [w,div_self]; simp; positivity
 let y(q:Config G n):=∏ j∈(slab o).erase i, TestVe r j q; have hp: Turret o r=fun x=> k x^2*y x:=funext fun x=> (mul_prod_erase (slab o) (fun i=> TestVe r i x) h).symm -- tune
 let S:= k∘ increment f; have hx: S 0=0:=by change k (RG.increment f 0)=_; rw [G07.at_zero_increment]; exact hz
 have hk:ContDiffAt ℝ ω S 0:=by unfold S k Function.comp faire; simp_rw [G.chord_price]; exact contDiffAt_const.sub ((contDiffAt_const.mul (price_smooth (mat_face_inc i f).contDiffAt)).div_const _|>.pow 2)
 have hv(s':Finset (Face (Per n))):ContDiffAt ℝ ω (fun x=>∏ j∈s', TestVe r j (increment f x)) 0:=by induction s' using Finset.induction_on with | empty=> simp only [prod_empty]; exact contDiffAt_const| @insert i u v ih=> simp_rw [prod_insert v]; exact (lineTur f r i).mul ih
 have he:= ((hk.differentiableAt (by simp)).hasFDerivAt.pow 2).mul ((show ContDiffAt ℝ ω (y ∘ increment f) 0 from hv _).differentiableAt (by simp)|>.hasFDerivAt); simp [hx] at he -- tune
 rw [hp]; exact ⟨by change k f^2 * _=0; rw [hz]; ring, he.fderiv⟩
lemma turn_rise (x:ℝ) (p:flags x F=∅)(q:∀ i∈slab o,faire G F i<x): ∀ᶠ t:ℝ in 𝓝 0,flags x (turnLink (o,e) X t F)=∅:=by
 let f(i:tandem G n):True:=True.intro -- not function type?
 let V(t:ℝ):=turnLink (o,e) X t F; have hp(i): ∀ᶠ s:ℝ in 𝓝 0, faire G (V s) i ≤ x:=by
    by_cases h:i∈slab o
    · have hk:Continuous (fun t:ℝ=>faire G (V t) i):= G.continuous_chord.comp ((continuous_travel ..).comp (turn_see X F _)); exact (hk.continuousAt.eventually (gt_mem_nhds (by change faire G (V 0) i<x; unfold V; rw [turn_zero]; exact q i h))).mono fun i h=> LT.lt.le h
    exact Eventually.of_forall fun i'=> by unfold V faire; rw [offsite o e X F i h i']; exact sooty _ _ p
 refine (eventually_all.mpr hp).mono (fun t p=> eq_empty_iff_forall_notMem.mpr ?_); intro z h; obtain ⟨i,w,g⟩:= (flags_spec ..).mp h; exact (p i).not_gt g
lemma coatI (f:ℝ→E)(h:Set ℝ)(v: HasDerivAt f 0 0)(x:f 0=0): HasDerivAt (h.indicator f) 0 0:=by
 rw [hasDerivAt_iff_tendsto_slope] at *
 -- norm squeeze
 have hz: h.indicator f 0=0:=by by_cases p:(0:ℝ)∈h<;> simp [p,x]
 apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' _ ?_ (tendsto_zero_iff_norm_tendsto_zero.mp v) -- name
 · exact Eventually.of_forall fun _=>norm_nonneg _
 refine Eventually.of_forall fun t=>?_ ; simp only [Function.comp_apply,slope_def_module,x,hz,sub_zero, Set.indicator]; split_ifs <;> simp
lemma blanket (x:ℝ)(h:HasDerivAt (fun t:ℝ=> g (turnLink (o,e) X t F)) (0:E) 0) (v:g F=0): HasDerivAt (fun t:ℝ=> Set.indicator {F:Config G n| flags x F=∅} g (turnLink (o,e) X t F)) 0 0:=by
 let S:= {F: Config G n| flags x F=∅}; let V(t:ℝ):=turnLink (o,e) X t F; refine (coatI (g ∘ V) (V ⁻¹' S) h (by simp [V,v])).congr_of_eventuallyEq (Eventually.of_forall fun t=> ?_); by_cases ht: V t∈ S
 · exact (Set.indicator_of_mem ht _).trans (Set.indicator_of_mem (show t∈V ⁻¹' S from ht) (g ∘ V)).symm
 exact (Set.indicator_of_notMem ht _).trans (Set.indicator_of_notMem (show t∉V ⁻¹' S from ht) (g ∘ V)).symm
-- absolute.Mark integral linear and Q vector.Domain in finite torus
variable (T:Config G n→ E)[MeasurableSpace E][BorelSpace E][CompleteSpace E][SecondCountableTopology E]
lemma trPref (m:ℝ)(h:∀ x:Config G n, HasDerivAt (fun t:ℝ=>g (turnLink (o,e) X t x)) (T x) 0)(hp:Envelope g)(vp: Envelope T) : (∫ x:Config G n,T x∂prior G n)=0:=by
 let μ:=prior G n; let f(t:ℝ)(x:Config G n):= g (turnLink (o,e) X t x); let H(t:ℝ)(x:Config G n):= T (turnLink (o,e) X t x)
 obtain ⟨C,W⟩:=vp.cost; have hr (t:ℝ):MeasurePreserving (turnLink (G:=G) (o,e) X t) μ μ:=turn_preserving (o,e) X t
 have hs(t:ℝ)(x:Config G n): HasDerivAt (fun s:ℝ=> f s x) (H t x) t:=by
    let F:=turnLink (o,e) X t x; have hp: HasDerivAt (fun s:ℝ=> s-t) 1 t:= by simpa using (hasDerivAt_id' t|>.sub_const t)
    have hx(s:ℝ):turnLink (o,e) X (s-t) F=turnLink (o,e) X s x:=by rw [← turn_add, sub_add_cancel]
    simpa only [Function.comp_def,hx,one_smul] using (show HasDerivAt (fun s:ℝ=> g (turnLink (o,e) X s F)) (T F) (t-t) from sub_self t|>.symm ▸ h F).scomp (h:=fun i=>i-t) t hp
 have ht:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=f) (F':=H) (μ:=μ) (x₀:=(0:ℝ)) (bound:=fun _=>C) (s:=Set.univ) univ_mem (Eventually.of_forall fun t=> (hp.meas.comp (hr t).measurable).aestronglyMeasurable) (?_ ) (by rw [show H 0=T from funext fun u=> by simp [H]]; exact vp.meas.aestronglyMeasurable) (Eventually.of_forall fun i t _=>W _) (integrable_const _) (Eventually.of_forall fun i t _=> hs t i)).2
 swap; · rw [show f 0=g from funext fun u=> by simp [f]]; exact Push.SectorMeasure.Env.integrableX hp _ -- tune
 have hw(t:ℝ): MeasurableEmbedding (turnLink (o,e) X t):=by
    rw [show turnLink (o,e) X t= ⇑(Homeomorph.mulLeft (turnLink (o,e) X t 1)) from ?_]; exact (Homeomorph.mulLeft _).measurableEmbedding
    funext U i; change _=turnLink (o,e) X t 1 i*U i; by_cases p:i=(o,e) <;> simp [p,turnLink,Function.update_of_ne]
 have he(t): (∫ x:Config G n,f t x∂μ)=∫ x,g x∂μ:= (hr t).integral_comp (hw t) g
 simp_rw [he,show H 0=T from funext fun i=> by simp [H]] at ht; exact ht.unique (hasDerivAt_const ..)
end Shield
end YM.CF.XGarden
end
