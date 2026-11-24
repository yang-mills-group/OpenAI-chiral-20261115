/- This file incorporates modified third-party source. See the source attributions in notices/. -/ 
import SatinPP.Silk
import YM.SU5.Macro.Across

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace


/-- Punctured Wick region including the seam. -/
abbrev sheath:Set ℂ:={z|0 ≤ z.re ∧ z≠0}
lemma inside_subset_sheath: inside ⊆ sheath:=fun z h=>
   ⟨(show (0:ℝ)<z.re from h).le,by intro v; subst z; exact lt_irrefl (0:ℝ) h⟩

structure Harbor {V: Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (f:ℂ→V) : Prop where
  keep : ContinuousOn f sheath
  free : AnalyticOnNhd ℂ f inside

namespace Harbor
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {f g:ℂ→V}{a:ℂ→ℂ}
lemma const (v:V): Harbor (fun _=>v):=⟨continuousOn_const,analyticOnNhd_const⟩
lemma add (F:Harbor f)(G:Harbor g):Harbor (fun z=>f z+g z):= ⟨F.keep.add G.keep,F.free.add G.free⟩
lemma sub (F:Harbor f)(G:Harbor g):Harbor (fun z=>f z-g z):=⟨F.keep.sub G.keep,F.free.sub G.free⟩
lemma smul (A:Harbor a)(G:Harbor g): Harbor (fun z=>a z • g z):=⟨A.keep.smul G.keep,A.free.smul G.free⟩
lemma pass (F:Harbor f)(T:V→L[ℂ] W):Harbor (fun z=> T (f z)):=⟨ T.continuous.comp_continuousOn F.keep,
 fun z h=> (T.analyticAt _).comp (F.free z h)⟩
lemma use (F:Harbor f) (c:EqOn g f sheath) : Harbor g:=
 ⟨F.keep.congr c,F.free.congr open_inside (c.symm.mono inside_subset_sheath)⟩
lemma tInv:Harbor (fun z=>z⁻¹):= ⟨continuousOn_id.inv₀ (fun _ h=>h.2), analyticOnNhd_id.inv (fun z h=>(inside_subset_sheath h).2)⟩
end Harbor

variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)

attribute [local instance] Measure.Subtype.measureSpace in
theorem harbor_integral {K : Set E4} (hK : IsCompact K) (B : ℂ → E4 → H)
    (hc : ContinuousOn (uncurry B) (sheath ×ˢ K))
    (hp : ∀ p ∈ K, DifferentiableOn ℂ (fun z => B z p) inside) :
    Harbor (fun z => ∫ p in K, B z p) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : IsFiniteMeasure (volume : Measure K) :=
    ⟨by rw [Measure.Subtype.volume_univ hK.isClosed.measurableSet.nullMeasurableSet]
        exact hK.measure_lt_top⟩
  let D (z : ℂ) := ContinuousMap.mkD (K.restrict (B z)) (0 : C(K,H.space))
  have he (z) (hz : z ∈ sheath) : ContinuousOn (B z) K :=
    hc.comp (Continuous.prodMk_right z).continuousOn fun _ hw => ⟨hz, hw⟩
  have hD (z) (hz : z ∈ sheath) (p : K) : D z p = B z p := by
    dsimp only [D]
    rw [ContinuousMap.mkD_of_continuousOn (he z hz)]; rfl
  let P (p : K×H.space) := (innerSL ℂ p.2).comp
      (ContinuousMap.evalCLM ℂ p.1 : C(K,H.space) →L[ℂ] H)
  have hDc : ContinuousOn D sheath :=
    ContinuousMap.continuousOn_mkD_restrict_of_uncurry B 0 hc


  have hF : Harbor D := by
    refine ⟨hDc,Analysis.lift_weak (Set.range P) ?_ open_inside (hDc.mono inside_subset_sheath) ?_⟩
    · intro f g h; refine ContinuousMap.ext fun i => ext_inner_left ℂ fun x=>h (P (i,x)) (mem_range_self _)
    rintro _ ⟨⟨p,x⟩,rfl⟩
    have t:DifferentiableOn ℂ (fun z=>D z p) inside:=(hp p p.2).congr (fun z hz=>hD z (inside_subset_sheath hz) p)
    exact (innerSL ℂ x).differentiable.comp_differentiableOn t
  have hl (f : C(K,H.space)) : Integrable f :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let A : C(K,H.space) →ₗ[ℂ] H :=
    { toFun := fun f => ∫ p, f p
      map_add' := fun f g => integral_add (hl f) (hl g)
      map_smul' := fun a f => integral_smul a (fun p => f p) }
  let E := LinearMap.mkContinuous A ((volume : Measure K).real univ) (fun f => by
    rw [mul_comm]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun p => f.norm_coe_le_norm p))
  apply (hF.pass E).use
  intro z hz
  change _ =(∫ p : K, D z p)
  simp_rw [hD z hz]
  exact (integral_subtype hK.isClosed.measurableSet _).symm



local notation "Dn"=> {z:ℂ| z.im<0}
local notation "Seam"=> {z:ℂ| z.im≤0 ∧ z≠0}
lemma vanish_seam {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
    {f:ℂ→X} (F:Harbor f) {a b:ℝ}(ha:0≤a)(hab:a<b)
    (w:∀ t∈Ioo a b,f (sideways t)=0):
    EqOn f (fun _=>0) sheath:=by
  let g(z:ℂ):= f (I*z)
  have imI (z:ℂ): (I*z).re= -z.im:= by simp
  have G:AnalyticOnNhd ℂ g Dn:= F.free.comp (analyticOnNhd_const.mul analyticOnNhd_id)
      (fun z h=>show 0<(I*z).re by rw [imI];exact neg_pos.mpr h)
  have C:ContinuousOn g Seam:=F.keep.comp ((continuousOn_const.mul continuousOn_id))
      (fun z h=> ⟨by rw [imI]; exact neg_nonneg.mpr h.1,mul_ne_zero I_ne_zero h.2⟩)
  let T := {z:ℂ| z.re∈Ioo (-b) (-a)}
  let k(z:ℂ):=if z.im<0 then g z else 0
  have hD : IsOpen T:=isOpen_Ioo.preimage continuous_re
  have hup:IsOpen {z:ℂ|0<z.im}:=isOpen_lt continuous_const continuous_im
  have hdn:IsOpen Dn:=isOpen_lt continuous_im continuous_const

  have Tz : ∀z∈T,z≠0:=by
    intro z h t; have e: z.re< -a:=h.2; subst z; rw [zero_re] at e;linarith
  have hk : ContinuousOn k T := by
    apply ContinuousOn.if
    · intro z hz
      have p: z.im=0 := (show z ∈ { z : ℂ | z.im = 0 } from frontier_setOf_im_lt 0 ▸ hz.2)
      change f _=0
      rw [show I*z=sideways (-z.re) from Complex.ext (by simp [sideways,p]) (by simp [sideways])]
      exact w _ ⟨lt_neg.mpr hz.1.2,neg_lt.mpr hz.1.1⟩
    · rw [closure_setOf_im_lt]; exact C.mono (fun z h=>⟨h.2,Tz z h.1⟩)
    exact continuousOn_const
  have hf (z : ℂ) (t : 0 < z.im) : (fun _=> (0:X)) =ᶠ[𝓝 z] k := (show ∀ᶠ x : ℂ in 𝓝 z, 0 < x.im from hup.mem_nhds t).mono
    (fun _ (q : 0 < _)=> (if_neg q.asymm).symm)
  have hg (z : ℂ) (t : z.im < 0) : g =ᶠ[𝓝 z] k := (show ∀ᶠ x : ℂ in 𝓝 z, x.im < 0 from hdn.mem_nhds t).mono
    (fun _ (q : _ < 0)=> (if_pos q).symm)


  have hd : AnalyticOnNhd ℂ k T := by
    apply YM.SatinMacro.Glue.analyticOnNhd_of_off hD hk
    intro z e t
    rcases lt_or_gt_of_ne t with t|t
    · exact ((G z t).congr (hg z t)).differentiableAt
    exact (analyticAt_const.congr (hf z t)).differentiableAt
  have ht : Convex ℝ T := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  obtain ⟨x,hx,j⟩ := exists_between (neg_lt_neg hab)
  have v:= hd.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const ht.isPreconnected
     (show Complex.mk x 1 ∈ T from ⟨hx,j⟩) (hf _ zero_lt_one |>.symm)
  have he : Complex.mk x (-1) ∈ T := ⟨hx,j⟩
  have i: Complex.mk x (-1)∈Dn:= (neg_one_lt_zero (R:=ℝ))
  have h:= G.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
     (convex_halfSpace_im_lt 0).isPreconnected i
     ((hg _ i).trans (v.eventuallyEq_of_mem (hD.mem_nhds he)))
  have h' := h.of_subset_closure C continuousOn_const (fun z (p:z.im<0)=>⟨p.le,fun t=>lt_irrefl _ (zero_im ▸ (t ▸ p))⟩) (by rw [closure_setOf_im_lt]; exact fun z t=>t.1)
  intro z hz
  specialize h' (x:=-I*z) ⟨by simp [hz.1],mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz.2⟩
  unfold g at h'; rw [←mul_assoc,mul_neg,I_mul_I,neg_neg,one_mul] at h'
  exact h'


-- Ω
def tide (z:ℂ): H.Op:=S.edge (-z.im)*S.E z.re.toNNReal
lemma tide_c {X:Type*}[TopologicalSpace X]{f:X→ℂ}{g:X→H}
 (hf:Continuous f)(hg:Continuous g):Continuous (fun z=>tide S (f z) (g z)):= by
 apply S.cont_edge (fun z=> S.E (f z).re.toNNReal (g z)) (fun z=>-(f z).im) _ (continuous_im.comp hf).neg
 exact (duet S).comp (hg.prodMk ((continuous_real_toNNReal.comp continuous_re).comp hf))
lemma tide_norm (z:ℂ)(x:H):‖tide S z x‖≤‖x‖:=
   (S.life ..).trans_le (stayPay S x z.re)
lemma tide_heat (z:ℂ)(p:z∈inside): tide S z = S.F z:=by
 unfold tide; have h:0<z.re.toNNReal:=Real.toNNReal_pos.mpr p
 rw [← S.roots_heat h]
 refine Eq.trans (S.along (dur.mpr h) _) ?_
 have l:0≤z.re:=(Real.toNNReal_pos.mp h).le
 congr 1; apply Complex.ext <;> simp [duration,sideways,l]
lemma tide_edge (t:ℝ): tide S (sideways t) = S.edge t:=by
 simp [tide,sideways,S.eZero,show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl]


abbrev infer (z:ℂ)(c:ℝ):ℂ:= c*z
lemma infer_warm {z:ℂ}(p:z∈inside){c:ℝ}(h:0<c):infer z c∈inside:=by
  change 0<(infer z c).re; simp [infer]; exact mul_pos h p
lemma tide_hol: AnalyticOnNhd ℂ (tide S) inside :=
    S.localHeat.congr open_inside (fun z p=>(tide_heat S z p).symm)
lemma tide_analytic (c:ℝ)(h:0<c):AnalyticOnNhd ℂ (fun z=>tide S (infer z c)) inside :=
 (tide_hol S).comp (analyticOnNhd_const.mul analyticOnNhd_id) fun _ p=>infer_warm p h

abbrev Q (p:E4):= S.U (SEP a p)
lemma Q_join {K:Type*}[TopologicalSpace K]{p:K→E4}{y:K→H}(h:Continuous p)(r:Continuous y):
    Continuous (fun t=>Q S (p t) (y t)):= S.cont_cross y (SEP a ∘ p) r ((SEP a).continuous.comp h)

variable (l u:ℝ)(A:H.Op)
abbrev fore (a:Axis)(l:ℝ)(p:E4):ℝ:= p a-l
abbrev aft (a:Axis)(u:ℝ)(p:E4):ℝ:=u-p a
def entry (z:ℂ)(p:E4): H.Op:=
 tide S (infer z (fore a l p))*Q S p*A*Q S (-p)*tide S (infer z (aft a u p))


lemma entry_val (z:ℂ)(p:E4)(x:H) :
 entry S l u A z p x=tide S (infer z (fore a l p)) (Q S p (A (Q S (-p) (tide S (infer z (aft a u p)) x)))):=rfl
lemma entry_cost (z:ℂ)(p:E4)(x:H): ‖entry S l u A z p x‖≤‖A‖ * ‖x‖:=by
 rw [entry_val]
 refine (tide_norm ..).trans ?_
 rw [show ∀ x, ‖Q S p x‖=‖x‖ from S.unitary _]
 refine (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
 rw [show ∀ x, ‖Q S (-p) x‖=‖x‖ from S.unitary _]
 exact tide_norm ..
lemma entry_join {K:Type*}[TopologicalSpace K]{p:K→E4}{Z:K→ℂ}{y:K→H}
 (c:Continuous p)(z:Continuous Z)(h:Continuous y):
 Continuous (fun t=>entry S l u A (Z t) (p t) (y t)):=by
 have qc:Continuous (fun t=>p t a):=by fun_prop
 simp_rw [entry_val]
 refine tide_c S ?_ (Q_join S c (A.continuous.comp (Q_join S c.neg (tide_c S ?_ h)))) <;>
    (unfold infer; first| unfold fore | unfold aft) <;>fun_prop


variable (g:Test4)(z:ℂ)
local notation "I_" => entry S l u A
local notation "Arc" x:max => fun p:E4=> g p • I_ z p x
lemma coatP (p:E4)(x:H) : ‖g p • I_ z p x‖≤‖g p‖*(‖A‖*‖x‖):=
 (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (entry_cost ..) (norm_nonneg _))
lemma coatI (x:H) : Integrable (Arc x):=
 (g.integrable.norm.mul_const (‖A‖*‖x‖)).mono'
  (g.continuous.smul (entry_join S l u A continuous_id' continuous_const continuous_const)).aestronglyMeasurable
  (Eventually.of_forall (fun p=>coatP S l u A g z p x))
lemma coatL (x:H) : ‖∫ p,g p • I_ z p x‖≤ vial g * ‖A‖ * ‖x‖:=by
 rw [mul_assoc,vmeets,←integral_mul_const]; exact norm_integral_le_of_norm_le (g.integrable.norm.mul_const _)
    (Eventually.of_forall fun p=> coatP S l u A g z p x)
def coat : H.Op:= LinearMap.mkContinuous (σ:=RingHom.id ℂ) {
 toFun x:=∫ p,g p • I_ z p x
 map_add' x y:=by simp only [map_add,smul_add]; exact integral_add (coatI ..) (coatI ..)
 map_smul' b v:= by simp_rw [map_smul,smul_comm _ b]; rw [integral_smul]; rfl } (vial g*‖A‖) (fun x=> coatL S l u A g z x)
lemma coat_val(x:H) : coat S l u A g z x = ∫ p,g p • I_ z p x:=rfl


lemma coat_norm: ‖coat S l u A g z‖ ≤ vial g * ‖A‖:=ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (coatL S l u A g z)

structure Band(a:Axis)(l u:ℝ)(g:Test4):Prop where
 wide: HasCompactSupport g
 snug: ∀ p ∈ tsupport g, l<p a ∧ p a<u

variable {g}
lemma coat_harbor (r:Band a l u g){y:ℂ→H}(h:Harbor y):
   Harbor (fun z=>coat S l u A g z (y z)):=by
 let B(z:ℂ)(p:E4):= g p • I_ z p (y z)
 apply Harbor.use (g:=fun z=>coat S l u A g z (y z)) (harbor_integral r.wide B ?c ?h)
 · intro z e; symm; exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun p t=>
      show g p • I_ z p (y z)=0 by rw [image_eq_zero_of_notMem_tsupport t,zero_smul])
 case c=>
   change ContinuousOn (fun t:ℂ×E4=> g t.2 • I_ t.1 t.2 (y t.1)) _
   refine (show ContinuousOn (fun t:ℂ×E4=>g t.2) (sheath ×ˢ tsupport g) from (g.continuous.comp continuous_snd).continuousOn).smul ?_
   have f: ContinuousOn (fun t:ℂ×E4=>y t.1) (sheath ×ˢ tsupport ⇑g):=h.keep.comp continuous_fst.continuousOn (fun _ t=>t.1)
   have e:Continuous (fun t:(H.space × ℂ)×E4=> I_ t.1.2 t.2 t.1.1):=entry_join S l u A
       continuous_snd (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_fst)
   have hh:= e.comp_continuousOn ((f.prodMk continuous_fst.continuousOn).prodMk continuous_snd.continuousOn)
   exact hh
 case h=>
   intro p t
   obtain ⟨t₁,t₂⟩:=r.snug p t
   have v:AnalyticOnNhd ℂ (fun z=>I_ z p) inside:=
      (((((tide_analytic S _ (sub_pos.mpr t₁)).mul (analyticOnNhd_const (v:=Q S p))).mul (analyticOnNhd_const (v:=A))).mul
         (analyticOnNhd_const (v:=Q S (-p)))).mul (tide_analytic S _ (sub_pos.mpr t₂)))
   intro z d
   exact (differentiableAt_const _
      |>.smul ((v z d).differentiableAt.clm_apply (h.free z d).differentiableAt)).differentiableWithinAt

#print axioms coat_harbor
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

