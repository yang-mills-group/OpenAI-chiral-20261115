import YM.CF.BPress.Port.Ride
/-! Pull stack F. Measurability preserving L^1 exact. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(κ y:ℝ)(S:Seal X.Hcols)
def coast (x:Quarters X):= coordinate X x.1 (ratev X J y S)
def coastV (x:Quarters X):= coordinate X x.1 (fun _=>vcost B.D y)
lemma read_harbour (p:0<y)(r:LocalRatio J) : carriage X J y S= (harbour X).withDensity (ENNReal.ofReal ∘ coast X J y S):= cm X J y S p r
lemma read_volts : knell X y= (harbour X).withDensity (ENNReal.ofReal ∘ coastV X y):= km X y
lemma coast_meas (u:LocalRatio J): Measurable (coast X J y S):= Finset.measurable_fun_prod _ fun i _=> (show Measurable (ratev X J y S i) from by unfold ratev; split; exact v_meas ..; exact billH_meas B.D J y u).comp ((measurable_pi_apply i).comp measurable_fst)
lemma coast_pos (p:0<y)(u:LocalRatio J)(x): 0≤ coast X J y S x:=prod_nonneg fun i _=> rate_nn X J y S p u _ _
lemma volts_meas : Measurable (coastV X y):= Finset.measurable_fun_prod _ fun i _=> (v_meas B.D y).comp ((measurable_pi_apply i).comp measurable_fst)
lemma volts_pos (x): 0 ≤ coastV X y x:=prod_nonneg fun i _=>v_nonneg B.D y _
variable {F: Fare X}
variable {X}{u l:ℝ}{r k:ℕ}(P:Summer X F u l r k)
def wheel (e : BEnd X)(x:Quarters X): Quarters X:=(wjson e x.1,x.2)
def wheelE : Quarters X ≃ᵐ Quarters X:= MeasurableEquiv.prodCongr ((offer X).symm.trans ((swung P S).toHomeomorph.toMeasurableEquiv.trans (offer X))) (MeasurableEquiv.refl _)
lemma wheel_move : ⇑(wheelE S P)=wheel (F S):=rfl
@[fun_prop] lemma wheel_meas (A:BEnd X): Measurable (wheel A):= ((wjson_meas A).comp measurable_fst).prodMk measurable_snd
lemma log_move : MeasurePreserving (wheelE S P) (ENNReal.ofReal (detM X (F S)) • harbour X) (harbour X):=by
 let a:=(offer X).symm.trans ((swung P S).toHomeomorph.toMeasurableEquiv.trans (offer X)); let L:=detM X (F S); let b := ENNReal.ofReal L; let g:=(swung P S).toHomeomorph.toMeasurableEquiv; have hp:=P.root_pos S; have he:MeasurePreserving g (b • volume) volume:=by
    refine ⟨g.measurable,?_ ⟩; rw [Measure.map_smul,show ⇑g=(F S).toLinearMap from rfl, Measure.map_linearMap_addHaar_eq_smul_addHaar _ (show detM X (F S)≠0 from hp.ne')]; rw [smul_smul,abs_of_pos (inv_pos.mpr (show 0 < LinearMap.det (F S).toLinearMap from hp)), show LinearMap.det (F S).toLinearMap=detM X (F S) from rfl, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne',ENNReal.ofReal_one,one_smul] -- tune
 have hu: MeasurePreserving a (b • volume) volume := ((offers X).comp he).comp ((offers X).symm.smul_measure b); unfold harbour; rw [← Measure.prod_smul_left]; haveI: SigmaFinite (volume:Measure (Fills X)):=by rw [volume_pi]; infer_instance
 exact hu.prod (MeasurePreserving.id (Rains X)) -- tune
section formula
variable {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma duty_eq {X:Type*}[MeasurableSpace X](h:X→ℝ)(p:Measurable h)(u:∀ x,0≤ h x)(μ:Measure X)(f:X→E) : (∫ x, f x ∂(μ.withDensity (ENNReal.ofReal ∘ h)))=∫ x,h x • f x ∂μ:=by
 simp only [Function.comp_def]; rw [integral_withDensity_eq_integral_toReal_smul p.ennreal_ofReal (.of_forall fun x=> ENNReal.ofReal_lt_top)]; apply integral_congr_ae; filter_upwards with x; rw [ENNReal.toReal_ofReal (u x)]
lemma duty_int {X:Type*}[MeasurableSpace X](h:X→ℝ)(p:Measurable h)(u:∀ x,0 ≤ h x)(μ:Measure X)(f:X→E): Integrable f (μ.withDensity (ENNReal.ofReal ∘ h)) ↔ Integrable (fun x=>h x • f x) μ:=by
 simp only [Function.comp_def]; rw [integrable_withDensity_iff_integrable_smul' p.ennreal_ofReal (.of_forall fun x=>ENNReal.ofReal_lt_top)]; simp_rw [ENNReal.toReal_ofReal (u _)]
-- integrand assumed localized by THIS S.
variable (f:Offers X→E) {T:Sheet.Atlas}{A:Weave.Budget}(u':LocalRatio J)(h:Afford J T A B.D κ y)
def packRead := f ∘ uncurry (issueT X y S) ∘ wheel (F S)
include h P u'
lemma rollMove (v: Integrable f (Rains X))(e:StronglyMeasurable f)(p:∀ x, f x ≠ 0 → S=pick X κ y x):
 let g(x):= coast X J y S (wheel (F S) x) • packRead (F:=F) y S f x
 Integrable g (harbour X) ∧ (∫ x, f x ∂ Rains X)=detM X (F S) • ∫ x,g x ∂harbour X:=by
 intro g; let d:= court X J y S; let s:=voyage_mp X J y S h.young u'; let D:= carriage X J y S; let R:=uncurry (issueT X y S); let Q:= f ∘ R; let L:= fun x=> coast X J y S x • Q x; let C:= detM X (F S); have hc:=P.root_pos S; have ht : ∀ x, f x≠0→ x∈d:= by intro x n i _; unfold sail; split; trivial; next t=> apply h.cover u' _ i; rwa [← p x n]
 have hh : (∫ x, f x ∂Rains X)=∫ x,f x ∂((Rains X).restrict d):= (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x v=> not_not.mp (fun e=> v (ht x e)))).symm; have hm:= read_harbour X J y S h.young u'; have hv:Integrable Q D:= s.integrable_comp_of_integrable v.integrableOn
 have hi : Integrable L (harbour X):= (duty_int (coast X J y S) (coast_meas X J y S u') (coast_pos X J y S h.young u') _ Q).1 (hm ▸ hv); let φ:=wheelE S P; let he:= log_move S P
 have hx: (∫ x,f x ∂((Rains X).restrict d))=∫ x,L x ∂harbour X:= calc _ = ∫ x,Q x ∂ carriage X J y S:=by rw [← s.map_eq]; exact integral_map s.aemeasurable e.aestronglyMeasurable
                                                                        _ = _:=by rw [hm,duty_eq (coast X J y S) (coast_meas X J y S u') (coast_pos X J y S h.young u')]
 have hg : g=L ∘ φ:= rfl; rw [hg]; refine ⟨(integrable_smul_measure (by exact ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top).1 (he.integrable_comp_of_integrable hi), hh.trans (hx.trans ?_)⟩; rw [← he.integral_comp' L, integral_smul_measure, ENNReal.toReal_ofReal hc.le]; rfl
end formula
end YM.CF.BPress.Port
