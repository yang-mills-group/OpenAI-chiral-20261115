import YM.CF.BPress.Port.Orbit
/-!
One column chart release with right edges issued `A*exp W`. Applies measure-preserving changes to bring gaussian scaled Pack, before override; same W logs as in action when admitted. Log weights globally measured with support condition. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Set
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
lemma payoff_mp {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]{μ:Measure X}{ν:Measure Y}(f:Y→ℝ≥0∞)(φ:X→Y)(h:MeasurePreserving φ μ ν)(u:Measurable f) : MeasurePreserving φ (μ.withDensity (f ∘ φ)) (ν.withDensity f):=by
 refine ⟨h.measurable,Measure.ext fun i v=>?_⟩; rw [Measure.map_apply h.measurable v,withDensity_apply,withDensity_apply,←h.map_eq,setLIntegral_map v u h.measurable]; rfl; exact v; exact h.measurable v
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(y:ℝ)
def bMag : Market D:=fun i=>magnetH y i.2
def pullCover (D:ℕ)(J:ChartRatio group)(y:ℝ): Set (Market D):= (Homeomorph.mulLeft (bMag D y)) '' (covered J (1:Market D))
def rosin (v:Strings D) (i:Hub D) := bMag D y i * group.lieExp (v i)
@[simp] lemma rosin_eq (v:Strings D): rosin D y v= (Homeomorph.mulLeft (bMag D y)) (release 1 v):=by ext1 i; change _ = bMag D y i *(_*(1:Market D) i); simp [rosin]
lemma pull_cover (u: LocalRatio J): MeasurableSet (pullCover D J y):= ((Homeomorph.mulLeft _).isOpenMap _ (covered_isOpen u _)).measurableSet
lemma rosin_cover (u: LocalRatio J){x:Strings D}(p:x∈ mouth J): rosin D y x∈pullCover D J y:=by rw [rosin_eq]; exact ⟨_,(release_image J (1:Market D)) ▸ mem_image_of_mem _ p,rfl⟩ -- tune orientation
lemma rosin_mp (u:LocalRatio J) : MeasurePreserving (rosin D y) (logMeasure J (Hub D)) ((Rainy D).restrict (pullCover D J y)):=by
 let P:=Rainy D; let U:=covered J (1:Market D); let A:= (Homeomorph.mulLeft (bMag D y)).toMeasurableEquiv; have H:MeasurePreserving A P P:= measurePreserving_pi _ _ (fun i:Hub D=> measurePreserving_mul_left group.probHaar (bMag D y i)); have ht:MeasurePreserving A (P.restrict U) (P.restrict (A '' U)):= by
   let h:= A.restrict_map P (A '' U); rw [H.map_eq,A.injective.preimage_image] at h; exact ⟨A.measurable,h.symm⟩
 rw [funext (rosin_eq D y)]; exact ht.comp (array_release u 1)
-- compose with scaled Lie chart in full Pack
abbrev portDim (D:ℕ) := n_ang D
def hew (v:Pack D): Strings D:= colorsT D (g y • v)
def rose (v:Pack D): Market D:= rosin D y (hew D y v)
def mouthP:= hew D y ⁻¹' mouth J
def logPay (v:Pack D) := ∑ i:Hub D, Real.log (J.J (hew D y v i))
def cH := J.scale^(D*3) -- cardinal per hub
abbrev gH:= cH D J * g y^portDim D
-- outside soft chart weight null; ensure never log issue negative because mathlib. later set mouth always on swing/trunc.
def billH : Pack D→ℝ:= (mouthP D J y).indicator (fun v=>gH D J y * Real.exp (logPay D J y v))
lemma hewed : Measurable (hew D y):= (colorsT D).measurable.comp (by apply Continuous.measurable; fun_prop)
lemma lipm : MeasurableSet (mouthP D J y):= hewed D y (mouth_meas J)
lemma rose_meas : Measurable (rose D y):= measurable_pi_lambda _ fun i=> measurable_const.mul (group.lieExp_cont.measurable.comp ((measurable_pi_apply i).comp (hewed ..)))
lemma log_meas (u:LocalRatio J) : Measurable (logPay D J y):= Finset.measurable_sum _ fun i _=> (u.borel.comp ((measurable_pi_apply i).comp (hewed ..))).log
lemma billH_meas (u: LocalRatio J) : Measurable (billH D J y):= (measurable_const.mul (log_meas D J y u).exp).indicator (lipm ..)
lemma gH_pos (u: LocalRatio J)(p:0<y): 0 < gH D J y:=by unfold gH cH; positivity [u.scale,g_pos p]
lemma hew_mp (p:0<y) : MeasurePreserving (hew D y) (ENNReal.ofReal (g y^portDim D) • volume) volume:= by
 let q:=g y; have hp :0<q:=g_pos p; refine (slidesT D).comp (show MeasurePreserving (q • ·) (ENNReal.ofReal (g y^portDim D) • (volume : Measure (Pack D))) volume from ⟨measurable_const_smul _,?_ ⟩); rw [Measure.map_smul, Measure.map_addHaar_smul (volume:Measure (Pack D)) hp.ne', pack_n D, smul_smul]; rw [abs_of_pos (by positivity : 0<(q^n_ang D)⁻¹)]; change (ENNReal.ofReal (q^n_ang D) * ENNReal.ofReal ((q^n_ang D)⁻¹)) • volume= (volume:Measure (Pack D)); rw [← ENNReal.ofReal_mul (pow_nonneg hp.le _),mul_inv_cancel₀ (pow_pos hp _|>.ne'),ENNReal.ofReal_one,one_smul] -- tune name
lemma payH_eq (u:LocalRatio J)(x:Pack D)(p:x∈mouthP D J y): ennPay J (hew D y x) = ENNReal.ofReal (cH D J * Real.exp (logPay D J y x)):=by
 let a(i:Hub D):= J.J (hew D y x i); have ha(i):0<a i:=u.pos _ (p i (Set.mem_univ _)); have H:=u.scale; unfold ennPay; rw [← ENNReal.ofReal_prod_of_nonneg (fun i _=>mul_nonneg H.le (ha i).le)]; apply congrArg ENNReal.ofReal; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ, cH, logPay, Real.exp_sum]; congr 1; rw [show Fintype.card (Hub D)= D*3 by simp [Hub,SpatialDir]]; exact prod_congr rfl fun i _=> (Real.exp_log (ha i)).symm
lemma positive_bill (u:LocalRatio J)(p:0<y)(x:Pack D): 0 ≤ billH D J y x:= by unfold billH Set.indicator; split <;> positivity [gH_pos D J y u p]
lemma rose_mp (u: LocalRatio J)(p:0<y) : MeasurePreserving (rose D y) (volume.withDensity (ENNReal.ofReal ∘ billH D J y)) ((Rainy D).restrict (pullCover D J y)):=by
 let L:=(mouth J).indicator (ennPay (ι:=Hub D) J); have hx: logMeasure J (Hub D)=volume.withDensity L:=(withDensity_indicator (mouth_meas _) _).symm
 let r:=(g y)^portDim D; have hr:0<r:=pow_pos (g_pos p) _; let T:=hew D y; apply (rosin_mp D J y u).comp (show MeasurePreserving T _ (logMeasure J (Hub D)) from ?_); rw [hx]; let k:= L ∘ T; have hv:=payoff_mp L T (hew_mp D y p) ((ennPay_meas u).indicator (mouth_meas J)); convert! hv using 1; rw [withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]; apply congrArg volume.withDensity; ext i; by_cases v:i∈ mouthP D J y; swap; · simp [billH,k,T,L,v,(show T i ∉ mouth J from v)]; -- tune
 simp only [Pi.smul_apply,smul_eq_mul,comp_apply,billH,v,Set.indicator_of_mem]; rw [show L (T i)=ennPay J (hew D y i) from Set.indicator_of_mem (show T i∈mouth J from v) _, payH_eq D J y u i v, ← ENNReal.ofReal_mul hr.le]; unfold gH r; ring_nf
end YM.CF.BPress.Port
