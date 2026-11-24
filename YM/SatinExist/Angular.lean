import YM.SatinExist.Marl
import YM.Mink.Geometry

/-! ## Time dilation to real seam. Volume is ℝ-jacobian of physical time. -/
set_option autoImplicit false
set_option maxHeartbeats 230000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)(f:Probe E4)(s:ℝˣ)(v:Space3×ℝ)
def scaleT (s:ℝˣ): ℝ≃L[ℝ]ℝ:= ContinuousLinearEquiv.smulLeft s
def scaleSpace (s:ℝˣ): (Space3×ℝ)≃L[ℝ] Space3×ℝ:= (ContinuousLinearEquiv.refl ℝ Space3).prodCongr (scaleT s)
def tide (s:ℝˣ): E4≃L[ℝ] E4:= (Mink.divide.trans (scaleSpace s)).trans Mink.divide.symm
lemma tide_at (x:E4): tide s x= position (spatial x) ((s:ℝ)* time x):=rfl
lemma tide_det : LinearMap.det (tide s).toLinearEquiv.toLinearMap=(s:ℝ):=by
 have he : LinearMap.det (scaleSpace s).toLinearEquiv.toLinearMap=(s:ℝ):=by
    rw [show (scaleSpace s).toLinearEquiv.toLinearMap= (LinearMap.id (R:=ℝ)).prodMap ((s:ℝ) • (LinearMap.id (R:=ℝ))) from LinearMap.ext fun x=> rfl, LinearMap.det_prodMap]; simp -- name
 let u : (Space3×ℝ)≃ₗ[ℝ] E4:= Mink.divide.symm.toLinearEquiv
 rw [← he]; refine Eq.trans (congrArg _ (?_ : (tide s).toLinearEquiv.toLinearMap = (u: (Space3×ℝ)→ₗ[ℝ] E4) ∘ₗ (scaleSpace s).toLinearEquiv.toLinearMap ∘ₗ (u.symm:E4→ₗ[ℝ] (Space3×ℝ)))) (LinearMap.det_conj _ u)
 exact LinearMap.ext (fun _=>rfl)

private abbrev sec(s:ℝˣ) : E4 ≃ᵐ E4 := (tide s).toHomeomorph.toMeasurableEquiv
private lemma tide_price : MeasurePreserving (sec s) volume (ENNReal.ofReal |(s:ℝ)⁻¹| • volume):=by
 refine ⟨(sec s).measurable,?_⟩
 rw [← tide_det s]; exact map_linearMap_addHaar_eq_smul_addHaar _ ((tide_det s).symm ▸ s.ne_zero) -- unification prop dep; helper

-- tag u with detection scaling. Lebesgue-normalized, not a distribution of marks. `push`.

def inFlow (s:ℝˣ)(f:Probe E4): Probe E4:= ((↑|(s:ℝ)⁻¹|):ℂ) • Probe.along (tide s).symm f
lemma tide_scope : tsupport (inFlow s f)=(tide s) '' tsupport f:=by
 let A:= tide s; let h:= (tide s).toHomeomorph; let c:=((↑|(s:ℝ)⁻¹|):ℂ); have hc:c≠0:=by unfold c; exact ofReal_ne_zero.mpr (abs_ne_zero.mpr (inv_ne_zero s.ne_zero))
 rw [show tsupport (inFlow s f)=tsupport (⇑f ∘ h.symm) from ?_, tsupport_comp_eq_preimage, ← Homeomorph.image_eq_preimage_symm]; rfl
 apply congrArg closure; ext1 x; simp only [Function.mem_support,inFlow,_root_.smul_apply,Probe.along_at,comp_apply]; let y:= f (h.symm x); change c*y≠0 ↔ y≠0; simp [hc]
lemma from_vol (g:E4→H.space): (∫ p:E4,inFlow s f p • g p)=(∫ p:E4,f p • g (tide s p)) :=by
 let h':= Probe.along (tide s).symm f; let c:=|(s:ℝ)⁻¹|
 unfold inFlow; simp_rw [_root_.smul_apply,smul_eq_mul,mul_smul,integral_smul];
 change c • (∫ p:E4,h' p • g p)=_
 have hp : c • (∫ p:E4,h' p • g p)=∫ p:E4,h' p • g p ∂(ENNReal.ofReal |(s:ℝ)⁻¹| • volume):=by rw [integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
 rw [hp,← (tide_price s).integral_comp']; congr 1; funext p; change h' (tide s p) • _=_; unfold h'; rw [Probe.along_at,(tide s).symm_apply_apply]; rfl

variable (x:H)
private lemma tide_drop (p:E4): SEP timeAxis (tide s p)=SEP timeAxis p :=by
 rw [tide_at]; apply Subtype.ext; let q:= position (spatial p) ((s:ℝ)*time p)
 change q-time q • _= p-time p • _; apply Mink.ext_by
 · simp [q,sub_eq_add_neg]
 simp [q,sub_eq_add_neg]

lemma tide_cost (p:E4) (r t:ℝ)(u:(s:ℝ)=r*t): waveR S t (sideways r) p=S.unit.translation (tide s p):=by
 have h: sideways r * (↑(t*p timeAxis):ℂ)= sideways ((s:ℝ)*p timeAxis):=by unfold sideways; rw [u]; push_cast; ring
 unfold waveR; rw [h, oar_side]; let z:= tide s p
 have ht:z timeAxis= (s:ℝ) * p timeAxis:=by unfold z; rw [tide_at]; exact time_position ..
 change (S.U _).comp (S.edge _)=(S.edge (z timeAxis)).comp _; rw [ht,show (SEP timeAxis z)= _ from tide_drop s p]; exact (S.both ..).symm
lemma drift (r t:ℝ)(u:(s:ℝ)=r*t): advancing S x (inFlow s f)=fareR S t f x (sideways r):= by
 rw [advancing_eq,from_vol (H:=H)]; unfold fareR; simp_rw [tide_cost S s _ r t u] -- from_vol higher-order

-- profile amplitude normalized by (zσ)^n; full extension (all continuous, incl imaginary).
-- do NOT buy such amplitude in actual Eu quote; both endpoints norm bills below.
variable {Y:ℝ→H}(σ:ℝ)
lemma awarded (h:HasCompactSupport ⇑f)(u:charges timeAxis σ f)(p:VacuumPower Y)(k:Positive S Y){X: VacuumVector H}(e:Rim S Y X) :
    ∃ m:ℕ,∃ P:ℂ→ H, Continuous P ∧ AnalyticOnNhd ℂ P inside ∧
      P 1 = (((σ:ℂ)^m)) • (∫ x:E4,f x • S.U (SEP timeAxis x) (Y (σ*x timeAxis))) ∧
      (∀ z:ℂ,0≤z.re → Tendsto (fun t:ℝ=> ((z*(σ:ℂ))^m) • fareR S σ f (Y t) z) (𝓝[>] 0) (𝓝 (P z))) ∧
      ∀ (t:ℝ)(s:ℝˣ),(s:ℝ)=t*σ → P (sideways t)=((sideways t*(σ:ℂ))^m) • X (inFlow s f):=by
 obtain ⟨K,b,n,q⟩:=p; obtain ⟨v,hv⟩:= adding_cost S n Y k K b q; let m:=n+1
 let P':=(fun z:ℂ=>fareR S σ (dupes timeAxis z σ m f) v z)
 let A(z:ℂ):= (z*(σ:ℂ))^m
 have Hx(z:ℂ)(p:0≤z.re): Tendsto (fun x:ℝ=> A z • fareR S σ f (Y x) z) (𝓝[>] (0:ℝ)) (𝓝 (P' z)):=by
    let c:= RollCost S σ z (dupes timeAxis z σ m f)
    exact ((c.continuous.tendsto _).comp hv).congr (fun i=> (packet_roll S n σ (Y i) f u z p).symm)
 refine ⟨m,P',extends_stamp ..,marches_stamp S m σ v f u,  ?_,Hx,fun t s u=>?_⟩
 · have h':=tendsto_nhds_unique (Hx 1 (by simp)) ((loyal_stamp S σ f h u k).const_smul (A 1)); simpa only [A,one_mul] using h'
 refine tendsto_nhds_unique (Hx (sideways t) (by simp)) (((e.costs (inFlow s f)).const_smul (A (sideways t))).congr ?_)
 intro x; rw [drift S f s (Y x) t σ u]
end YM.SatinJets
