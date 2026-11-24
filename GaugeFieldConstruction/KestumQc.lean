import GaugeFieldConstruction.Fleck
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!
# Local Q2 calculus on many-price kernels
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Salam
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Metric
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ}
lemma rooted_neQc {m:ℕ}(a:Fin m)(i:Axis)(b:Fin m)(h:a≠b): ∀ᵐ x:Points m,x a i≠x b i:=by
 let K:Points m→L[ℝ] ℝ:= Payroll.proj i ∘L (Payroll.loc a-(Payroll.loc b))
 let U:=LinearMap.ker K.toLinearMap
 have hv(x:Points m): x∈U↔x a i=x b i:=by
    change Payroll.proj i ((Payroll.loc a-Payroll.loc b) x)=0 ↔ _ ; rw [ContinuousLinearMap.sub_apply,map_sub]; exact sub_eq_zero
 have he:U≠⊤:=by
    intro e; have He: direction a i∈U:=e.symm ▸ Submodule.mem_top; have g:=(hv _).mp He; simp [direction,h.symm] at g
 have hp: ∀ᵐ x ∂(volume:Measure (Points m)), x∈ (U:Set (Points m))ᶜ:=compl_mem_ae_iff.mpr (Measure.addHaar_submodule _ U he)
 exact hp.mono (fun x h y=> h ((hv _).mpr y))
lemma rooted_genericQc (m:ℕ): ∀ᵐ x:Points m,x∈generic m:=by
 have H(a b:Fin m)(i:Axis):∀ᵐ x:Points m,a≠ b→x a i≠ x b i:=by
    by_cases h:a=b; · simp [h]
    exact (rooted_neQc _ _ _ h).mono (fun _ l _=>l)
 filter_upwards [ae_all_iff.mpr (fun a=> ae_all_iff.mpr (fun b=> ae_all_iff.mpr (H a b)))] with x hx a i j he; exact Classical.byContradiction (fun h=> hx i j a h he)
def guild (v:E4) :Prop:= ∀ i:Axis,v i≠0
lemma PackfreeQc : ∀ᵐ x:E4, guild x:= ae_all_iff.mpr (fun (i:Axis)=>by -- analogous
 let K:E4→L[ℝ] ℝ:= Payroll.proj i; let U:=LinearMap.ker K.toLinearMap; have h:U ≠⊤:=by
    intro h; have he:basis i∈U:=h.symm ▸ Submodule.mem_top; change basis i i=0 at he; simp at he
 exact (show ∀ᵐ x ∂(volume:Measure E4), x ∈ (U:Set E4)ᶜ from compl_mem_ae_iff.mpr (Measure.addHaar_submodule _ U h)).mono (fun _ h k=>h k))
def LensQc (y:E4)(x:Points (n+1)):Points (n+2):= cons (head x+y) x
def LonelyQc (y:E4) : Points (n+1):= cons y 0
lemma HeelQc (y:E4)(h:guild y):∀ᵐ x:Points (n+1),LensQc y x∈ generic (n+2):=by
 let v:= LonelyQc (n:=n) y
 have Hp : MeasurePreserving (fun x:Points (n+1)=> x+v) volume volume:= measurePreserving_add_right _ _ -- tune
 filter_upwards [rooted_genericQc (n+1),Hp.quasiMeasurePreserving.ae (rooted_genericQc (n+1))] with x h₁ h₂ a
 change x+v∈generic (n+1) at h₂
 let u:= LensQc y x
 have he (i:Fin (n+1)): u i.succ a=x i a:=by simp [u,LensQc, cons]
 have T: u 0=head x+y:=by simp [u,LensQc,cons]
 have H (i:Fin (n+1)): u 0 a ≠ u i.succ a:=by
    rw[he,T]; refine Fin.cases ?_ ?_ i
    · simp [head,h a]
    intro j e
    apply (Fin.succ_ne_zero j).symm -- tune apply
    have v₀:(x+v) 0=x 0+y:=by simp [v,LonelyQc,cons]
    have vk:(x+v) j.succ=x j.succ:=by simp [v,LonelyQc,cons]
    exact h₂ a (a₁:=0) (a₂:=j.succ) (by simp only [v₀,vk]; exact e) -- tune
 intro i; refine Fin.cases ?_ ?_ i
 · intro j; refine Fin.cases ?_ ?_ j
   · simp
   intro k e; exact ((H k) e).elim
 intro k j; refine Fin.cases ?_ ?_ j
 · intro e; exact ((H k) e.symm).elim
 intro m e; exact congr_arg _ (h₁ a ((he k).symm.trans (e.trans (he m))))

-- actual initially Borel, plenum not smooth at ties. enough.
structure PlaqueQc (K:Points n→ℂ) :Prop where
  bright:Measurable K
  tiled:∀ u:Set (Points n), IsCompact u → u⊆conf n → ∃ C:ℝ,0≤C∧∀ x ∈ u, ‖K x‖ ≤ C
  warm:∀ x∈ generic n, ContinuousAt K x
lemma BondCostQc (p:Test n)(K:Points n→ℂ)(c:PlaqueQc K): Integrable (fun x=>p x*K x):=by
 let U:=tsupport p
 obtain ⟨V,h,e⟩:=c.tiled U p.hasCompactSupport p.tsupport_subset
 have he:Integrable (fun x => ‖p x‖*V):= ((p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport).norm).mul_const _
 refine he.mono' (p.continuous.measurable.mul c.bright).aestronglyMeasurable (Eventually.of_forall (fun x=>?_)); by_cases h:x∈U; · exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (e _ h) (norm_nonneg _))
 rw [image_eq_zero_of_notMem_tsupport (f:=p) h]; simp
lemma BondLensQc (p:Test (n+1))(K:Points (n+2)→ℂ)(c:PlaqueQc K) (y:E4) (q:∀ x∈tsupport p,LensQc y x∈conf (n+2)): Integrable (fun x=>p x*K (LensQc y x)):=by
 have v0:Continuous (LensQc (n:=n) y):= fuse.symm.continuous.comp ((helm.continuous.add_const _).prodMk continuous_id)
 obtain ⟨V,h,e⟩:=c.tiled _ ((show IsCompact _ from p.hasCompactSupport).image v0) (image_subset_iff.mpr q)
 have he:Integrable (fun x=> ‖p x‖*V):= ((p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport).norm).mul_const _
 refine he.mono' (p.continuous.measurable.mul (c.bright.comp v0.measurable)).aestronglyMeasurable (Eventually.of_forall fun x=>?_)
 by_cases h:x∈tsupport p; · exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (e _ (mem_image_of_mem _ h)) (norm_nonneg _))
 rw [image_eq_zero_of_notMem_tsupport (f:=p) h]; simp
#check MeasureTheory.MeasurePreserving
#check Fin.succ_ne_zero
#check MeasureTheory.Measure.addHaar_submodule
#print axioms rooted_genericQc
end YM.GaugeFieldConstruction.Fathom.Salam
