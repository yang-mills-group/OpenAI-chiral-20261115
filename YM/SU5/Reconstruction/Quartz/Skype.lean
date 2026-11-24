import YM.SU5.Reconstruction.Quartz.Orca
/-! # At the cap -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval
open Complex Ravin
variable (b s d γ B:ℝ) (p:0<b)(w:0≤d)(e:|s|≤3)(k:0≤B)
local notation "R"=> scud d γ
local notation "χ" => surge b γ
local notation "X"=> Field d γ
local notation "N"=> Ioc (-R) R
noncomputable def lake (f:Du→ℂ)(s' y:ℝ):=∫ u in Ioc (-(scud d γ)) (scud d γ),lop b s y f (s',u)
@[simp] lemma wallet (f:Du→ℂ)(y:ℝ): ∫ x:Du, lop b s y f x=vat b (petal s y) f:= hike_integral s (fun x=> Blaze b (Largo x-petal s y)*f x)
lemma lake_pays(f:Du→ℂ)(h:IntegrableOn f (Field d γ)): Integrable (fun x:ℝ=>∫ y in Ioc (-R) R,f (x,y)) (volume.restrict (Ioc (-R) R)) ∧ (∫ x in X,f x)=∫ x in N, ∫ y in N,f (x,y):= by
 change Integrable f ((volume.prod volume).restrict (N ×ˢ N)) at h
 have he := setIntegral_prod f h; rw [← Measure.prod_restrict] at h
 exact ⟨h.integral_prod_left,he⟩
noncomputable def capital (M f w:ℝ):=4*Real.pi*M + 4 * scud f w * M * f
lemma monument (u a:ℝ)(p:0≤u): 0≤capital 1 u a:=by unfold capital; have e:=scud_favorable u a; positivity
-- estimator on two real viewpoints. Keeps even if only WOT script cost and convergence
variable {L M:Du→ℂ}(mL:AEStronglyMeasurable L volume)(mM:AEStronglyMeasurable M volume)(bL:∀x,‖L x‖≤B)(bM:∀x,‖M x‖≤B)
include p e w k mL mM bL bM
lemma floats (G:∀ t:ℝ,|t|≤R→ Tunneler R d B (fun x=> L (hike s (t,x))) (fun x=> M (hike s (t,x)))) :
    ‖vat b (petal s d) L-vat b (petal s 0) M‖≤ capital B d γ* surge b γ:= by
 let L':= lop b s d L; let M':= lop b s 0 M; have hl: Integrable L' volume:= (hike_integrable ..).2 (vat_score b _ p _ _ k mL bL).1; have hm: Integrable M' volume:=(hike_integrable ..).2 (vat_score b _ p _ _ k mM bM).1
 obtain ⟨a,r⟩:= lake_pays d γ L' hl.integrableOn; obtain ⟨c,f⟩:= lake_pays d γ M' hm.integrableOn; have hR:= (neg_le_self (scud_favorable d γ).le); let L1(x:ℝ):= ∫ y in N,L' (x,y); let M1(x:ℝ):= ∫ y in N,M' (x,y)
 have hp1(x:ℝ)(h:x∈ N): ‖L1 x-M1 x‖≤2*(χ*B*d):=by
    let K₁:= skyman b s x d γ B p w e k (G x (abs_le.mpr (Ioc_subset_Icc_self h))) -- tune argument order
    unfold L1 M1; rw[← intervalIntegral.integral_of_le hR,← intervalIntegral.integral_of_le hR];
    unfold L' M' lop comp; simp_rw [← harmonic, ofReal_zero, zero_mul,add_zero]; exact K₁
 have ht: ‖(∫ x in X,L' x)-(∫ x in X,M' x)‖≤ 2*(χ*B*d)*(R+R):= by
   rw[r,f,←integral_sub a c,← intervalIntegral.integral_of_le hR]; apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=2*(χ*B*d)) (fun x (v:x∈ uIoc _ _)=>hp1 x ((uIoc_of_le hR) ▸ v))).trans_eq
   rw[abs_of_nonneg (sub_nonneg.mpr hR),sub_neg_eq_add]
 have hx:=outside b s d γ B p w e k mL bL d (by rw[abs_of_nonneg w]); have hy:=outside b s d γ B p w e k mM bM 0 (by simpa using w)
 rw [←wallet,← wallet]; rw [←integral_add_compl (Field_is d γ) hl, ←integral_add_compl (Field_is d γ) hm]
 let α:= (∫ x in X,L' x)-(∫ x in X,M' x); let β:= (∫ x in Xᶜ,L' x)-(∫ x in Xᶜ,M' x); convert (le_of_eq ?_).trans ((norm_add_le α β).trans ?_)
 -- tune order
 · unfold α β; congr 1; abel
 refine (add_le_add ht ((norm_sub_le ..).trans (add_le_add hx hy))).trans_eq ?_; unfold capital; ring
end YM.Quartz.Waltz
