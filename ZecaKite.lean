import ZecaStar
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.SatinJets.Stellar
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j)

lemma flight_steeper {c a b:ℝ}(hp:0<c)(p:c≤a)(q:c≤b):
 ‖S.E b.toNNReal - S.E a.toNNReal‖≤2/c*|b-a|:=by
 let D:Set ℂ:=Complex.ofRealCLM '' Set.Ici c
 have d:Convex ℝ D:=(convex_Ici c).linear_image ofRealCLM.toLinearMap
 have e(w:ℝ)(u:c≤ w):duration w.toNNReal=ofRealCLM w:=by
    rw [duration, Real.coe_toNNReal _ (le_trans hp.le u)]; rfl
 rw [←S.roots_heat (Real.toNNReal_pos.mpr (hp.trans_le p)),←S.roots_heat (Real.toNNReal_pos.mpr (hp.trans_le q)), e a p,e b q,
      ←Real.norm_eq_abs, ←Complex.norm_real, show ((↑(b-a)):ℂ)=ofRealCLM b-ofRealCLM a from Complex.ofReal_sub _ _]
 refine Convex.norm_image_sub_le_of_norm_deriv_le ?_ ?_ d ⟨_,p,rfl⟩ ⟨_,q,rfl⟩
 · rintro w ⟨t,y,rfl⟩; exact (S.localHeat _ (show 0<t from hp.trans_le y)).differentiableAt
 rintro w ⟨t,y,rfl⟩; rw [←e t y]
 exact (stellar_pay S (show 0<t from hp.trans_le y)).trans
    (div_le_div_of_nonneg_left (by positivity) hp y)
