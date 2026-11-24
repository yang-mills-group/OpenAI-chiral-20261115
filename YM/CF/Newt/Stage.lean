import YM.CF.Newt.Vist
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ E: Type} [NormedAddCommGroup E][NormedSpace ℝ E] [Fintype ι] [Fintype τ] {C D v K d N X U s r a e:ℝ}{n:ℕ}
open Next.SectorChange (panels shots)
open Next.SectorChange.Rows (gram)
variable {G:Gauge}{P:Patch}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
lemma smallF {n:ℕ}(hp:0<v)(M:ℝ): ∀ᶠ x:ℝ in atTop, Real.exp (-v*Stores.till x)*M ≤ (temp x)^n:=by
 -- without clue: use x⁻¹ ≤ temp; M ≤ x
 filter_upwards [Lift.plume v (n+1:ℝ) hp,eventually_gt_atTop (1:ℝ),eventually_gt_atTop M] with x hx ht hv
 have hp: 0<x:=zero_lt_one.trans ht
 calc
    _ ≤ x^(-(n+1:ℝ))*x:= (mul_le_mul_of_nonneg_left hv.le (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right hx hp.le)
    _ = (x⁻¹)^n :=by rw [Real.rpow_neg hp.le, Real.rpow_add hp, Real.rpow_natCast, Real.rpow_one,inv_pow]; field_simp
    _ ≤ _ :=by
        gcongr
        unfold temp; refine le_trans (inv_anti₀ (by positivity) (Real.sqrt_le_self_iff.mpr (Or.inr ht.le))) ?_; exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
lemma brightY (F:Forest T.ratio)(x:ℝ)(k:T.Choices)(he:Estimate n d v r a K (bareStores T) F R x (1:Config G c) k 0) (h:0<d)(hz:0≤K)(p:R.up.Bounds R.high T'.top.width T'.top.paths D)(ht:Bid.Larger (G:=G) T)(hx:Lift.Booth T' T R)(hf:Real.exp (-v*radiusB x)*K≤s)
 (hb:Real.exp (-(T'.top.width/4)*Stores.till x)*ozPay T.patch T.kernel T'.top.width T'.top.paths G≤s)(hu:‖gall R x k F 0‖ ≤ U):
 ‖ContinuousLinearMap.id ℝ _-(gall R x k F 0).comp (paintO (block (costP F k R.high R.up) 0))‖ ≤ (1+U)*s:=by
 have hs:0≤s:= (mul_nonneg (Real.exp_pos _).le hz).trans hf; have ha:0 ≤ U:=(norm_nonneg _).trans hu
 have hy:= (blemish F x k he h hz).trans (le_trans (mul_comm ..).le hf)
 let H:= paintO (block (costP F k R.high R.up) 0); let G':=gall R x k F 0; let K':= gabs R x k F 1
 have hh : ‖H-K'‖≤s:=(octo F x k p ht hx T'.top.paths_pos.le).trans hb
 have hb : ContinuousLinearMap.id ℝ _-G'.comp H= ContinuousLinearMap.id ℝ _-G'.comp K'-G'.comp (H-K'):=by ext v j; simp only [_root_.sub_apply,map_sub,ContinuousLinearMap.comp_apply]; simp only [Pi.sub_apply]; abel
 change ‖ContinuousLinearMap.id ℝ _-G'.comp H‖ ≤ _; rw [hb]; exact (norm_sub_le ..).trans ((add_le_add hy ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul hu hh (norm_nonneg _) ha))).trans_eq (by ring))
-- Earlier issue first epsilon Y from arbitrary Before functions. stage hypothesis
structure Cert {G:Gauge}(P:RG.Patch)(K:Teller G)(T:StepData c f)(U:Tube G T)(x:ℝ):Prop where
 got : T.patch=P
 funds: Lift.Booth K T U
 size : 100*(1+radiusB x)≤ c.val
 pace : Bid.Larger (G:=G) T
lemma moon (T:Teller G)(n:ℕ) (J:Patch)(p:J.Branches T.bind G): ∃ B C:ℝ,0<B∧ 0<C ∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(U:Tube G S),Cert J T S U x →
 ∀ (F:Forest S.ratio)(k:S.Choices), (∀ y:Mast G c, ‖y‖ ≤ B →Allows n (gall U x k F) y C) ∧ ‖ContinuousLinearMap.id ℝ _ - (gall U x k F 0).comp (paintO (block (costP F k U.high U.up) 0))‖ ≤ (1+C)*temp x:=by
 obtain ⟨r,d,v,y,Q,K,hr,hd,hv,-,-,hk,H⟩:=estimates G J T p n
 let F:= activation G n 0 d*K
 let C:= composeCost n F (Uniform.shade G); let C':=1+ max 0 C; have hC : 0<C':=by unfold C'; linarith [le_max_left 0 C]
 have hc:C≤C' := (le_max_right ..).trans (le_add_of_nonneg_left zero_le_one)
 let B:=min r 1; have hy :0<B:=lt_min hr zero_lt_one
 let K':= ozPay J T.bind T.top.width T.top.paths G
 have hh:= smallF (n:=1) hv K
 refine ⟨B,C',hy,hC,?_⟩
 filter_upwards [hh,H,smallF (n:=1) (show 0<T.top.width/4 by have h:=T.top.width_pos; positivity) K'] with x he hp he'
 intro c f S U H F k; have hA : (bareStores S).flags=flags (temp x) (1:Config G c):=(noFlags ..).symm
 have hP: T.Funds S U:=H.funds.1; obtain ⟨A,D,h1,h2⟩:=hP.feeds
 have ht {Z} (hZ : ‖Z‖ ≤ r) := hp.2 S U H.got H.size hP (bareStores S) F 1 hA k Z hZ
 have hI (v:Mast G c) (h:‖v‖ ≤ B):Allows n (gall U x k F) v C:=gallery F x k v (ht ((hull_h _).trans (h.trans (min_le_left ..)))) hd hk.le (h.trans (min_le_right ..))
 refine ⟨fun x hx=> (hI x hx).mono hc, brightY F x k (ht (Z:=0) (by simpa using hr.le)) hd hk.le (hP.high.symm ▸ h1) H.pace H.funds ?_ ?_ ((hI _ (by simpa using hy.le)).value.trans hc)⟩
 · rw [pow_one] at he
   apply le_trans ?_ he; apply mul_le_mul_of_nonneg_right _ hk.le; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hv.le); exact_mod_cast (Nat.div_le_self (radiusB x) 100000)
 rw [H.got,hP.knobs]; rwa [pow_one] at he'
end YM.CF.Newt
