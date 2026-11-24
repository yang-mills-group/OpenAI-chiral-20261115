import YM.CF.BPress.Wealth.Pane
/-!
κ up to 1/16. Eventually for these uses per y uniform. Price orientation panels with Taylor. Constants need be bought before further coupled choices. Show support of Taylor reads below amplitude on actual Mission at every regular root, plus global background.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
lemma m_sub : NPL (fun i=> mA i/temp i):= npl_congr (F:=fun i=>(heigh i)⁻¹^2) ((eventually_gt_atTop (0:ℝ)).mono fun i p=>by rw [temp_price p,mA_price p]; have h:=heigh_pos i; have hs:= root_pos p; field_simp) (npl_power heigh_npl _ (by omega))
lemma x_sub : NPL (fun i=> xi i/temp i):= npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun i p=> show root i^4* heigh i^(-8:ℤ)=_ from by rw [temp_price p,xi_price p,zpow_neg]; have h:=heigh_pos i; have hs:=root_pos p; field_simp) (root_tall _ _ (by omega))
lemma finer_sub : NPL (fun i=>finer i/temp i):= npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun i p=> show aA i+temp i+xi i/temp i=_ from by have hs:= temp_pos p; unfold finer; field_simp) ((npl_aA.add npl_temp).add x_sub)
lemma t_a : NPL (fun i=> temp i/aA i):= npl_congr (F:=fun i=> root i^1 * heigh i^(5:ℤ)) ((eventually_gt_atTop (0:ℝ)).mono fun i p=>by rw [temp_price p, aA_price p, pow_one]; have ht:=root_pos p; have he:=heigh_pos i; field_simp) (root_tall _ _ (by omega))
lemma finer_full : NPL (fun y=> y * finer y * temp y):= by
 unfold finer; apply npl_congr (F:=fun i=>(root i^1 *heigh i^ (19:ℤ)+root i^2*heigh i^(24:ℤ))+root i^4*heigh i^(8:ℤ)) _ (((root_tall 19 1 (by omega)).add (root_tall 24 2 (by omega))).add (root_tall 8 4 (by omega))); filter_upwards [eventually_gt_atTop (0:ℝ)] with y p; have h:=heigh_pos y
 rw [aA_price p,temp_price p,xi_price p]; have ht:=root_pos p; apply Eq.symm; nth_rw 1 [show y=(root y^4)⁻¹ from (by rw [hat_price p,inv_inv])] -- recursive rw RHS all occurrences! use nth_rw
 field_simp
-- handy jacobian curvature lift in Frob
-- Linear left inverse at chord coordinate.
def curveAbs (G : Gauge) : G.Mat →ₗ[ℝ] G.Color:= (G.colorScale/2) • (G.projectColor.comp ((LinearMap.id: G.Mat →ₗ[ℝ] G.Mat) - (starL' ℝ).toLinearEquiv.toLinearMap))
lemma curve_le (G : Gauge)(v:G.Mat) : ‖curveAbs G v‖ ≤ ‖v‖:=by
 change ‖(G.colorScale/2) • G.projectColor (v-star v)‖≤ _; have ht:=G.colorScale_pos; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_left (G.project_norm _) (by positivity)); field_simp; nlinarith only [(norm_star v) ▸ (norm_sub_le v (star v))] -- tune rt
lemma curved_actual (U:E): curveAbs group (canonM U)=group.curvature U:=by
 let A:=group.mat U-1; have ht: star A=group.mat U⁻¹-1:=by simp [A]
 change (scr/2) • group.projectColor (scr⁻¹ • A-star (scr⁻¹ • A))=_; rw [star_smul,star_trivial,ht,←smul_sub]; unfold A; rw [sub_sub_sub_cancel_right,←map_smul, smul_smul]; congr 2; have hx:0<scr:=group.colorScale_pos; field_simp
lemma curved_canon (v:ink): curveAbs group (canonE v)=v:=by
 let K:=group.colorScale; have hx:0<K:=group.colorScale_pos; change (K/2) • group.projectColor ( (K⁻¹) • group.colorMat v-star (K⁻¹ • group.colorMat v)) = _; rw [star_smul,star_trivial,group.colorMat_skew,←smul_sub,map_smul,smul_smul, map_sub,map_neg, group.project_colorMat]; rw [sub_neg_eq_add, ←two_smul ℝ, smul_smul,show K/2*K⁻¹*2=1 by field_simp]; exact one_smul _ _

abbrev faceR {s:Side} (v : Signed)(U:Micro s)(p:Bonding s):= faceValue (pull v 0 U) p
lemma item_close {s:Side}(v : Signed)(U V:Micro s)(p:Bonding s)(c:ℝ)(h:∀ i, chord (U (address v (aperture p i))) (V (address v (aperture p i))) ≤ c) : chord (faceR v U p) (faceR v V p) ≤ 4*c:=by unfold faceR; rw [readA_val,readA_val]; apply reader_cost _ _; intro i; rw [pull_close]; exact h _

structure Dividend (D κ C y:ℝ) : Prop where
 young : 0<y
 posC : 0<C
 branch : 0 ≤ κ*temp y
 brand : aA y≤1
 mag : mA y ≤ temp y
 fire : temp y ≤ aA y
 olive : xi y+κ*temp y ≤ temp y
 fixed (v:Signed)(p:PlaqAxes): ‖psi v p‖ ≤ C
 bgChord (s:Side)(v:Signed)(p:Bonding s): group.chord (faceR v (background y) p) ≤ C*mA y
 bgCase (s:Side)(v:Signed)(p:Bonding s): ‖canonM (faceR v (background y) p)-mA y • canonE (psi v p.2)‖ ≤ C*aA y^3
 buyer : 4*(xi y+κ*temp y) + C*mA y ≤ temp y
 bgView (i:Axis): group.chord (group.lieExp (aA y • backgroundDir i)) ≤ C*aA y
 faceCase (s:Side)(v:Signed)(U:Micro s)(p: Bonding s) (g:Directions group s) (f : ∀ i,‖g (address v (aperture p i))‖ ≤ D*temp y) (w:∀ i,chord (U (address v (aperture p i))) (actuated y g (address v (aperture p i))) ≤ xi y):
    ‖canonM (faceR v U p)-canonM (faceR v (background y) p)-canonE (orbitP v p g)‖ ≤ C*finer y
lemma base_call : ∃ C:ℝ, 0<C ∧ ∀ᶠ y in atTop, ∀ i:Axis, group.chord (group.lieExp (aA y • backgroundDir i)) ≤ C*aA y :=by
 choose C h H using fun i:Axis=> chord.exp_order (backgroundDir i)|>.exists_pos; let L:=∑ i:Axis,C i; have hs:=group.colorScale_pos; have he(i):C i≤ L:=single_le_sum (fun i _=>(h i).le) (mem_univ i); refine ⟨L/group.colorScale,div_pos ((h 0).trans_le (he _)) hs,?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ), eventually_all.mpr (fun i: Axis=> npl_aA.drop.eventually (H i).bound)] with y p q i; specialize q i; rw [Real.norm_of_nonneg (aA_positive p).le] at q; unfold Gauge.chord; change _ ≤ _; refine le_trans (div_le_div_of_nonneg_right (q.trans (mul_le_mul_of_nonneg_right (he _) (aA_positive p).le)) hs.le) ?_; rw [mul_div_right_comm]; rfl -- tune

lemma weak_dividend (D κ:ℝ)(p:0<D)(q:0<κ)(k:κ≤1/16) : ∃ C:ℝ, 0<C ∧ ∀ᶠ y in atTop, Dividend D κ C y:=by
 obtain ⟨C,h,H⟩:= panel_purchase D p; obtain ⟨B,vB,W⟩:= base_call; let Z:=2*C+B; have hZ:0<Z:=by unfold Z; positivity
 have z:C≤Z:=by unfold Z; linarith
 refine ⟨Z,hZ,?_⟩; filter_upwards [H,W,x_sub.drop.eventually (ge_mem_nhds (by norm_num : 0<(1/16:ℝ))), m_sub.drop.eventually (ge_mem_nhds zero_lt_one), (m_sub.const_mul Z).drop.eventually (ge_mem_nhds (by norm_num : 0<(1/2:ℝ))), npl_aA.drop.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ), t_a.drop.eventually (ge_mem_nhds zero_lt_one)] with y a b x m ht l f ff
 have hx:=temp_pos f; have hm:= mA_pos f; have hv:= aA_positive f
 have hs: mA y≤temp y:= by apply (div_le_one hx).mp; exact m
 have z':0≤ κ * temp y:= mul_nonneg q.le hx.le; have px:= (div_le_iff₀ hx).mp x; have hh:4*(xi y+κ*temp y) + Z*mA y≤temp y:=by change Z* _ ≤ _ at ht; rw [←mul_div_assoc] at ht; have hp:=(div_le_iff₀ hx).mp ht; nlinarith only [hp, k,hx,px]; -- tune
 refine ⟨f,hZ,z',l,hs,(div_le_one hv).mp ff,(by nlinarith only [hx,k,px]), fun v j=> (a v j).1.trans z, ?_,?_,hh,fun i=> (b i).trans (mul_le_mul_of_nonneg_right (show B ≤ Z by unfold Z; linarith only [h]) hv.le),?_ ⟩
 · intro s v i; unfold faceR; rw [color_panel, ←canonM_price]; obtain ⟨x,p,e⟩:= a v i.2; refine le_trans (norm_le_norm_sub_add _ (mA y • canonE (psi v i.2))) ?_; apply le_trans (add_le_add p le_rfl); rw [norm_smul, canonE.norm_map,Real.norm_of_nonneg hm.le,pow_succ,aA_sq f]; unfold Z; nlinarith only [mul_le_mul_of_nonneg_left x hm.le,mul_le_mul_of_nonneg_left l (mul_nonneg h.le hm.le),h,hm, mul_pos vB hm] -- tune shadows
 · intro s v i; unfold faceR; rw [color_panel]; exact (a v i.2).2.1.trans (mul_le_mul_of_nonneg_right z (pow_nonneg hv.le _))
 intro s v U i g e t; unfold faceR; rw [color_panel]; apply le_trans ?_ (mul_le_mul_of_nonneg_right z (finer_pos f).le); refine (a v i.2).2.2 (brandW v g i) (faceR v U i) ((pi_norm_le_iff_of_nonneg (mul_pos p hx).le).mpr (fun i=> ?_)) ?_; swap; · rw [← rolled]; exact item_close v U _ _ _ t
 rw [brandW,orbit_fee]; exact e i -- tune
end YM.CF.BPress.Wealth
