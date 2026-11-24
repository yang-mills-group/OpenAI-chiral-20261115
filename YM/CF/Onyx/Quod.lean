import YM.CF.Onyx.Opal
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {j:ℕ}{r C D:ℝ}
namespace Yard
variable {S:ℕ→Side}{R:ℕ→ℝ}{X Y:Gaia}{v:∀ i,Offset (S i)}{M:ℕ→Male}{k:∀ i,Site (S i)}{A:∀ i,Site (S i)→Peb}{z:ℕ→Cover}
variable (h:Yard S R)(f:∀ᶠ i in atTop,FormU (v i) j (M i) r C (A i))(H:1≤j)
include h H
lemma mote (W:Tendsto (fun i=>duel (R i) (v i) (k i)) atTop (𝓝 X))(M:ℕ→Male): Tendsto (fun i=> (R i)^2*disk j (M i) (glen (v i) (k i))) atTop (𝓝 (fieldV X)):=by
 let T(i):= (R i:ℂ); have hp:= flare h M W H |>.norm
 rw [Complex.norm_real,Real.norm_of_nonneg (by unfold fieldV; positivity)] at hp
 simp_rw [norm_mul,norm_pow,Complex.norm_real, show ∀ i,‖R i‖=R i from fun i=>Real.norm_of_nonneg (h.pos i).le] at hp; exact hp
include f
lemma sled_h(p:X≠0)(w:Tendsto (fun i=>duel (R i) (v i) (k i)) atTop (𝓝 X)): Tendsto (fun i=> ((R i)⁻¹:ℝ) • A i (k i)) atTop (𝓝 ((fieldV X:ℂ)⁻¹ • ((1/2:ℂ) • lash (river X)))):=by
 let G(i):=glen (v i) (k i); have hm:= h.mote H w M; have he:= h.water.pow 2|>.const_mul r; change Tendsto (fun n=> r*_^2) _ _ at he; rw [zero_pow (by decide),mul_zero] at he; have ht:0<fieldV X:=fen p
 have hz:(fieldV X:ℂ)≠0:=by exact_mod_cast ht.ne'
 apply (((flare h M w H).inv₀ hz).smul (hook h M w H)).congr'; filter_upwards [f,hm.eventually (lt_mem_nhds (show fieldV X/2<fieldV X by linarith)),he.eventually (gt_mem_nhds (show 0<fieldV X/2 by positivity))] with i hi e u; have hr:=h.pos i
 have hk: r*pinch (S i)^2<disk j (M i) (G i):=by
    apply lt_of_mul_lt_mul_left (a:=(R i)^2) _ (by positivity); refine lt_trans ?_ (show _ < (R i)^2 *disk j (M i) (G i) from e); change r*(R i * pinch (S i))^2 <_ at u; exact (le_of_eq (by ring : R i^2*(r*pinch (S i)^2)=r*(R i*pinch (S i))^2)).trans_lt u
 let P:= tmap (G i); let y:ℂ:= (R i:ℂ); let m:= M i
 change (y^2 * shell j m.val P)⁻¹ • (y • _) = ((R i)⁻¹:ℝ) • _; rw [hi.far (k i) hk,dip, ← BZ.ofReal_action,smul_smul,smul_smul,Complex.ofReal_inv,mul_inv]; change _= (y⁻¹*(shell j m.val P)⁻¹) • _; rw [show (y^2)⁻¹ * (shell j m.val P)⁻¹ * y=y⁻¹*(shell j m.val P)⁻¹ from (by have hv:y≠0:=(by unfold y; exact_mod_cast hr.ne'); rw [mul_right_comm,show (y^2)⁻¹*y=y⁻¹ from (by rw [←inv_pow,sq,mul_assoc,inv_mul_cancel₀ hv,mul_one])])]
set_option maxHeartbeats 600000 in
lemma core_h(p:X≠0)(w:Tendsto (fun i=>duel (R i) (v i) (k i)) atTop (𝓝 X))(W:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 Y))(q:0<D): Tendsto (fun i=>sled (v i) (sulk (v i) j (M i) (R i) D (A i)) (z i) (R i) (k i)) atTop (𝓝 (sha D Y X)):=by
 let y:=fieldV X; have he:0<y:=fen p
 let L(i):=Real.exp (-(soft (R i) D*disk j (M i) (glen (v i) (k i))))
 let d:=tog (kiln D) X; have ht:Tendsto L atTop (𝓝 d):=by
    have hx:= h.mote H w M; have hg:= Real.continuous_exp.continuousAt.tendsto.comp ((hx.div_const (D^2)).neg); convert hg using 1
    · ext i; unfold L soft; congr 1 -- inspect
      ring
    congr 1; unfold d tog fieldV kiln; congr 1; ring
 have hp:Tendsto (fun i=>charK (v i) (k i) (z i)) atTop (𝓝 (burn Y X)):=by
    let E(p:Gaia×Gaia):= burn p.1 p.2; have hf:Continuous E:=by unfold E burn; fun_prop
    have ht:= hf.tendsto (Y,X); refine (ht.comp (W.prodMk_nhds w)).congr (fun i=>?_); exact (cartR _ _ (h.pos i) _).symm
 have hh:= hp.smul (ht.smul (h.sled_h f H p w)); convert hh using 1
 · ext1 i; let c:=charK (v i) (k i) (z i); unfold sled sulk; change _= c • (L i • _); rw [smul_comm ((R i)⁻¹:ℝ) c,smul_comm ((R i)⁻¹:ℝ) (L i)]; -- tune
 congr 1; rw [sha,← BZ.ofReal_action]; simp only [smul_smul]; congr 1; unfold d purr pet fieldV; push_cast; have hz:=norm_pos_iff.mpr p; have hv:(‖X‖:ℂ)≠0:=(by exact_mod_cast hz.ne'); field_simp; ring
lemma hail_v(W:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 Y))(p:0<r)(u:0<C)(d:0<D): Tendsto (fun i=> bore (v i) (R i) (z i) (sulk (v i) j (M i) (R i) D (A i))) atTop (𝓝 (dun D Y)):=by
 classical
 obtain ⟨V,g,P⟩:= hold_p H p u d; simp_rw [show ∀ i,bore (v i) (R i) (z i) (sulk (v i) j (M i) (R i) D (A i))= _ from fun i=>boon _ _ (h.pos i) _] -- tune
 let F(i):= sled (v i) (sulk (v i) j (M i) (R i) D (A i)) (z i) (R i)
 let T(i):= apr (F i) (R i)
 have he :∀ᵐ x:Gaia,x≠0:=by rw [ae_iff]; simp
 unfold dun; apply Tendsto.const_smul (f:=fun i=>∫ x:Gaia,T i x) _ cartWeight; apply tendsto_integral_filter_of_dominated_convergence V (Eventually.of_forall fun i=> sot ..) _ g
 swap; · filter_upwards [f,h.water.eventually (gt_mem_nhds one_pos)] with i hi hx; exact he.mono fun x hu=> P x hu (h.even _) hi (h.pos i) (le_of_lt hx) _
 filter_upwards [he,h.cells] with x hu hx
 let k(i):= if H:∃ k:Site (S i),x∈ pie (R i) k then H.choose else 0
 have ht:∀ᶠ i in atTop,x∈pie (R i) (k i):=hx.mono fun i h=>by unfold k; rw [dif_pos h]; exact h.choose_spec
 exact (h.core_h f H hu (h.facing ht v) W d).congr' (ht.mono fun i e=> (shout e _).symm)
lemma struck(H':Y≠0)(W:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 Y))(p:0<r)(u:0<C): Tendsto (fun i=> bore (v i) (R i) (z i) (A i)) atTop (𝓝 (pencil Y)):=by
 obtain ⟨c,g,V⟩:= h.sheen H p u Y _ W H'
 refine Metric.tendsto_nhds.mpr fun e he=> ?_
 have ht:Tendsto (fun x:ℝ=> c/x^2) atTop (𝓝 0):=by have hg:= (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_pow_atTop (by decide : (2:ℕ)≠0)); simpa only [Function.comp_def,mul_zero,←div_eq_mul_inv] using hg.const_mul c
 have hx:=Metric.tendsto_nhds.mp (wind_v H') (e/3) (by linarith)
 obtain ⟨D,⟨hd,hy⟩,hD⟩:= ((hx.and (ht.eventually (gt_mem_nhds (show 0<e/3 by linarith)))).and (eventually_gt_atTop 0)).exists -- syntax shape
 filter_upwards [V,f,Metric.tendsto_nhds.mp (h.hail_v f H W p u hD) (e/3) (by linarith)] with i hi hz ht; have hp:= dist_triangle (bore (v i) (R i) (z i) (A i)) (bore (v i) (R i) (z i) (sulk (v i) j (M i) (R i) D (A i))) (pencil Y)
 have hr:= dist_triangle (bore (v i) (R i) (z i) (sulk (v i) j (M i) (R i) D (A i))) (dun D Y) (pencil Y); have hh:= hi D hD _ _ _ hz; rw [← dist_eq_norm] at hh; linarith
end Yard
end YM.CF.Onyx
