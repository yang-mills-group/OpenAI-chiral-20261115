import YM.CF.BPress.Wealth.Swell
/-! Taylor on any single four arguments in a channel. Key bc second derivative scale a_A. Uniform in y (eventual); no volume. Uses fixed B-data physics of plaquette. Normalize embedding into matrix Hilbert space (Frobenius).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
abbrev ink := group.Color
abbrev matY := group.Mat
abbrev Arg := Fin 4→ ink
local notation "loc" => 𝓝 (0:ℝ)
variable (v:Signed)(i:PlaqAxes)
abbrev scr := group.colorScale
/-- normalized norm price is in chord. Lie `ψ` colors normalized *with* generators. -/
def canonE : ink →ₗᵢ[ℝ] matY where
 toLinearMap:= scr⁻¹ • group.colorMat
 norm_map' x:=by change ‖scr⁻¹ • group.colorMat x‖=_; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr group.colorScale_pos.le),group.colorMat_norm, show group.colorScale=scr from rfl, inv_mul_cancel_left₀ group.colorScale_pos.ne']
def canonM (U:E) : matY:= scr⁻¹ • (group.mat U-1)
lemma canonM_price (U:E) : ‖canonM U‖=group.chord U:=by unfold canonM; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr group.colorScale_pos.le), inv_mul_eq_div]; rfl
lemma canonM_dist (U V:E) : dist (canonM U) (canonM V)=chord U V:=by
 unfold canonM; rw [dist_eq_norm, ←smul_sub, sub_sub_sub_cancel_right,norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr group.colorScale_pos.le), inv_mul_eq_div,chord.mat_eq] -- tune
private lemma cont_panel : ContDiff ℝ ω fun x: ℝ× Arg=> canonM (panel v i x.1 x.2):=by
 have h(k) : ContDiff ℝ ω (fun x:ℝ×Arg=> group.mat (review v (colorDir i k) x.1 (x.2 k))):=by
    unfold review rollA; split_ifs <;> simp_rw [group.mat_mul] <;> apply ContDiff.mul <;> (apply group.exp_jet.comp; fun_prop)
 unfold canonM panel readA; simp only [group.mat_mul,group.mat_inv]; apply ContDiff.const_smul (c:=scr⁻¹); apply ContDiff.sub _ contDiff_const; apply ContDiff.mul; swap; · exact (starL' ℝ).contDiff.comp (h _)
 exact (((h 0).mul (h 1)).mul ((starL' ℝ).contDiff.comp (h 2))) -- tune
private def panelD := fderiv ℝ (fun x: ℝ × Arg=> canonM (panel v i x.1 x.2)) 0
private lemma panelD_slot (w:Arg): panelD v i (0,w)=canonE (circle w):=by
 let f:= fun x: ℝ × Arg=> canonM (panel v i x.1 x.2); let H(x:ink)(t:ℝ):= group.mat (group.lieExp (t • x)); let Y:= (0,w);
 have h:HasDerivAt (fun t:ℝ=> canonM (panel v i 0 (t • w))) (panelD v i (0,w)) 0:= by
    let X:ℝ →(ℝ × Arg):= fun t=> (0,t • w); have hx :=(hasDerivAt_const (0:ℝ) (0:ℝ)).prodMk ((hasDerivAt_id' (0:ℝ)).smul_const w); have ht:HasDerivAt X (0,w) (0:ℝ):=by convert! hx using 1; simp
    exact ((cont_panel v i|>.differentiable (by simp)|>.differentiableAt (x:=X 0)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ht)|>.congr_deriv (by simp [X,panelD, (show ((0:ℝ),(0:Arg))=0 from rfl)]; rfl) -- tune
 have g(x:ink): HasDerivAt (H x) (group.colorMat x) 0:=by
    unfold H; simp_rw [group.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (group.colorMat x) (0:ℝ) -- namespace
 apply h.unique; have hv(k:Fin 4)(t:ℝ): group.mat (review v (colorDir i k) 0 ((t • w) k))=H (w k) t:=by unfold review rollA; split <;> simp [H]; -- tune
 simp only [panel,readA,canonM,group.mat_mul,group.mat_inv]; simp_rw [hv]; let x:= w 0; let y:= w 1; let z:=w 2; let q:= w 3; let Z := g x; let D:= ( ((((g x).mul (g y)).mul (g z).star).mul (g q).star).sub (hasDerivAt_const (0:ℝ) (1:matY))).const_smul scr⁻¹
 apply D.congr_deriv; have he(x:ink) : H x 0=1:=by simp [H]
 simp only [Pi.mul_apply, he,mul_one,one_mul,star_one,sub_zero]; simp [canonE,circle,x,y,z,q,group.colorMat_skew]; simp only [smul_add,smul_sub]; abel -- tune orientation

def finer (y:ℝ) := aA y*temp y + temp y^2 + xi y
lemma finer_pos {y:ℝ}(p:0<y): 0<finer y:= by unfold finer; positivity [temp_pos p,aA_positive p,xi_pos p]
lemma p_norm (w:Arg){l:ℝ}(p:‖w‖ ≤ l): ‖circle w‖ ≤ 4*l:=by
 apply le_trans (norm_sub_le ..); apply le_trans (add_le_add (norm_sub_le ..) le_rfl); apply le_trans (add_le_add (add_le_add (norm_add_le ..) le_rfl) le_rfl); have ht:= pi_norm_le_iff_of_nonneg ((norm_nonneg w).trans p)|>.mp p; linarith only [ht 0,ht 1,ht 2,ht 3]

private lemma panel_taylor (D:ℝ)(p:0<D) : ∃ C:ℝ, 0<C ∧ ∀ᶠ y in atTop, ∀ z:Arg, ‖z‖ ≤ D*temp y →
 ‖canonM (panel v i (aA y) z)-canonM (panel v i (aA y) 0) - canonE (circle z)‖ ≤ C* (aA y*temp y+ temp y^2):=by
 obtain ⟨δ,C,k,t,u⟩:= taylor_change (0: ℝ×Arg) (cont_panel v i).contDiffAt (((cont_panel v i).differentiable (by simp) (0: ℝ×Arg)).hasFDerivAt)
 refine ⟨ C*(D+D^2),by positivity,?_⟩; filter_upwards [((npl_aA.add (npl_temp.const_mul D)).drop.eventually (gt_mem_nhds k)),eventually_gt_atTop (0:ℝ)] with y g a z h; let S:=aA y; let w:=temp y; let r:= S+D*w; have hs:0≤S:=(aA_positive a).le; have hp:0<w:=temp_pos a; have vt:r<δ:=g; have ht:S≤r:=le_add_of_nonneg_right (mul_nonneg p.le hp.le); let x:=(S,z); let y':=(S,(0:Arg)); have he(z:Arg)(v:‖z‖ ≤ D*w): (S,z)∈ Metric.closedBall (0:ℝ×Arg) r:= by rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def]; exact max_le ((Real.norm_of_nonneg hs).le.trans ht) (v.trans (le_add_of_nonneg_left hs))
 have f:= u r vt _ (he z h) _ (he 0 (by rw [norm_zero]; positivity)); have hx: x-y'=(0,z):=Prod.ext (sub_self _) (sub_zero _); change ‖canonM (panel ..)-canonM (panel ..)-panelD v i (x-y')‖≤ C*r*‖x-y'‖ at f -- tune panel ..
 rw [hx, panelD_slot,Prod.norm_def] at f; simp only [norm_zero,sup_eq_right.mpr (norm_nonneg _)] at f; change _ ≤ C*(D+D^2)*(S*w+w^2); refine f.trans ( (mul_le_mul_of_nonneg_left h (mul_nonneg t.le (hs.trans ht))).trans ?_); change C*(S+D*w)*(D*w) ≤ _; nlinarith only [mul_nonneg (mul_nonneg t.le (show 0≤ D^2 by positivity)) (mul_nonneg hs hp.le),mul_nonneg (mul_nonneg t.le p.le) (sq_nonneg w)] -- tune

private lemma panel_t0 : ∃ C : ℝ, 0<C ∧ ∀ᶠ y in atTop, ‖canonM (panel v i (aA y) 0)- mA y • canonE (psi v i)‖ ≤ C*aA y^3:=by
 obtain ⟨k,h,F⟩:= chord.panel_price (oriDir v i.val.1) (oriDir v i.val.2)|>.exists_pos; refine ⟨scr⁻¹*k,by positivity [show 0<scr from group.colorScale_pos],?_⟩; filter_upwards [npl_aA.drop.eventually F.bound, eventually_gt_atTop (0:ℝ)] with y v h; rw [panel_bg]; let k:=k -- tune
 unfold canonM; change ‖scr⁻¹ • _- _ • (scr⁻¹ • group.colorMat (psi _ _))‖ ≤_; rw [smul_comm (mA y),←smul_sub, ← aA_sq h,norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr group.colorScale_pos.le)]; rw [norm_pow,Real.norm_of_nonneg (aA_positive h).le] at v; exact (mul_le_mul_of_nonneg_left v (inv_nonneg.mpr group.colorScale_pos.le)).trans_eq (mul_assoc ..|>.symm)

-- template proof with price read from all orientations finite maxima. canonical links + C ξ noise, four added. can pass smaller constants. separately norm & Bool etc.
set_option maxRecDepth 4000 in
theorem panel_purchase (D : ℝ)(p: 0<D): ∃ C : ℝ, 0<C ∧ ∀ᶠ y in atTop,∀ (v:Signed)(i:PlaqAxes), let A:=panel v i (aA y) 0
    ‖psi v i‖ ≤ C ∧ ‖canonM A - mA y • canonE (psi v i)‖ ≤ C*aA y^3 ∧ ∀ (z:Arg)(t:E), ‖z‖ ≤ D*temp y → chord t (panel v i (aA y) z) ≤ 4*xi y→ ‖canonM t-canonM A-canonE (circle z)‖ ≤ C*finer y:=by
 choose C h l using fun i v=> panel_taylor v i D p; choose B k H using fun i v=> panel_t0 v i
 let f (i:Signed×PlaqAxes):= C i.2 i.1+B i.2 i.1+ ‖psi i.1 i.2‖; let K:= ∑ i,f i; have he(i) : 0 ≤ f i:= by unfold f; positivity [h i.2 i.1,k i.2 i.1]
 have hx(i) : f i≤K:=single_le_sum (fun i _=> he i) (mem_univ i); refine ⟨K+4,by have he:=sum_nonneg (s:=univ) fun i _=> he i; positivity,?_ ⟩; filter_upwards [eventually_gt_atTop (0:ℝ), eventually_all.mpr (fun i:PlaqAxes=>eventually_all.mpr (fun v:Signed=>(l i v).and (H i v)))] with y a g v i; intro A; have hf:= hx (v,i); dsimp only [f] at hf; have b := (h i v); have he:= k i v; have hh:0 ≤ ‖psi v i‖:= norm_nonneg _; have ht:=temp_pos a; have hy:=aA_positive a; have hh':=xi_pos a; refine ⟨by linarith,le_trans (g i v).2 (mul_le_mul_of_nonneg_right (by linarith only [hf,b,hh] : B i v≤K+4) (by positivity)),fun z t h k=>?_⟩; have he : ‖canonM t-canonM (panel v i (aA y) z)‖ ≤ 4*xi y:=by rw [←dist_eq_norm, canonM_dist]; exact k
 let F':=canonM (panel v i (aA y) z); rw [show canonM t-canonM A-canonE (circle z)=(canonM t-F')+(F'-canonM A-canonE (circle z)) from (by abel)]
 apply (norm_add_le ..).trans ((add_le_add he ((g i v).1 z h)).trans ?_); unfold finer; -- nonlinear cross
 have hv:C i v≤K:=by linarith
 nlinarith [mul_le_mul_of_nonneg_right hv (show 0≤aA y*temp y+temp y^2 by positivity)]
end YM.CF.BPress.Wealth
