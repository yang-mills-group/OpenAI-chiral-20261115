import YM.SU5.FiniteGaugeData.CodaT.Oriel
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
-- matching natural currencies for any wired bilinear (WP18). Does not need aligning at planar origins. We construct explicitly so basis signs checked on tiny wrapped endpoints, to read moving slope for this family stencil. Here `Spin10`/`δ5` each paid, upper/lower. Common law on gauge. -/
namespace Niagara
variable {x y a b:Cover}{u v:SpinIdx}
open Largo Mirage -- placeholder
open Dial -- tickA
open Cascade Ember Stationary MeasureTheory
namespace Chisel
variable (A:Chisel)
local notation "E"=> boundsEarth
local notation "μx"=> volume.restrict E
abbrev stage(N:Side)(M:Tulip.Male):ℂ := (∑ i:Site N, μWallet A M.val (mel i)) / ((N.val:ℕ):ℂ)^4
def scoreC(y:Gaia):ℂ:= angleK A (river y) (melody (river y))
abbrev finalIncome(A:Chisel):ℂ:= (cartWeight:ℂ) * ∫ x:Gaia, A.scoreC x ∂(volume.restrict boundsEarth)
lemma finalAt(M':Male)(h:Standing (tickA N) (spar 4 M' (1:Pane N))): (A.DesireB K).slope K 4 N M'= (dimf A.σ:ℂ)* A.stage N M':=by
 let P:= A.shiftSign N; have hp:= A.sumCost M' N h; change Relief.cup _ _ _= _; rw [show ((A.DesireB K).print N 1)=A.buyD N 1 from rfl,hp,mul_assoc, A.modeCost,←mul_sum]; unfold stage; rw [inv_mul_eq_div]; push_cast; rfl -- tune include M' declaration not retained.
lemma earth_pass {Y:Gaia}(h:Y≠0)(z:Y∈boundsEarth)(i:Cover): pass (river Y+reciprocal i) ≠ 0:= by
 let f(a:Axis):ℝ:=Y a+2*Real.pi*(i a:ℝ); let U:= river Y+reciprocal i; have ht(a:Axis): U a=↑(f a):=by unfold U f; rw [Pi.add_apply]; unfold river reciprocal; push_cast; rfl
 obtain ⟨a,p⟩:∃ a:Axis,Y a≠0:=by contrapose! h; exact PiLp.ext fun i=>h i
 have hp : f a≠0:= by
    obtain ⟨v,u⟩:= z a; change -Real.pi< Y a at v; change Y a≤_ at u; unfold f; rcases lt_trichotomy (i a) 0 with t | t | t;
    · have he: (i a:ℝ) ≤ -1:=by exact_mod_cast (by omega : i a ≤ -1)
      intro g; nlinarith [Real.pi_pos];
    · rwa [t,Int.cast_zero,mul_zero,add_zero]
    have he:1≤(i a:ℝ):=by exact_mod_cast (by omega : 1 ≤ i a)
    intro g; nlinarith [Real.pi_pos]
 change Largo.pass U≠0; unfold Largo.pass; simp_rw [ht,← Complex.ofReal_pow,←Complex.ofReal_sum]; exact_mod_cast (show ∑ i:Axis,(f i)^2≠0 from (lt_of_lt_of_le (sq_pos_of_ne_zero hp) (Finset.single_le_sum (fun _ _=> sq_nonneg _) (mem_univ a))).ne')
private lemma contour : ∃ C:ℝ,0<C∧∀ (M:Tulip.Male)(N:Side)(i:Site N), ‖μWallet A M.val (mel i)‖≤ C/‖bark i‖ := by
 obtain ⟨C,h,t⟩:= Cascade.chillY 4 (by norm_num); refine ⟨Real.sqrt C,Real.sqrt_pos.mpr h,fun M N i=>?_⟩
 let P:= mixL 4 M.val (mel i); let H:= shell 4 M.val (mel i); let y:=zen P; let u:ℝ:=∑ i,(P i).re^2; have hp:= mel_h i; let q:=bark i; have hq:0<‖q‖:=lt_of_lt_of_le (pinch_pos _) (Ember.torch _)
 have hu:physical P:=phys_mix _ _ M.property _ hp.1; have he : ‖y‖^2=u:=by
    rw [sq, ← CStarRing.norm_star_mul_self,show star y= -y from zenStar P hu, neg_mul,show y*y= _ from zenSq P, ← neg_smul,neg_neg,norm_smul,norm_one,mul_one,prodM_self _ hu,Complex.norm_real,Real.norm_of_nonneg (sum_nonneg fun i _=> sq_nonneg _)] -- neg_smul orientation?
 have hw:‖H⁻¹‖=1+u:=by unfold H; rw [shell_inv _ _ (base_subset_realCube zone_pos (mel_h i)) (mel_away _),inv_inv, prodM_self _ hu]; change ‖(1:ℂ)+(u:ℂ)‖=_; rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (add_nonneg zero_le_one (sum_nonneg fun _ _=> sq_nonneg _))]
 have ht:= t M N i; change ‖H⁻¹‖≤_ at ht; rw [hw] at ht;
 unfold μWallet angleK; rw [norm_mul, mode_real _ _ hp.1, one_mul]; refine le_trans (norm_entry _ _ _) ((norm_neg _).le.trans ((sq_le_sq₀ (norm_nonneg y) (by unfold q at hq; positivity)).mp ?_)); rw [he,div_pow,Real.sq_sqrt h.le, div_eq_mul_inv]; linarith
private def arbor {N:Side}(f:Site N→ℂ)(x:Gaia):ℂ:= (plants (fun i=> (f i).re) x:ℂ)+ Complex.I* (plants (fun i=> (f i).im) x:ℂ)
private lemma belongs(h:Even N.val)(f: Site N→ℂ): Integrable (arbor f) μx := Integrable.add (Integrable.ofReal (fortunate (fun i=>(f i).re) h)) (Integrable.const_mul (c:=Complex.I) (Integrable.ofReal (fortunate (fun i=>(f i).im) h))) -- maybe c implicit
private lemma arboretum_b{N:Side}(f:Site N→ℂ)(k:Site N){p:Gaia}(h:p∈cellH k):arbor f p=f k:=by unfold arbor; rw [flora _ k h,flora _ k h, mul_comm Complex.I]; exact Complex.re_add_im _
lemma arbX(h:Even N.val)(f:Site N→ℂ):cartWeight • (∫ p:Gaia,arbor f p ∂μx)=(∑ i:Site N,f i)/((N.val:ℂ)^4):=by
 let S:ℝ:=(N.val:ℝ)^4; have he:= belongs h f; have h0:((N.val:ℂ)^4)=(S:ℂ):=(by push_cast [S]; rfl);
 rw [h0,div_eq_inv_mul]; change _= (S:ℂ)⁻¹*_; rw [← Complex.ofReal_inv]; apply Complex.ext
 · rw [Complex.smul_re, Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero,Complex.re_sum]; rw [show (∫ p:Gaia,arbor f p ∂μx).re=(∫ p:Gaia,(arbor f p).re ∂μx) from (integral_re he).symm]; unfold arbor; simp only [Complex.add_re, Complex.ofReal_re,Complex.I_mul_re,Complex.ofReal_im,neg_zero,add_zero]; change cartWeight*_=_; rw [← fullF _ h]; unfold S; ring -- tune
 rw [Complex.smul_im, Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,Complex.im_sum,show (∫ p:Gaia,arbor f p ∂μx).im=(∫ p:Gaia,(arbor f p).im ∂μx) from (integral_im he).symm]; unfold arbor; simp only [Complex.add_im,Complex.ofReal_im,Complex.I_mul_im,Complex.ofReal_re,zero_add]; change cartWeight*_=_; rw [←fullF _ h]; unfold S; ring
abbrev environment(i:ℕ):Side:=⟨2*i+2,by omega⟩
private def plantQ (N:Side)(M:Male)(x:Site N):= μWallet A M.val (mel x)
private def planted(M:Male)(N:Side):Gaia→ℂ := arbor (plantQ A N M)
private lemma haunt (C:ℝ): Integrable (fun (i:Gaia)=>C/‖i‖) (volume.restrict boundsEarth):=by
 let F(i:Gaia):=C/‖i‖; have he:Module.finrank ℝ Gaia=4:=by simp [Gaia,Axis]
 let S: Set Gaia:=ball 0 (2*Real.pi+1)
 refine IntegrableOn.mono_set (t:=S) (integrableOn_ball_of_norm_le_rpow (μ:=volume) (f:=F) (C:=|C|) (α:=1) ?_ ?_ (Eventually.of_forall (fun i=> ?_)) ?_) (fun x v=>?_); -- order tune
 · rw [he]; omega
 · rw [he]; norm_num
 · unfold F; simp only [Real.norm_eq_abs, abs_div,abs_of_nonneg (norm_nonneg _),Real.rpow_neg (norm_nonneg _), Real.rpow_one,div_eq_mul_inv]; rw [abs_mul, abs_inv, abs_of_nonneg (norm_nonneg _)]
 · exact (show Measurable F by unfold F; fun_prop).aestronglyMeasurable
 exact Metric.closedBall_subset_ball (lt_add_one _) (earth_bounded _ v)
private lemma soul_cont : Continuous (fun p:Momentum × Momentum=> angleK A p.1 p.2):=by
 unfold angleK Laurent.mode Fir.zen; simp_rw [Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply]; fun_prop
private lemma river_cont : Continuous Ember.river := continuous_pi fun i=> show Continuous (fun x:Gaia=> (x i:ℂ)) by fun_prop
variable {N_:ℕ→Side}{M_:ℕ→Male}(g:Tendsto (fun i=>(M_ i).val.val) atTop atTop)(p:Tendsto (fun i=>(N_ i).val) atTop atTop)(e:∀ i,Even (N_ i).val)
local notation "Y"=> fun i=> planted A (M_ i) (N_ i)
omit g p in
private lemma tribe (e:∀ i,Even (N_ i).val):∀ᵐ x∂μx,x ≠ (0:Gaia) ∧ x∈ boundsEarth ∧ ∀ i:ℕ, ∃ k:Site (N_ i), x∈cellH k :=by
    refine Eventually.and ?_ ((ae_restrict_mem earth_meas).and ((ae_all_iff.mpr fun i=> ((Ember.arboretum (e i) earth_meas (_root_.le_refl E)).mono fun x p=>p.2))))
    exact ae_restrict_of_ae (by rw [ae_iff]; simp)
include g p
omit g in
private lemma βGoal (K:∀ i,Site (N_ i))(V:Gaia)(H:∀ i:ℕ, V∈cellH (K i)):Tendsto (fun i=>mel (K i)) atTop (𝓝 (river V)):=by
 let x:=V; have ht:Tendsto (fun i=> Ember.pinch (N_ i)) atTop (𝓝 0) := Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop.comp p) _ -- tune
 have hh:Tendsto (fun i=>bark (K i)) atTop (𝓝 V):= Metric.tendsto_nhds.mpr (fun ε h=> (ht.eventually (gt_mem_nhds (half_pos h))).mono (fun i hi=>by
    rw [dist_eq_norm]; apply lt_of_le_of_lt (proximity _ (H i)); change Ember.pinch (N_ i) <ε/2 at hi; linarith only [hi]));
 apply (river_cont.tendsto V |>.comp hh).congr' (Eventually.of_forall fun i=> (show _=_ from riverB (K i)))
private lemma puffA(K:∀ i,Site (N_ i))(V:Gaia)(c:V≠0)(X:V∈boundsEarth)(q:Tendsto (fun i=>mel (K i)) atTop (𝓝 (river V))): Tendsto (fun i=>plantQ A (N_ i) (M_ i) (K i)) atTop (𝓝 (scoreC A V)):=by
    let Q(i:ℕ):= mixL 4 (M_ i).val (mel (K i)); have he:Tendsto Q atTop (𝓝 (melody (river V))) :=  (by apply tendsto_pi_nhds.mpr; intro w; change Tendsto (fun i=> mixL 4 (M_ i).val (mel (K i)) w) atTop (𝓝 (melody (river V) w)); exact harmony (M:=fun i=>(M_ i).val) (fun i=> (M_ i).property) g q (fun j=> earth_pass c X j) w (Eventually.of_forall fun i=> mel_h (K i)))
    let f(i:Momentum × Momentum):= angleK A i.1 i.2; have hh:Continuous f:= soul_cont A; let Yc:=melody (river V); have ht:Tendsto (fun i=>(mel (K i),Q i)) atTop (𝓝 ((river V,Yc):Momentum×Momentum)):= q.prodMk_nhds he;
    change Tendsto (f ∘ fun i=>(mel (K i), Q i)) atTop (𝓝 (f (river V, Yc))); exact (hh.tendsto _).comp ht
private lemma bfull(V:Gaia)(c:V≠0)(X:V∈boundsEarth)(S:∀ i:ℕ,∃ k:Site (N_ i),V∈cellH k): Tendsto (fun i=>planted A (M_ i) (N_ i) V) atTop (𝓝 (scoreC A V)):=by
    let x:=V; have ht:Tendsto (fun i=> Ember.pinch (N_ i)) atTop (𝓝 0) := Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop.comp p) _ -- tune
    choose K H using S; unfold planted; have he(i:ℕ): arbor (plantQ A (N_ i) (M_ i)) V = plantQ A (N_ i) (M_ i) (K i):=arboretum_b _ (K i) (H i); simp_rw [he] -- dependent
    exact puffA A g p K V c X (βGoal p K V H)
omit g p
private lemma won (C:ℝ)(M:Tulip.Male)(N:Side)(hc:0<C)(t:∀ i:Site N, ‖μWallet A M.val (mel i)‖≤ C/‖bark i‖)(x:Gaia)(c:x≠0)(k:Site N)(hk:x∈cellH k): ‖planted A M N x‖≤ 3*C/‖x‖:=by
 let B:=bark k; change ‖arbor _ x‖≤_; rw [arboretum_b _ _ hk]; refine (t k).trans ?_; have hx:= norm_pos_iff.mpr c; have hp:0 < ‖B‖:= lt_of_lt_of_le (pinch_pos _) (Ember.torch _); rw [_root_.div_le_div_iff₀ hp hx]; have he: ‖x‖≤3*‖B‖:=by
   have he:= norm_sub_norm_le x B; rw [norm_sub_rev x B] at he; linarith only [he,proximity _ hk,Ember.torch k]
 exact (mul_le_mul_of_nonneg_left he hc.le).trans_eq (by ring) -- careful duplicate let
include p e g
lemma authorized : Integrable (A.scoreC) (volume.restrict boundsEarth) ∧ Tendsto (fun i=>A.stage (N_ i) (M_ i)) atTop (𝓝 (A.finalIncome)):=by
 obtain ⟨C,hc,t⟩:= contour A; have ht:Tendsto (fun i=> Ember.pinch (N_ i)) atTop (𝓝 0) := Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop.comp p) _ -- tune defin unfolding
 let P:= Y; let V:= volume.restrict boundsEarth; have hi: (∀ j,Integrable (P j) V):=fun j=> belongs (e j) _
 have hp:=tribe e
 let F(x:Gaia):=3*C/‖x‖; have ha:Integrable F V:=haunt (3*C)
 have hb:∀ᵐ x∂V,∀ i,‖P i x‖ ≤ F x:=hp.mono fun x ⟨c,X,S⟩ i=> won A C _ _ hc (t _ _) x c (S i).choose (S i).choose_spec
 have hm:∀ᵐ x∂ V, Tendsto (fun i=>P i x) atTop (𝓝 (scoreC A x)):= hp.mono fun x ⟨c,X,S⟩=> bfull A g p x c X S
 refine ⟨Integrable.mono' ha (_root_.aestronglyMeasurable_of_tendsto_ae atTop (fun i=> (hi i).aestronglyMeasurable) hm) ((hb.and hm).mono (fun x ⟨g,h⟩=> le_of_tendsto h.norm (Eventually.of_forall g))),?_⟩
 let Z:=tendsto_integral_of_dominated_convergence F (fun i=> (hi i).aestronglyMeasurable) ha (fun i=> hb.mono fun x h=> h i) hm; apply Tendsto.congr' _ (Z.const_mul (cartWeight:ℂ)); exact Eventually.of_forall fun i=>by
    dsimp only; rw [← Complex.real_smul]; exact arbX (e i) _ -- fin.
end Chisel
end Niagara
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
