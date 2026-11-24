import YM.SU5.Gleam.Innate
import YM.SU5.Regis.Trophy
/-! # Blocking permissions with width-independent thresholds when right width choice made. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
local notation "B" x:max=> (height x:ℝ)
lemma descends (J:ChartRatio G)(D:LocalRatio J)(t:ℝ)(p:0≤t)(b:ℝ)(h:0≤ b):∃ A>(0:ℝ),∀ᶠ x:ℝ in atTop,∀ β:ℝ, x/2≤ β → β ≤ 2*x → descendCost J β t b ≤ A* (height x:ℝ):=by
 obtain ⟨A,u,V⟩:=margin_fee J D t p; let C':=(Fintype.card G.ColorIndex:ℝ)/2+b; have he:0≤C':=by unfold C'; positivity; -- fine
 refine ⟨A+C',by positivity,?_⟩; filter_upwards [V,Work.E08.eventual_radiusB 1] with x u h β a p; unfold descendCost; rw [add_assoc,add_mul]; exact add_le_add (u β a p) (le_mul_of_one_le_right he (show 1≤(height x:ℝ) from Nat.one_le_cast.mpr h))
lemma jewel (k: Clip)(R: Rules G)(D:LocalRatio J)(t:ℝ)(L:Side)(p:0<η)(g:0≤C)(S:ℝ)(h:0 ≤ t)(κ e:ℝ)(r:0<e)(R0:ℝ)(hr:0 ≤ R0) : ∀ᶠ x:ℝ in atTop, ∀ w:Side, Odd w.val → moder (height x) w.val L→ ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ (n c:Side)(R':Ratio c n),2*(R'.count.val+1)<n.val → R'.count=w → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B':Z.Bounds k η C S){μ a:ℝ}(q:Floor H k n μ a),0<μ → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ t) → ∀ (τ Q R₁ R₂:ℝ) {φ:Config G n→ℝ}, Envelope φ → GaugeInvariant φ → ∀ (W:Altar G n→ℝ), ContDiff ℝ 1 W → (∀ i,|W i| ≤ R₁) → (∀ i, ‖fderiv ℝ W i‖ ≤ R₂) → (∀ a:Support c, SceneLease B' P p' R' (height x) β (pace L x) (Q+R0*trap R' (height x) a) a τ φ W) → (∫ U:Config G n,richG Z k p' β κ U * Real.exp (τ * φ U) ∂prior G n) ≤ Real.exp (Roof J β n H + e*Fintype.card (Site n)+ Q + plumeCost B' P W τ + Regis.trend*R₂^2*τ^2):=by
 let u:=e/8; have he:0<u:=div_pos r (by norm_num); obtain ⟨A,hA,hX⟩:=descends J D t h R0 hr; filter_upwards [soothe k R D κ A u hA.le he L,hX, (shown k R L p g S).eventually (ge_mem_nhds he), eventually_gt_atTop 0,taller A L u hA.le he] with x hu hf hT hx t' w l H p' β hβ vP n c X wX wL H Z V B' μ a q h₁ d τ Q B1 B2 φ p3 g1 W0 p4 hb1 hb2 bnd
 let v:=X.count; have he':Odd X.count.val:=(show X.count=w from wL).symm ▸ l; have ht: moder (height x) X.count.val L:=wL.symm ▸ ‹moder _ _ _›; -- ht H shadowed
 let W:= height x; let J':= pace L x; let F:= descendCost J β t R0
 obtain ⟨hh,hM⟩:= t' v.val he' ht; have hv: F ≤ A * B x:= hf β hβ.1 hβ.2
 refine (harvest_slate B' V q D (hu _ ht _ p' hβ.1 vP) wX p3 p4 hb1 hb2 hr (show Odd X.count.val from he') hh d h₁ ((half_pos hx).trans_le hβ.1) h g ?_ g1 bnd).trans (Real.exp_monotone ?_)
 · unfold soot; gcongr
 unfold rentRoom; let N:ℝ:= Fintype.card (Site n); let M:ℝ:=Fintype.card (Site c); let t:= largerBill v.val (hallBill W); have hz:0≤N:=by unfold N; positivity
 have hp:0≤M:=by unfold M; positivity
 have hN:N=M*(v.val:ℝ)^4:=by unfold N M v; rw [site_card,site_card,X.exact_size]; push_cast; ring
 have hu':= mul_le_mul_of_nonneg_left hM hp; have hm: taxΔ R k n p' β J' η C S W ≤ u*N:= (bill_simpl L k hβ.2 vP R g hx.le).trans (mul_le_mul_of_nonneg_right hT hz); -- tune binder r'

 let w:ℝ:=v.val; change M*(4*(A*B x)*t+_)≤ M*(u*w^4) at hu'; have ht:= le_trans (show 4*F*M*t ≤ M*(4*(A*B x)*t) from ?_) (le_refl _); swap; · have hh:0 ≤ (t:ℝ):=Nat.cast_nonneg _; nlinarith only [mul_le_mul_of_nonneg_left hv (show 0 ≤ M*(t:ℝ) from mul_nonneg hp hh)]
 unfold u at *; change N=M*w^4 at hN; change Roof J β n H + (taxΔ R k n p' β J' η C S W + 4*(e/8)*N+4*F*M*t) + _ + _+ _ + Real.log 2*M ≤ _;
 change taxΔ R k n p' β J' η C S W ≤ _ at hm; nlinarith only [ht,hN,hm,hu',hz,mul_nonneg r.le hz,mul_le_mul_of_nonneg_left hN.le r.le,mul_le_mul_of_nonneg_left hN.ge r.le]
end clocks
private lemma on_wind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))
variable (B:Z.Bounds q η C S) {φ:Config G n→ℝ}(u: Envelope φ)
include B u in
lemma forEach (ξ:ℝ)(t:ℝ)(hh:∀ d: Signed,(∫ x:Config G n, richG Z q p β κ x *Real.exp (t*φ (pull d 0 x)) ∂prior G n) ≤ ξ) : (∫ x:Config G n, angBill Z q p β κ x * Real.exp (t*φ x) ∂prior G n) ≤ ξ := by
 let M:ℝ:=Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 let w:= M⁻¹; let S:=angBill Z q p β κ (n:=n); let F (s: Signed) (x:Config G n):= richG Z q p β κ x * Real.exp (t*φ (pull s⁻¹ 0 x)); let X:=prior G n; let Φ(s:Signed)(x:Config G n ):=F s (pull s 0 x)
 have hw:∑ _:Signed,w=1:= by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 have E(i:Signed) : Envelope (F i):=(income_g B).mul ((fun p:Envelope (fun x:Config G n=> φ (pull i⁻¹ 0 x) )=>expEnv p t) ⟨u.meas.comp (by apply (prior_pull _ _).measurable), u.cost.choose,fun _=> u.cost.choose_spec _⟩); let G'(x: Config G n):= ∑ i: Signed,w*Φ i x
 have he(i:Signed): Integrable (fun x=>w*Φ i x) X:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable ((E i).integrable X)).const_mul w
 have hf:Integrable G' X:= integrable_finsetSum _ (fun i _=> he i)
 refine le_trans (integral_mono (show Integrable _ _ from ((env_ang (n:=n) (p:=p) (κ:=κ) (β:=β) B).mul (expEnv u t)).integrable X) hf ?_) ?_
 · intro x; let f(s:Signed):= Z.principal q p β (pull s 0 x); let g:= κ*(misdemean p.threshold x).card; let e(s:Signed):= -f s+g + t*φ x; have ht(i:Signed): Φ i x=Real.exp (e i ):=by unfold Φ F richG e; rw [on_wind, pull_pull]; simp [affine,Real.exp_add]; ring -- maybe
   unfold G'; simp_rw [ht]; let tt:= (convexOn_exp.map_sum_le (w:=fun _ : Signed=>w) (fun i _=> inv_nonneg.mpr hM.le) hw (fun s _ => Set.mem_univ (e s)))
   rw [←Real.exp_add]
   change Real.exp _ ≤ ∑ i,w • _; apply tt.trans'; refine Eq.le (congrArg Real.exp ?_); unfold e; simp only [smul_eq_mul,mul_add,sum_add_distrib, mul_neg,sum_neg_distrib, ← mul_sum, sum_const, card_univ,nsmul_eq_mul]; change -(w*∑ s,f s)+ g + t*φ x= -(w*∑ s,f s)+ w * (M*g) + w * (t*(M*φ x)); rw [mul_left_comm t M, inv_mul_cancel_left₀ hM.ne', inv_mul_cancel_left₀ hM.ne'] -- order
 unfold G'; rw [integral_finsetSum _ (fun i _=> he i)] -- signature lemma
 have h(i:Signed):(∫ x:Config G n, w*Φ i x∂X)=w*∫ x,F i x∂X:=by rw [integral_const_mul]; refine congrArg (w * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂X from (by have ht:= integral_map (μ:=prior G n) (f:=F i) t.measurable.aemeasurable (show AEStronglyMeasurable (F i) _ from (E i).meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht))
 simp_rw [h]; refine (Finset.sum_le_sum (g:=fun _=> w*ξ) (fun i _=>?_)).trans_eq ?_; · exact mul_le_mul_of_nonneg_left (hh i⁻¹) (by unfold w; positivity)
 rw [← Finset.sum_mul,hw,one_mul]
end YM.Gleam
#print axioms YM.Gleam.clocks.jewel
#print axioms YM.Gleam.forEach
