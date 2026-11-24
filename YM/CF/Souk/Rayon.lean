import YM.CF.Souk.Rate
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort MeasureTheory AnalyticBridge.RelativeLogdet
open Next.SectorChange PatchReads Next.SectorChange.Wisps Summit
variable{z z': Fish ι→ℝ}{p:ChartRatio G} {M:ℝ}{k:S.Choices}
lemma rate_b (p:0<t)(f:E→B)(h:ContDiffAt ℝ n (fun y:E=> f (t• y)) 0):ContDiffAt ℝ n f 0:=by
 let L(y:E):=t⁻¹ • y; let F(y:E):=f (t• y); have hl:L 0=0:=smul_zero _
 apply ((show ContDiffAt ℝ n F (L 0) from hl.symm ▸ h).comp (f:=L) _ (contDiffAt_id.const_smul _)).congr_of_eventuallyEq; filter_upwards with i; exact (congr_arg f (smul_inv_smul₀ p.ne' i)).symm
lemma token(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(l:ℕ)(hl:l ≤18)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind 5) :∃ C:ℝ,0 ≤ C ∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio),Cert P K S T x→ sizedP G P K S T F → ∀ (k:S.Choices)(q:Chi)(M:ℝ)(j:Fin 2→Primary c G),
 let L(y:Mast G c):= Real.log (μ₁ T F x k q M 1 l y).det - tallyX T x F k q M l (facadeX G y)
 ContDiffAt ℝ 2 L 0 ∧ |Uniform.entry L 0 j| ≤ C*(raised G P.L ((l+52)*radiusB x))*(radiusB x:ℝ)^27*temp x:=by
 obtain ⟨θ,C,u,v,Q,D,hθ,hC,hu,hv,hQ,h⟩:=jumpW K P 3 l (by decide) hl p W
 have ht : Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 let L(b):=composeCost 2 b (Uniform.shade G); have he(b x): L (b*lamp x)= L b * lamp x:=by unfold L composeCost; ring
 have ha(b:ℝ):∀ᶠ x in atTop,L (b*lamp x) ≤1/2:= by simp_rw [he]; exact (show Tendsto (fun x=> L b * lamp x) atTop (𝓝 0) by simpa using lamp_s.const_mul (L b)).eventually (ge_mem_nhds (by norm_num))
 let A(b):=40000*(L b)*(L b)^3; let B:=A C+A Q+A D; refine ⟨max 0 B,le_max_left ..,?_⟩
 filter_upwards [h, reserve K P, ha C,ha Q,ha D, Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, eventually_gt_atTop (0:ℝ), Newt.smallF (n:=1) hv 1,Newt.smallF (n:=1) hθ 1, lamp_s.eventually (ge_mem_nhds zero_lt_one)] with x h he' hc hx hy hB hX hQ' hθ' heL
 intro c f S T F hP h₀ k q M j f'; let Y:=bareStores S; obtain ⟨hg,hU⟩:= h.2.2.2 S T Y F (1:Config G c) hP (PhysicalNext.JointLoad.Heir.noFlags ..).symm h₀ k; obtain ⟨hh,hv'⟩:=hU q M 1; let t:=temp x; have ht:0<t:= Work.E09.temp_pos hX
 have hp {v:ℝ}(h:0<v)(hp:Real.exp (-v*Stores.till x)*1 ≤ t^1): tipPay v x ≤ lamp x:=by
    rw [mul_one,pow_one] at hp; apply le_trans _ (hp.trans (le_mul_of_one_le_left ht.le (one_le_pow₀ (show (1:ℝ)≤radiusB x by exact_mod_cast (show 1 ≤ radiusB x from by omega))))) -- tune
    apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr h.le); exact_mod_cast (show Stores.till x ≤ radiusB x/60 by unfold Stores.till; omega)
 obtain ⟨hm,hY⟩:=charm (he' S T hP.got hP.size hP.funds.1) hB hg hh hv' hC.le (hp hθ hθ') (hp hv hQ') hc hx hy heL j
 let E:=raised G P.L ((l+52)*radiusB x); have hF:0≤ E:=by unfold E raised; positivity
 let U(y:Mast G c):=f' (t•y); have hh':U=(fun y=>Real.log (μ₁ T F x k q M (temp x) l y).det-tallyX T x F k q M l (facadeX G (temp x • y))):=by funext j; unfold U f' μ₁; rw [one_smul]
 have hu: ContDiffAt ℝ 2 f' 0:= by
    have hu:ContDiffAt ℝ (2:ℕ) f' 0:=rate_b ht _ (show ContDiffAt ℝ (2:ℕ) U 0 from hh'.symm ▸ (hm.of_le (by norm_num))); simpa using hu
 have ht' : |Uniform.entry U 0 j|≤ B*E*(lamp x)^3:=by
    rw [hh']; apply hY.trans; dsimp only; rw [hP.got]; apply le_of_eq; unfold B A L lamp composeCost; ring -- tune (unfold order)
 refine ⟨hu,?_⟩; unfold U at ht'; rw [entry_scale f' t _ 0 (show ContDiffAt ℝ (2:ℕ) f' (t •0) from by rw [smul_zero]; exact hu.of_le (by norm_num)),smul_zero,smul_eq_mul,abs_mul,abs_of_pos (pow_pos ht _)] at ht'; apply le_of_mul_le_mul_left _ (pow_pos ht 2); apply ht'.trans; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 0 B) hF) ?_); exact le_of_eq (by unfold E t lamp; ring)
 unfold lamp; exact pow_nonneg (mul_nonneg (by positivity) ht.le) _
def golden (T:Tube G S)(F:Forest S.ratio)(k:S.Choices)(p:ChartRatio G)(q:Chi)(t a x:ℝ)(l:ℕ)(y:Mast G c): ℝ:=
 let z:= flute F (sol S T k x F l) 1 y
 inLoop (safeD T.up (Stores.till x)).loop F z - tallyX T x F k q t l (facadeX G y) - addH F p z - draft a (safeD T.down (Hors.cart x S.patch.L)) T.low (tint G _ y)
lemma finish_r (h:ContDiffAt ℝ 2 z 0)(hp:ContDiffAt ℝ 2 z' 0)(j:Fin 2→ι)(he:|Uniform.entry z 0 j| ≤ C)(hg:|Uniform.entry z' 0 j| ≤ Q):|Uniform.entry (z+z') 0 j| ≤ C+Q:=by unfold Uniform.entry; rw [iteratedFDeriv_add_apply (h.of_le (by norm_num)) (hp.of_le (by norm_num)), _root_.add_apply]; exact (abs_add_le ..).trans (add_le_add he hg)
lemma hercule (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(l:ℕ)(hn:1 ≤ l)(hl:l ≤18)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind 5) (hG:G.Simple)(J:ChartRatio G)(hO:LocalRatio J)(Θ v Λ:ℝ):
 ∃ B C D:ℝ,0<B∧0≤C∧0≤ D∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio),Cert P K S T x→sizedP G P K S T F→ T.up.Bounds T.high K.top.width K.top.paths Λ→ T.down.Bounds T.low K.below.width K.below.paths Λ →∀ α:ℝ,(∀ z,Critical F T.high T.up z→ FiniteBound F T.up T.down T.high T.low α J z Θ v 1)→ ∀(k:S.Choices)(q:Chi)(a:ℝ)(j:Fin 2→Primary c G),
 let N:=raised G P.L ((l+52)*radiusB x)
 let f:=golden T F k J q a α x l
 ContDiffAt ℝ 2 f 0 ∧ |Uniform.entry f 0 j| ≤ B*(N+1)*(radiusB x:ℝ)^27*temp x + (Fintype.card (Site c):ℝ)*Θ*Real.exp (-v*c.val) + (C*|α|+D)*tollE K.below.width (Hors.cart x S.patch.L):=by
 obtain ⟨X,hX,H₀⟩:= hive K P p hG l hn hl W J hO Λ; obtain ⟨Y,hY,H₁⟩:=token K P p l hl W; obtain ⟨U,hU⟩:=Uniform.paint_supply G 2
 let s:=K.below.width; let L:= Stationary.gramCost G K.below.paths; let C:= stip G 1 2 U s; refine ⟨X+Y,|L*C|,|Λ*C|,add_pos_of_pos_of_nonneg hX hY,abs_nonneg _,abs_nonneg _,?_⟩
 filter_upwards [H₀,H₁] with x h₀ h₁ c f S T F hr ht hp hv α hA k q a j N f'
 obtain ⟨z,hz,hQ⟩:=h₀ S T F hr hp ht; let V:=gateY J T F x k q a l; let m(y:Mast G c):= thermal F k T.high T.up z J (tint G _ y); let K'(y:Mast G c):=draft α T.down T.low (tint G _ y); let L'(y:Mast G c):=draft α (safeD T.down (Hors.cart x S.patch.L)) T.low (tint G _ y)
 obtain ⟨he,hu⟩:= hQ k q a j; let R(y:Mast G c):= Real.log (μ₁ T F x k q a 1 l y).det - tallyX T x F k q a l (facadeX G y)
 obtain ⟨hf,hE⟩:=h₁ S T F hr ht k q a j; obtain ⟨hT,hT'⟩:= bearerX (T:=T) (k:=k) (hA z hz.critical) j; rw [mul_one] at hT'; let Q:=m-K'; have hS : ContDiffAt ℝ 2 Q 0:= hT.of_le le_top
 obtain ⟨hb,hb'⟩:= cap_f hv hU (show 2 ≤ c.val by have hh:=hr.size; omega) α (Hors.cart x S.patch.L) j
 let W:=V-m; have hx: f'=W+R+Q+(K'-L'):=by ext y; simp only [f',golden,W,V,gateY,R,Q,Pi.add_apply,Pi.sub_apply]; unfold K' L'; abel
 rw [hx]; let S':=K'-L'; have hg:ContDiffAt ℝ 2 S' 0:= hb.of_le le_top; have hw:ContDiffAt ℝ 2 (W+R) 0:= ContDiffAt.add (g:=R) he hf
 have ht:|Uniform.entry (W+R) 0 j| ≤(X+Y)*(N+1)*(radiusB x:ℝ)^27*temp x:=(finish_r (z:=W) (z':=R) he hf j hu hE).trans (by
    have h0: 0≤ N:=by unfold N raised; positivity
    have hX':0≤temp x:=Work.E04.temp_nonneg _
    let R(a b:ℝ):=a*b*(radiusB x:ℝ)^27*temp x; have hp:R Y N ≤ R Y (N+1):=by unfold R; gcongr; linarith only
    exact (add_le_add (le_refl (R X (N+1))) hp).trans (le_of_eq (by unfold R N; ring))
 )
 have hp: |Uniform.entry S' 0 j|≤ (|L*C| *|α|+|Λ*C|)*tollE K.below.width (Hors.cart x S.patch.L):=by
    apply hb'.trans; apply le_trans ?_ (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self (L*C)) (abs_nonneg _)) (le_abs_self ..)) (Real.exp_pos _).le); exact le_of_eq (by unfold L C s; ring)
 refine ⟨(hw.add hS).add hg,finish_r (hw.add hS) hg j (finish_r hw hS j ht hT') hp⟩
end YM.CF.Souk
