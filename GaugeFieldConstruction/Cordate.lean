import YM.SU5.Fineness.Resource
import YM.CF.Wray.Frost
import GaugeFieldConstruction.Cobalt
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 108000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
set_option linter.unusedVariables false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}

/- P1. Lengths here at the same Trough as review estimates. -/
section cyan
open Fineness
abbrev fourthDeck (x:ℝ) := (Real.sqrt (Real.sqrt x))⁻¹
lemma fourthDeck_price (x:ℝ) (h:0≤x) : fourthDeck x = x^(-(1/4):ℝ):= by
 rw [Real.rpow_neg h]; unfold fourthDeck; congr 1; rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,← Real.rpow_mul h]; norm_num

lemma deckL (m:Side): ∀ x, x≤Scales.y SU.group m x := by
 intro x
 exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos Thera.yet_one).le (Real.log_nonneg (Nat.one_le_cast.mpr m.property)))

lemma size_fourth {L:Side}{F:ℝ→ℝ} (hF:Fief.sizeK L 1 F) (c:ℝ) (hc:0<c):∀ᶠ x in atTop, |F x| ≤ c*fourthDeck x:=by
 let y:=Scales.y SU.group L; let g:=Scales.g SU.group L; let p:=Scales.p SU.group L
 obtain ⟨H,h⟩:=(hF.square 4)
 have hg:Fief.sizeK L 1 g:=sizeK.main L
 have ht:Fief.sizeK L 2 (fun x=> g x^2*p x^H):=(hg.square _).tint ((sizeK.height _).square _)|>.low (by simp)
 filter_upwards [h,eventually_gt_atTop (0:ℝ), (ht.low (k:=1) (by decide)).spine.eventually (ge_mem_nhds (show 0<c^4 by positivity))] with x hK hv hh
 let t:=Real.sqrt (Real.sqrt x); let s:=Real.sqrt x; have hx:s>0:=Real.sqrt_pos_of_pos hv; have hy:t>0:=Real.sqrt_pos_of_pos hx
 have hs:t^4=x:= by rw [show t^4=(t^2)^2 from by ring,show t^2=s from Real.sq_sqrt hx.le,show s^2=x from Real.sq_sqrt hv.le]
 change |F x| ≤ c*t⁻¹
 rw [← div_eq_mul_inv]; apply (le_div_iff₀ hy).2
 refine le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) hc.le ?_
 rw [mul_pow,hs, ←abs_pow]; change |F x^4| ≤ g x^4*p x^H at hK; refine (mul_le_mul_of_nonneg_right hK hv.le).trans (le_trans ?_ (show g x^2*p x^H ≤c^4 from hh))
 have hy₀:0<y x:=hv.trans_le (deckL L x); apply (mul_le_mul_of_nonneg_left (show x ≤ y x from deckL L x) (mul_nonneg (pow_nonneg (show 0≤g x from (Scales.gauge _ _ hy₀).le) _) (pow_nonneg (Scales.pos ..).le _))).trans (le_of_eq ?_)
 rw [show g x^4*p x^H*y x=(g x^2*p x^H)*(y x*g x^2) from by ring,show y x*g x^2=1 from Scales.yg2 _ _ hy₀,mul_one]

open YM.SectorNext.Vacuum Fineness
-- log cost on any positive plateau
lemma log_rel (b a c:ℝ)(h:0<c)(p:c≤b)(q:c≤a): c * |Real.log b-Real.log a| ≤ |b-a| := by
 have hl := h.trans_le p; have hm:=h.trans_le q
 have k{b a:ℝ}(p:c≤a)(q:a≤b): c*(Real.log b-Real.log a) ≤ b-a := by
   have hr:=h.trans_le p; have hw:=hr.trans_le q; rw [mul_comm,← le_div_iff₀ h,← Real.log_div hw.ne' hr.ne']; apply (Real.log_le_sub_one_of_pos (div_pos hw hr)).trans
   rw [show b/a-1=(b-a)/a by field_simp]; exact div_le_div_of_nonneg_left (sub_nonneg.mpr q) h p
 rcases le_total a b with t|t
 · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm t)),abs_of_nonneg (sub_nonneg.mpr t)]; exact k q t
 · rw [abs_sub_comm b a, abs_sub_comm (Real.log b),abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hl t)),abs_of_nonneg (sub_nonneg.mpr t)]; exact k p t

open Pannier
variable {G:Gauge}
lemma LensFareX(A:ChartRatio G)(g:KernelChoices)(p:LocalRatio A):∃ C>0, ∀ᶠ b:ℝ in atTop, ∀ {m n:Side}(S:StepData m n), S.kernel=g →
 Real.sqrt b * |Real.log (S.penaltyZ b G)-Real.log (spare A b)+halfLie G * Real.log g.penalty|≤ C:=by
 let t:=g.penalty; have u:=g.penalty_pos; let d:= Module.finrank ℝ G.Color
 let d':=halfLie G
 let v:=narrow A t; have ht:0<v:=narrow_pos A p _ u
 have he:Real.log v=logFlat A - d'*Real.log g.penalty:=by
    have hp : (Real.pi / (t/2))>0:= div_pos Real.pi_pos (half_pos u)
    rw [show v=A.scale * (Real.pi / (t/2)) ^ d' from rfl, Real.log_mul p.scale.ne' (Real.rpow_pos_of_pos hp _).ne',Real.log_rpow hp]
    rw [show Real.pi/(t/2)= (2*Real.pi)/g.penalty from by unfold t; ring,Real.log_div (mul_pos (by norm_num) Real.pi_pos).ne' u.ne']; unfold logFlat d'; rw [shadowLie (G:=G)]; ring
 obtain ⟨C,hC,c⟩:=cobalt_asymptotic A p g.penalty_pos; have hv:v/2 < v:=half_lt_self ht
 refine ⟨C/(v/2),div_pos hC (half_pos ht),?_⟩
 filter_upwards [Real.tendsto_sqrt_atTop.eventually ((first_asymptotic A p g.penalty u).eventually (le_mem_nhds hv)), Real.tendsto_sqrt_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with b hp hx hb m n S hS
 let a:=Real.sqrt b; let f (x:ℝ):= x^d*linkZ G (g.penalty*x^2)
 have ha:0<a:=Real.sqrt_pos_of_pos hb
 change v/2 ≤ f a at hp; have hQ:= log_rel (f a) v (v/2) (half_pos ht) hp hv.le; apply (le_div_iff₀ (half_pos ht)).mpr
 have heq : S.penaltyZ b G = linkZ G (g.penalty*b) := by
   unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth; rw [hS]; congr 1; ext x; ring_nf
 have hx' : Real.log (S.penaltyZ b G)-Real.log (spare A b)+d'*Real.log g.penalty=Real.log (f a)-Real.log v := by
   have ha':a^2=b:=Real.sq_sqrt hb.le
   unfold f; rw [ha',← heq,Real.log_mul (pow_ne_zero _ ha.ne') (S.penaltyZ_pos ..).ne', Real.log_pow,show Real.log a=_ from Real.log_sqrt hb.le,he,spare_formula A p.scale hb,←shadowLie]; unfold d' d halfLie; ring -- ambiguity logFlat
 rw [show halfLie G = d' from rfl,hx',mul_assoc,mul_comm (|_|) (v/2)]
 exact ((mul_le_mul_of_nonneg_left hQ ha.le).trans (c a hx))

open MeasureTheory ProbabilityTheory
lemma point_tailX(G:Gauge):∃ a >0, ∃ C>0,∀ b ≥ (0:ℝ),
  |Appel.point G b - 1| ≤ C*Real.exp (-a*b^2):=by
 let μ:= Appel.rice G; haveI:IsGaussian μ:=inferInstanceAs (IsGaussian (stdGaussian G.Color)); haveI:IsProbabilityMeasure μ:=inferInstanceAs (IsProbabilityMeasure (stdGaussian G.Color)); obtain ⟨a,h,p⟩:= IsGaussian.exists_integrable_exp_sq μ
 let F(x:G.Color):= Real.exp (a*‖x‖^2); have Hp:Integrable F μ:=p; have hf:∀ x:G.Color,0≤F x:=fun _=> (Real.exp_pos _).le; let C:= (∫ x,F x ∂μ) + 1; have hp:0<C:=add_pos_of_nonneg_of_pos (integral_nonneg hf) zero_lt_one
 refine ⟨a,h,C,hp,fun b hb=>?_⟩; let A:=closedBall (0:G.Color) b; have ha:MeasurableSet A:=isClosed_closedBall.measurableSet
 let Y:=Real.exp (a*b^2)
 have v: |Appel.point G b-1|= μ.real Aᶜ:=by
    rw [show Appel.point G b= μ.real A from rfl, abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr measureReal_le_one), measureReal_compl ha]; simp -- syntax
 have hq: μ.real Aᶜ * Y ≤ ∫ x,F x ∂μ:=calc
    _ = ∫ x in Aᶜ,(fun _ : G.Color=>Y) x ∂μ:= by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ x in Aᶜ,F x ∂μ:= setIntegral_mono_on integrableOn_const p.integrableOn ha.compl (fun x hx=> Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb (le_of_not_ge (mt mem_closedBall_zero_iff.mpr hx)) _) h.le))
    _ ≤ _:= integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hf) Hp
 rw [v,neg_mul,Real.exp_neg,← div_eq_mul_inv]; exact (le_div_iff₀ (Real.exp_pos _)).mpr (hq.trans (le_add_of_nonneg_right zero_le_one))

-- Length c depends on the plateau purchase (after h etc.), not on the Scratchpad.
lemma point_flares (l:Side)(A':ChartRatio SU.group)(p: LocalRatio A')
 (a k:ℝ)(h:0<a)(t:0<k): ∀ᶠ x:ℝ in atTop,∀ (y:ℝ), k*Scales.p SU.group l x≤ y →
  ∀ b> (0:ℝ),|Real.log (shotM A' y b)-Real.log (spare A' b)| ≤ a*fourthDeck x:=by
 let G := SU.group; let P:= Scales.p G l
 obtain ⟨D,hD,C,hC,c⟩:=point_tailX G
 have hk:Tendsto (fun x=> k*P x) atTop atTop:= Tendsto.const_mul_atTop t (Scales.peak ..)
 have hh:Tendsto (fun x=> (1+(radiusB x:ℝ))/P x) atTop (𝓝 0):=by simpa only [Scales.b,P,one_mul,Real.rpow_one,pow_one] using Scales.cover_pay G l 1 (a:=1) one_pos
 obtain ⟨z,hz⟩:=eventually_atTop.mp ((Fineness.arc_guard G).eventually (le_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
 let T:=D*k^2; have hT:0<T:=by unfold T; positivity
 filter_upwards [hk.eventually_ge_atTop z,(Scales.peak G l).eventually_ge_atTop 1,size_fourth (sizeK.tempo l) (a/(2*C)) (by positivity),hh.eventually (ge_mem_nhds zero_lt_one),Newt.smallF (n:=1) hT 1] with x hK pK r hx hy
 intro y w b i; have hq : P x >0:= Scales.pos ..; have he:0<y:=(mul_pos t hq).trans_le w
 have H0: (1:ℝ)/2 ≤ Appel.point G y:= hz y (hK.trans w)
 rw [Reine.shotM, Real.log_mul (spare_pos A' p i).ne' (Appel.point_p he).ne', add_sub_cancel_left]
 have hp0:=log_rel (Appel.point G y) 1 (1/2) (by norm_num) H0 (by norm_num)
 rw [Real.log_one,sub_zero] at hp0
 have ht: Real.exp (-D*y^2) ≤ temp x:=by
   simp only [pow_one,mul_one] at hy
   change (1+(radiusB x:ℝ))/P x ≤ 1 at hx; rw [div_le_one hq] at hx
   apply le_trans (Real.exp_monotone ?_) hy
   have hP: 1 ≤ P x:= pK; let B:=Stores.till x; change -D *_ ≤ -T*B
   have Ht: B ≤ radiusB x:=by unfold B Stores.till; omega
   have h': (B:ℝ)≤ P x^2:=by nlinarith only [hx,hP,Nat.cast_le (α:=ℝ)|>.mpr Ht]
   have hvK:=mul_le_mul_of_nonneg_left h' hT.le; have hvx:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos t hq).le w 2) hD.le
   unfold T at *; nlinarith only [hvK,hvx]
 have hV: (1:ℝ)/2*|Real.log (Appel.point G y)|≤ C*temp x:=hp0.trans ((c y he.le).trans (mul_le_mul_of_nonneg_left ht hC.le))
 have hz:C*temp x≤C*(a/(2*C)*fourthDeck x):=mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) r) hC.le
 rw [show C*(a/(2*C)*fourthDeck x)= a*fourthDeck x/2 by field_simp] at hz
 change |Real.log (Appel.point G y)|≤ _; linarith only [hz,hV] -- point notation

lemma deck_on_pane (K:Teller SU.group)(l:Side)(A:ChartRatio SU.group)(p: LocalRatio A)
 (η:ℝ)(h:0<η): ∀ᶠ x:ℝ in atTop,∀ b :ℝ, Scales.y SU.group l x/2 ≤ b→∀ {m n:Side}(S:StepData m n), S.kernel=K.bind →
 |Real.log (S.penaltyZ b SU.group)-Real.log (spare A b)+halfLie SU.group * Real.log S.kernel.penalty|≤ η*fourthDeck x:=by
 obtain ⟨C,hC,c'⟩:= LensFareX A K.bind p
 obtain ⟨z,hz⟩:=eventually_atTop.mp c'
 let s:=Real.sqrt; have hk:Tendsto (s ∘ s) atTop atTop:= Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
 filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (2*z), hk.eventually_ge_atTop (2*C/η)] with x hx ht hu b i m n S hS
 rw [hS]; have hw:x/2≤b:= (div_le_div_of_nonneg_right (deckL l x) (by norm_num)).trans i
 have hh:= hz b (by linarith only [hw,ht]) S hS
 let f:= s x; let g:= s f; let t:=s b; have hv:0<f:=Real.sqrt_pos_of_pos hx; have hG:0<g:=Real.sqrt_pos_of_pos hv; have hT:0<t:=Real.sqrt_pos_of_pos ((half_pos hx).trans_le hw)
 have hg:g^2=f:=Real.sq_sqrt hv.le; have he:t*2≥f:=by nlinarith [show t^2=b from Real.sq_sqrt (((half_pos hx).trans_le hw).le),show f^2=x from Real.sq_sqrt hx.le]
 have hf: g*η ≥ 2*C:=(div_le_iff₀ h).mp hu
 let absX:=|Real.log (S.penaltyZ b SU.group)-Real.log (spare A b)+halfLie SU.group*Real.log K.bind.penalty|
 change t*absX ≤ C at hh; change absX ≤ η*g⁻¹; rw [← div_eq_mul_inv]; apply (le_div_iff₀ hG).2; apply le_of_mul_le_mul_left _ hT
 calc
 t*(absX*g) = t*absX*g:=by ring
 _ ≤ C*g:=mul_le_mul_of_nonneg_right hh hG.le
 _ ≤ _:=by nlinarith only [mul_le_mul_of_nonneg_right hf hG.le,mul_le_mul_of_nonneg_left he h.le, congr_arg (fun i => i*η) hg]

lemma porch_stairs(K:Teller SU.group)(R:Patch)(η:ℝ)(p:0<η): ∀ᶠ x in atTop,∀ {m n:Side}(S:StepData m n)(M:Monk SU.group S)(U:Tube SU.group S)(H:Bed){η' δ:ℝ},Floor H K.top.clip n η' δ→Attached H U.up→ Bid.Sworn H n SU.group→ Newt.Cert R K S U x→ |Corne.arcD U x M+(1/2:ℝ)*Real.log (FreeResolvent.treeMatrix SU.group S M.park H.metric).det| ≤ η*fourthDeck x* Fintype.card (Site n):=by
 let v:= K.top.width/4; have hp:0<v:= by unfold v; have h:=K.top.width_pos; positivity
 let k:= FreeResolvent.Affine.headGap SU.group R K.bind K.top.clip; have he:0<k:= FreeResolvent.Affine.headGap_pos ..
 let c:ℝ:= 2*(Fintype.card SU.group.ColorIndex:ℝ); have hc:0≤c:=by unfold c; positivity
 filter_upwards [Newt.smallF (n:=1) hp (ozPay R K.bind K.top.width K.top.paths SU.group), size_fourth ((sizeK.tempo R.L).scale (c/k)) η p] with x ht hz m n S M U H η' δ u t q a
 rw [pow_one] at ht; rw [mul_comm _ (Fintype.card (Site n):ℝ)]; apply (YM.Fineness.porch S M U H u t q a).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
 apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht he.le) hc).trans
 rw [show c*(temp x/k)=c/k*temp x by ring]; exact (le_abs_self _).trans hz

end cyan
end YM.CF.Py.Rate
end
