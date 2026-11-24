import YM.CF.Vp929.Rails.Climate
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "Y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
open Dialect Lid Appel.Rate
open Lor
variable {P:Pilot} {n₁:ℕ}{c:Estimate}{Bv:ℝ}
local notation "BX" => Esti.plow
local notation "ηB" x:max=> Scales.y SU.group R.L x
/-- d_X and margin attenuation. -/
abbrev dwidth (R:Patch)(x:ℝ):= Scales.y SU.group R.L x/(Esti.plow x)^6
abbrev dye (x:ℝ):= ((Esti.plow x)^5)⁻¹
def sprayM(P:Pilot)(R:Patch)(a x:ℝ):= Real.exp (-(Esti.scaleM SU.group R.L (a*(P.large/4)^2/4) x))
local notation "Fas"=>sprayM P R ag
include R P
lemma misty_m (x:ℝ) : desire R P ag Cg x=(Fas x)^4* Cg := by unfold desire sprayM; rw [← Real.exp_nat_mul]; unfold Esti.scaleM Pilot.hat; push_cast; ring_nf
lemma sinks (C:0 < ag)(k:ℕ): sizeK R.L k Fas:= by
 let g:= ag*(P.large/4)^2/4; have p:0<g:=by unfold g; have h:= P.high; positivity
 refine ⟨0,?_ ⟩; let H:= loomH ((Wray.invertC R.L).power k) _ p R.L
 filter_upwards [H,(Scales.year SU.group R.L).eventually_gt_atTop 0] with x l s
 let k0:= Scales.g SU.group R.L x; let F:= Esti.scaleM SU.group R.L g x; have e:0<k0:= Scales.gauge SU.group R.L s
 have hx: (k0^k)⁻¹ ≤Real.exp F:= by rw [← inv_pow]; exact (le_abs_self _).trans l
 unfold sprayM; rw [abs_of_pos (Real.exp_pos _), Real.exp_neg,pow_zero,mul_one]; exact (inv_anti₀ (inv_pos.mpr (pow_pos e k)) hx).trans_eq (inv_inv _)
omit P
lemma plantd : Tendsto Esti.plow atTop atTop := tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
abbrev wasted (R:Patch):= Fintype.card Axis * R.L.val^4
lemma waste_l(x:ℝ): (wasteful R (radiusB x):ℝ)≤ wasted R * (2*BX x)^4:= by unfold wasteful wasted Esti.plow Scales.b; push_cast; gcongr; linarith
section
variable (T:Estimate.Economic c R)(C: Patron ag Cg) (framH: Framing n₁ Bv)
include T framH C
local notation "N'"=> (VolumeRate.panel n₁).card
lemma eventually_climate (P:Pilot) : ∃ κ:ℝ→ℝ,sizeK R.L 1 κ ∧∀ᶠ x in atTop, Climate P R c x (dwidth R x) (dye x) (sprayM P R ag x) (κ x) ag Cg Bv n₁:= by
 let Q(x):= Bv*((VolumeRate.panel n₁).card*c.Pc x); have pQ:sizeK R.L 1 Q:= (T.Pc.scale _).scale _; obtain ⟨G,p,u⟩:=officeH (23/4) (1/4) pQ
 let F:= sprayM P R ag; have hm:= sinks (P:=P) (R:=R) C.pos 1; let s:=(widthS n₁+3:ℝ); let K:ℝ:= ↑(wasted R); let T'(x:ℝ):ℝ:=↑(wasteful R (radiusB x)); have ht: BoreP T':= by unfold T' wasteful; push_cast; exact (BoreP.still _).grip (((BoreP.radius_c.join BoreP.radius_c).join (BoreP.still _)).self 4)
 have hs: Tendsto (fun x=>(1+T' x)*Cg* F x) atTop (𝓝 0) := ((((BoreP.still 1).join ht).grip (BoreP.still Cg)).creditK R.L|>.tint hm).spine
 have he:Tendsto (fun x=>BX x^5* (Cg*F x)) atTop (𝓝 0):= Chill_v.coin (hm.scale Cg) 5
 have hb:= @plantd R; have y:Tendsto (fun x=> Pilot.hat P R x) atTop atTop:= Tendsto.const_mul_atTop P.high (Scales.peak SU.group R.L)
 refine ⟨G,p,?_⟩; have ha:=C.pos; have h':=C.earns
 filter_upwards [u,speedK (billX R.L), hs.eventually (ge_mem_nhds (show (0:ℝ)<1/1024 by norm_num)),he.eventually (ge_mem_nhds zero_lt_one),hb.eventually_ge_atTop (s*(2/ag)*Cg), hb.eventually_ge_atTop 2,hb.eventually_ge_atTop (512*K), y.eventually_ge_atTop 4, hm.spine.eventually (ge_mem_nhds zero_lt_one), (Scales.year SU.group R.L).eventually_gt_atTop 0] with x hx sp s₁ s₂ h₁ h₂ h₃ h₄ h₅ g
 have hv:0<F x:=Real.exp_pos _; let Rb:= BX x; have hb:0 < Rb:=lt_of_lt_of_le two_pos h₂; change F x≤1 at h₅
 have hp:G x ≥ Footprint.payment 1 (6*(radiusB x+1)) 0 (1/4) 1 (Bv*((VolumeRate.panel n₁).card*c.Pc x)) ((23/4)+1) 0:= hx.2.2
 have U:(widthS n₁+3:ℝ)*dwidth R x/ Scales.y SU.group R.L x = s/Rb^6:= by unfold dwidth s; field_simp; rfl
 have h₆:1/ Rb^5=dye x:=one_div _
 have h₇:dye x≤1/2:= by rw [←h₆,div_le_div_iff₀ (by positivity) (by norm_num)]; have H:=le_trans h₂ (le_self_pow₀ (by linarith [show 2 ≤ Rb from h₂] : (1:ℝ)≤ Rb) (show (5:ℕ)≠0 by norm_num)); linarith
 have w: s/Rb^6*(2/ag)*Cg ≤ 1/Rb^5:=by rw [div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by positivity)]; exact (mul_le_mul_of_nonneg_right (show s*(2/ag)*Cg ≤ Rb from h₁) (pow_nonneg hb.le 5)).trans_eq (by ring)
 refine ⟨framH,C,hx.1,h₄,div_pos g (pow_pos hb 6),hp,hx.2.1,sp,⟨inv_nonneg.mpr (pow_nonneg hb.le _),h₇⟩,?_ ,?_ ,?_ ,?_ ,hv,h₅,?_⟩
 · rw [U]; have hu : s/Rb^6*(2/ag) ≤1:=by
     have hQ:Cg≥1:= C.earns
     have hn:0≤ s/Rb^6*(2/ag):=by unfold s; positivity
     exact le_trans (le_mul_of_one_le_right hn hQ) (w.trans (h₆.trans_le (h₇.trans (by norm_num))))
   field_simp at hu; apply (div_le_iff₀ (pow_pos hb ..)).2; linarith
 · rw [U,←h₆]; exact w
 · rw [misty_m,←h₆,le_div_iff₀ (by positivity)]; have h₈:=pow_le_of_le_one hv.le h₅ (n:=4) (by norm_num); refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₈ (by linarith :0≤Cg)) (pow_nonneg hb.le 5)) ?_; simpa only [mul_comm Cg, mul_comm (Rb^5)] using (show Rb^5*(Cg*F x)≤1 from s₂)
 · rw [←h₆]; apply le_trans (mul_le_mul_of_nonneg_right (waste_l (R:=R) x) (by positivity)); change (K* (2*Rb)^4)*(4*(1/Rb^5)) ≤ _; field_simp; nlinarith only [mul_le_mul_of_nonneg_right (show 512*K ≤ Rb from h₃) (pow_nonneg hb.le 4),h₃]
 · rw [misty_m]; have h₈:=pow_le_of_le_one hv.le h₅ (n:=2) (by norm_num); have hz:(1+T' x)*Cg*F x^2 ≤ 1/1024:= le_trans (mul_le_mul_of_nonneg_left h₈ (mul_nonneg (by unfold T'; positivity) (zero_le_one.trans C.earns))) s₁; have hp:= mul_le_mul_of_nonneg_right hz (pow_two_nonneg (F x)); change _* (F x^4*Cg) ≤ F x^2/1024; unfold T' at hp; ring_nf at hp ⊢; exact hp
end
end Pitching
end YM.CF.Py.Rate
