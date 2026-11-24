import YM.CF.Moto.Slate
import YM.CF.Tale.Tree
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tune
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.VerifiedReset Siete Taxi Moto
variable {n m:Side}{E P:BudgetPoint}{S:StepData (More n) (More m)}{T:Tube SU.group S}{q o v x y:ℝ}{k:ℕ}{M:Side}
local notation "XΦ"=> PlaqAxes×PlaqAxes
variable (Z:Skate)(A i:PlaqAxes)(u:Verc Z)(hx:∀ i j, ‖Z i j‖≤v)
variable (Y: Config SU.group (More n) → Config SU.group (More m))(X:Support (More m))(X':Support (More n))(a:Site (More n))
local notation "a0"=> S.ratio.embed a
local notation "Lx"=> (M.val:ℝ)⁻¹
local notation "θ"=> E.threshold
local notation "θ₂"=> P.threshold
variable (h:Tale.Wyth T X Y a E M q)(hk:Lattice.halo 2 {S.ratio.embed a}⊆ X)
local notation "IV"=> increment (1:Pane n)
local notation "ZΦ"=> M--dummy
local notation "HΦ"=> θ^2*Lx^4 / θ₂^2
variable (vP:∀ i j:PlaqAxes, ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) (Tale.quanta Y (S.ratio.embed a) i j) 0)
local notation "E'"=> tangD n
local notation "K"=> ![Tale.clipT E a A,Tale.clipT E a i]
local notation "PΓ"=> kerP a0 P Z
local notation "PS" t:max=> ((Z t.1 t.2)/((2:ℝ)*θ₂^2:ℝ)) -- coerces
local notation "Cκ"=> (Fintype.card XΦ:ℝ)
local notation "Yq" t:max=> (Tale.a_Op (More m) a0 t.1 t.2)
-- plain expansion
include hk
lemma grip_m (V:Pane m): kerP (S.ratio.embed a) P Z V=∑ t:XΦ, (PS t) * ↑((Yq t) V):=by
 unfold kerP; apply Complex.ext <;> (simp only [Complex.add_re,Complex.add_im, Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im, Complex.mul_I_re,Complex.mul_I_im,Complex.re_sum,Complex.im_sum]) -- these names?
 · unfold counter AnalyticBridge.VerifiedReset.quad; simp_rw [Finset.sum_div]; rw [Fintype.sum_prod_type]; simp only [neg_zero,add_zero]; refine sum_congr rfl fun p _=>sum_congr rfl fun i _=>?_ ; simp only [Complex.mul_re,Complex.div_ofReal_re,Complex.ofReal_re,Complex.ofReal_im,Tale.a_Op,mul_zero,sub_zero]; ring -- tune
 unfold counter AnalyticBridge.VerifiedReset.quad; simp_rw [Finset.sum_div]; rw [Fintype.sum_prod_type]; simp only [zero_add]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; simp only [Complex.mul_im,Complex.div_ofReal_im,Complex.ofReal_re,Complex.ofReal_im,Tale.a_Op,mul_zero,zero_add]; ring
omit hk
lemma loan_t (p:BudgetPoint)(M':Side)(i j v w:PlaqAxes):Tale.zolo p M' i j v w= if i=j∧v=w then p.threshold^2*((M'.val:ℝ)⁻¹)^4 else 0:=by
 unfold Tale.zolo Tale.lens_k; by_cases a:i=j<;>by_cases b:v=w<;> simp only [a,b,↓reduceIte,and_self,true_and,false_and, real_inner_smul_left,real_inner_smul_right,inner_zero_left,inner_zero_right, mul_zero,real_inner_self_eq_norm_sq,smul_zero,norm_zero, norm_smul, spike_norm Thera.yet_one,mul_one,Real.norm_of_nonneg p.threshold_pos.le,Real.norm_of_nonneg (sq_nonneg ((M'.val:ℝ)⁻¹))] <;> ring
include hk h vP hx u
local notation "Mλ"=> (q*θ^2)
abbrev l_fee (k:ℝ)(P E:BudgetPoint)(q v:ℝ):= k*(v/(2*P.threshold^2)*(q*E.threshold^2))
lemma clasp : ‖iteratedFDeriv ℝ 2 (PΓ ∘ Y ∘ increment 1) 0 K-(↑(θ^2*Lx^4 / θ₂^2):ℂ)*Z A i‖ ≤ l_fee Cκ P E q v:=by -- syntax
 let W(t:XΦ):ℂ:= PS t; let F(t:XΦ):E'→ℂ:=Complex.ofReal ∘ Tale.quanta Y a0 t.1 t.2; let Φ0(t):E'→ℂ:= W t • F t
 have hg(t):ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (Φ0 t) 0:= contDiffAt_const.smul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (vP t.1 t.2))
 have hp:PΓ ∘ Y ∘ increment 1= ∑ i:XΦ,Φ0 i:=funext fun s=> (grip_m (P:=P) Z X a hk (Y (increment 1 s))).trans (Finset.sum_apply s (univ:Finset XΦ) Φ0).symm -- tune equality
 let U(t:XΦ):=Tale.zolo E M i t.1 A t.2; let V(t:XΦ):= Tale.zolo E M A t.1 i t.2; let D:=θ^2 *Lx^4
 have hv(a b:PlaqAxes): (∑ t:XΦ,W t * ↑(Tale.zolo E M a t.1 b t.2))= W (a,b)*↑D:=by rw [sum_eq_single (a,b), loan_t,if_pos]; tauto; intro t _ l; simp [loan_t,show ¬(a=t.1∧b=t.2) from (fun k=>l (Prod.ext k.1.symm k.2.symm))]; simp
 let Tt(t:XΦ):=iteratedFDeriv ℝ 2 (Φ0 t) 0 K; let Ht(t:XΦ):= U t+ V t
 have he: (∑ t:XΦ,W t *↑(Ht t))=(↑(HΦ):ℂ)*Z A i:=by unfold Ht U V; simp_rw [Complex.ofReal_add,mul_add]; rw [sum_add_distrib,hv,hv]; unfold W; rw [u i]; unfold D; push_cast; ring -- tune
 rw [hp,←he,iteratedFDeriv_sum_apply (fun i _=> hg i),_root_.sum_apply] -- name check
 let η:=(v/(2*θ₂^2))* Mλ; change ‖(∑ t:XΦ,Tt t)- ∑ t:XΦ,_‖ ≤ _; rw [←sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>η) ?_).trans_eq ?_); swap; · simp [η,l_fee]
 intro t _; have ho:‖W t‖≤ v/(2*θ₂^2):=by unfold W; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (by positivity)]; exact div_le_div_of_nonneg_right (hx _ _) (by positivity)
 let Tg:= Tale.quanta Y a0 t.1 t.2; have hs:=vP t.1 t.2; let Kp:=iteratedFDeriv ℝ 2 Tg 0 K
 have hh: Tt t=W t * Kp:=by
    unfold Tt Φ0; have ht:F t= Complex.ofRealCLM ∘ Tg:=rfl
    rw [ht,iteratedFDeriv_const_smul_apply (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hs),Complex.ofRealCLM.iteratedFDeriv_comp_left hs (le_refl _)] -- tune rhs
    rfl
 rw [hh,←mul_sub,← Complex.ofReal_sub,norm_mul]; rw [Complex.norm_real]; exact mul_le_mul ho (h.sonic _ _ A i hk) (norm_nonneg _) ((norm_nonneg _).trans ho)
end YM.CF.Tune
