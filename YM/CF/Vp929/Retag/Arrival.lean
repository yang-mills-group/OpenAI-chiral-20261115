import YM.CF.Vp929.Retag.Size
import YM.CF.Vp929.Retag.Switch
import YM.CF.Vp929.Budget.Arith
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.SplitFlag
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
open Ione Beau Haro Cascade
open scoped Mew
open Jet SU Taxi Rue
open WilsonStartup
/-! Factor the gas sum. -/
open Py Py.Rate
open scoped ComplexConjugate
variable {n:Side} (c : Clip) (b p:BudgetPoint)
abbrev topTag (z:ℂ): Pair (Corr n):= ((0,entry c b p z Complex.reCLM),(0,entry c b p z Complex.imCLM))
lemma top_real (β:ℝ) : (topTag (n:=n) c b p β).2=0:=by
  refine Prod.ext rfl ?_; funext i x; change entry _ _ _ _ Complex.imCLM i x=0; unfold entry; split; swap; rfl
  unfold minted; split_ifs; rw [←Complex.ofReal_neg,←Complex.ofReal_mul, ←Complex.ofReal_exp,show ∀ v:ℝ,Complex.imCLM (v:ℂ)=0 from fun _=>rfl,mul_zero,map_zero]; rw [mul_zero,map_zero]
lemma top_holo (Z:Set ℂ)(f:ℂ→ℂ)(H:IsOpen Z)(h:DifferentiableOn ℂ f Z) : HoloCorr (s:=n) Z (topTag c b p ∘ f):=by
  constructor
  · intro i v; change Holo Z (fun _=> ((0:Cipher n),0)); exact ⟨differentiableOn_const _,differentiableOn_const _⟩
  intro i v; let D:=marks i
  let G(z:ℂ):= if Used b i ∧ Unmasked b p v.1 D then (((#(patch i):ℝ)⁻¹:ℝ):ℂ) * Complex.exp (-f z* tagEnergy c b p D v.1) else 0
  have he(z:ℂ)(A:ℂ→L[ℝ]ℝ): entry c b p (f z) A i v= (A (G z)) • 1:=by
    unfold G entry minted;
    split_ifs <;>(try simp only [map_zero,mul_zero,zero_smul]) <;> first|rfl| (rw [show ∀ (z:ℂ)(x:ℝ), (x:ℂ)*z=x • z from fun z x=> (Complex.real_smul ..).symm, map_smul]; rfl) | tauto
  have hg:DifferentiableOn ℂ G Z:=by unfold G; split; exact (DifferentiableOn.const_mul ((h.neg.mul (differentiableOn_const _)).cexp) _); exact differentiableOn_const _
  change Holo Z (fun z=> (entry c b p (f z) _ i v, entry c b p (f z) _ i v))
  dsimp only [Holo,Pair.plus,Pair.minus,Complex.reCLM_apply,Complex.imCLM_apply]; simp_rw [he,Complex.reCLM_apply,Complex.imCLM_apply,← Complex.coe_smul,smul_smul,← add_smul,←sub_smul]; simp_rw [mul_comm Complex.I,Complex.re_add_im];
  constructor
  · exact hg.smul (differentiableOn_const _)
  have hp : DifferentiableOn ℂ (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) ((starRingEnd ℂ) ⁻¹' Z):=fun z hz=> (differentiableAt_conj_conj_iff.mpr ((hg _ hz).differentiableAt (H.mem_nhds hz))).differentiableWithinAt
  apply (hp.smul (differentiableOn_const (1:Cipher n))).congr; intro y _;  congr 1; apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (W : Grace K R L) {B N:Side} {d:ℝ} (U : Grasp W.U B d) (G' : GivenX W U) (J: Robes N W G') (h:ℝ)
lemma buy_retag (hc:K.top.clip.direct ≤ 1) : ∀ᶠ e in atTop, ∀ N0:ℕ, Retag W U G' J h N0 e:= by
  obtain ⟨a,ha⟩:= eventually_atTop.mp (capacity K.top.clip hc R.L); obtain ⟨j,hj⟩:= Rue.arrests
  filter_upwards [eventually_ge_atTop a,eventually_gt_atTop j,eventually_ge_atTop (Real.exp 1)] with e he hr hl N0
  intro x y hx hs hw m S p b hp hb _ _ _ _ _ _ _ _
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩:= ha y (he.trans (hx.trans hs)) b hb; obtain ⟨H₁,H₂,H₃,_⟩:= ha x (he.trans hx) p hp
  let T:= topTag (n:=mid m B) K.top.clip b p
  have hxy:b.threshold ≤ p.threshold:=hb.threshold ▸ hp.threshold ▸ hj.antitoneOn (hr.trans_le hx) (hr.trans_le (hx.trans hs)) hs
  refine ⟨T,fun z H=>?_,fun Z h f _=> top_holo _ _ _ Z f h, fun β _=> ⟨top_real .., fun v _ hv=>switch_launch b p W U S h₁ H₁ hxy β v hv⟩⟩
  have hP:0<x:=(Real.exp_pos _).trans_le (hl.trans hx)
  have Hz:y/4 ≤ z.re:= by linarith only [H.1,hw]
  have hZ:0≤ z.re:= le_trans (by have := hP.trans_le hs; positivity) Hz
  let g:= Timing.quota (Real.log y); let C:= K.top.clip; let Δ:= Real.exp g-1; let I:=vanilla (mid m B)
  have hh : 3*Timing.M (Real.log y) ≤ z.re*(gain b-liabilities C b p):= h₆.trans (mul_le_mul Hz (by linarith [h₇ p hp.order hp.power (by rw [hb.threshold,hp.threshold]; exact winter_fit _ _ hP (hl.trans hx) hs (by linarith))]) (by have := gain_pos b; positivity) hZ)
  have ht A (hr:∀ x,|A x|≤‖x‖) : Charged b I K.j R.L.val h Δ (0,entry C b p z A):= by
    have hy : 0 ≤ Δ:= sub_nonneg.mpr (Real.one_le_exp (Real.exp_pos _ |>.le)); have hv: Charged b I K.j R.L.val h Δ 0 := Charged.zero.mono hy
    exact ⟨⟨hv.inc,earns_entry C b p z A h₁ h₂ h₄ h (fun i U=> minted_price C b p z A U i _ h₁ hxy H₃ hr hZ hh)⟩,hv.dawn,hv.warp⟩
  exact ⟨(ht _ Complex.abs_re_le_norm).mono h₅,(ht _ Complex.abs_im_le_norm).mono h₅⟩
end YM.CF.SplitFlag
