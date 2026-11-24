import YM.CF.Vp929.Canon.Cedar
import YM.CF.Vp929.Canon.Crown
import YM.CF.Vp929.Canon.Rime
import YM.CF.Vp929.Canon.Sub
import YM.CF.Vp929.Stage.Costs
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
open Salt Vow Bake Larch Cycle929
open Sour Sour.MatchW Sour.MatchW.Technique
variable {T U:BeatL n}{e h r θ b0 b1 b2:ℝ} [Nonempty (Haro.ΘS r)]{O:Scree.Loom n}{N:ℕ}
local notation "pP"=> P

variable (χ:Technique P h e θ N O T U b0 b1 b2 r)(p:2*P.supportExponent*Fief.tileN 1 ≤ b0/2*P.B)
variable {x σ u' θ' h0 z0 z1 Cα Cδ ζ ℓ v0:ℝ}
variable {R:PathData SU.group}{c:Clip}
open QuiltB Fixed.Voltage Push.BetaTransport Pitching.Focus
variable {Q:RegBudget n}{D:Cusp n}(u:1 ≤j)(t:Scree.Hub n→ Scree.Hub n)

abbrev aligner (P:BudgetPoint)(L:Side)(t:Scree.Hub n→Scree.Hub n)(q:↥SpaceM)(Q:RegBudget n)(η:SpaceM→ₗ[ℝ] RegBudget n)(w:ℝ) : RegBudget n:= NetX t P (η q) + w • Q

abbrev phaseY (P:BudgetPoint)(L:Side)(t:Scree.Hub n→Scree.Hub n)(q:↥SpaceM)(D:Cusp n)(η:SpaceM→ₗ[ℝ] RegBudget n)(w:ℝ):= NetY t P L.val (η q)+ w • D
abbrev shiftB (P:BudgetPoint)(n:Side)(F:RegBudget n) (q:ℝ)(R:PathData SU.group)(c:Clip):ℝ:= - gaugeTest q F P / kineticC n R c P q
abbrev shiftM (P:BudgetPoint)(F:RegBudget n)(L:Side)(M:Male)(j:ℕ)(u:1 ≤j):= pointW n j u M (StackL F (treeΘ P L.val))
local notation "db"=> (shiftB P n F q R c)
local notation "dm"=> (shiftM P F L M j u)
local notation "fq"=> lmap χ dm
local notation "xp"=> aligner P L t dm Q (lmap χ) db
local notation "yp"=> phaseY P L t dm D (lmap χ) db
local notation "hT"=> kineticC n R c P q
variable (kQ:Kit P h R c L.val Q D 1 z0 z1)(Ω:R.Bounds c σ C ℓ)
variable (g:Extension L.val P n t)(ht:q≤ 1)(H:Frequency L n q)
local notation "τm"=> mstar L.val
abbrev priceB(c:Clip):ℝ:= (90000*‖Complex.reCLM‖)/direct_cost c
local notation "tB"=> P.threshold
abbrev rollFX (c:Clip)(P:BudgetPoint)(L:ℕ)(a:ℝ):= priceB c*P.threshold⁻¹^2*a*Real.exp (- (mstar L:ℝ))
abbrev rollGX (j:ℕ)(u:1≤ j)(L:ℕ)(a h:ℝ):= aimC j u * (Real.exp (-(mstar L:ℝ))*a/h^2)

abbrev priceU (j:ℕ)(u:1 ≤j)(L:ℕ)(a:ℝ):= |u_early| * (aimC j u *(Real.exp (-(mstar L:ℝ))*a))
abbrev priceXU (c:Clip)(j:ℕ)(u:1 ≤j)(L:ℕ)(P:BudgetPoint)(a z:ℝ):= profitX (priceU j u L a) P L + rollFX c P L a*|z|
abbrev priceYT(c:Clip)(j:ℕ)(u:1 ≤j)(L:ℕ)(P:BudgetPoint)(a z:ℝ):= profitY (priceU j u L a) P L+ rollFX c P L a*|z|
structure Joint (P:BudgetPoint)(L:Side)(F:RegBudget n)(Q:Cusp n)(R:PathData SU.group)(c:Clip)(V:RegBudget n)(Δ h a d b q:ℝ) (j:ℕ)(M:Male) :Prop where
 piece : Piece P h R c V Q Δ a d
 crown : gaugeTest q (F+V) P=0 ∧ waveTest q (F+V) j M=0
 house : Lord P (F+V) b h L.val
 warped : Sour.BondL.mintv (treeΘ P L.val) j M (F+V)

lemma LordAdd (X V:RegBudget n)(v:IncX Utrue X P a b)(k:IncX Utrue V P a C)(p:1 ≤ a):gaugeTest q (X+V) P=gaugeTest q X P+gaugeTest q V P:=by
 have ht:= logic_gauge (P:=P) (n:=n) q p; apply eq_add_of_sub_eq; rw [←ht.earnings (X+V) V ⟨_,addT P v k⟩ ⟨_,k⟩,add_sub_cancel_right]
lemma Kit.freeK {V:RegBudget n}{Z:Cusp n} (p:Kit P h R c L.val V Z A d a):Ionic P L.val V∧ StackL V (treeΘ P L.val)=0:=by
 refine ⟨fun i _ t=> by rw [p.rest i t]; exact Beau.none_q _,?_⟩; unfold StackL; apply sum_eq_zero; intro i q; rw [p.rest i (show shortHub P L.val i from (mem_filter.mp q).2)]; exact Neon.orbit_0 _
variable (X:Lord P F a h L.val)(q0: waveTest q F j M=0)(t':P=Pitching.Focus.epoch x)(V':Vast L.val P.B n)(v':4≤ (More n).val)(r':0<r)
include X kQ Ω H u g χ p q0 t' V' v' r'
local notation "Rμ_"=> priceU j u L.val a
set_option maxHeartbeats 1200000 in
lemma knit_budget (L0:4 ≤L.val) : let X0:=priceXU c j u L.val P a z0; let Y0:=priceYT c j u L.val P a z1; |db| ≤ rollFX c P L.val a ∧ Joint P L F yp R c xp db h X0 Y0 (a+X0) q j M:=by
 intro X0 Y0; have hp:=χ.floor; let v:= kQ.toPiece; let U:= transverse (s:=n) q; let V:= (v.kinSmooth hp U); let Kc:= hT; have he:direct_cost c ≤ Kc:=macy Ω H _ V; have ht:0< Kc:=(posed c).trans_le he; let A:=db; let Z':RegBudget n:=xp; let Z:=dm; let xq:= NetX t P (lmap χ Z); let Xp:= (A • Q); let α:= F+(xq+Xp); let ξ:= Real.exp (-(mstar L.val:ℝ))
 obtain ⟨u0,t0,g₁⟩:= (show P.order =6 ∧ P.power=2 ∧ P.supportExponent=1 from (by rw [t']; exact let_X HI x));
 have hv: |db|≤ rollFX c P L.val a:=by
    unfold shiftB rollFX; rw [abs_div,abs_neg,abs_of_pos ht]; obtain hh:= conductor X.tax hp v' H t0 g₁ V' X.theme; refine le_trans (div_le_div_of_nonneg_left (abs_nonneg _) (posed c) he) ((div_le_div_of_nonneg_right hh (posed c).le).trans_eq (by unfold priceB; ring))
 have H1: ‖Z‖ ≤ rollGX j u L.val a h:=by
    obtain e:= (cake u g₁ t0 X.tax hp H (M:=M)); rw [q0,zero_sub,norm_neg] at e; exact e
 have hc: u_early*h^2*‖Z‖≤Rμ_:=by
    have hk:u_early*h^2*‖Z‖ ≤ |u_early| *h^2*‖Z‖:=by gcongr; exact le_abs_self _
    exact hk.trans ((mul_le_mul_of_nonneg_left H1 (by positivity)).trans_eq (by unfold rollGX priceU; field))
 let XF:= upgradeI P Utrue (wageL χ p r' x t' dm) hc
 obtain ⟨e,e',D'⟩:= realizeX t g L0 XF hp R c
 let W:= kQ.scale A; obtain ⟨A',w⟩:= Kit.freeK W; let T₁:= X.tax
 let Xr:= |A| * z0; let Xt:=|A| *z1; let c0:= priceU j u L.val a
 let E:=profitX c0 P L.val+Xr; let E':= profitY c0 P L.val+Xt
 have ux:E≤X0:=add_le_add le_rfl ((mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hv (abs_nonneg _)))
 have ut:E'≤ Y0:=add_le_add le_rfl ((mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hv (abs_nonneg _)))
 let pV:= W.toPiece; have qΨ:Piece P h R c Z' yp A E E':= by simpa only [zero_add,mul_one] using e.add pV
 have e1: Lord P Z' X0 h L.val:= ((Lord.merge (show Lord P xq _ _ _ from ⟨e.hire,e'⟩) (zero_le_one.trans hp) (show Lord P Xp _ _ _ from ⟨pV.hire,A'⟩)).uprate ux)
 let eU:= X.merge (zero_le_one.trans hp) e1
 refine ⟨hv,⟨ { qΨ with hire:=upgradeI _ _ qΨ.hire ux, cannon:=qΨ.cannon.purse ut },?_,eU,?_⟩⟩
 · refine ⟨?_,?_⟩; · rw [LordAdd _ _ T₁ e1.tax hp,qΨ.bT hp q V]; change gaugeTest q F P+(-gaugeTest q F P/Kc)*Kc=0; rw [div_mul_cancel₀ _ ht.ne']; abel
   rw [←pointE,mark_T,Plum.piece_stack qΨ,add_zero]; exact q0
 let T:=treeΘ (X:=n) P L.val; have hk:= (gem (plea n P L.val) eU.tax hp t0 u M 0 (fun i _=> Nat.zero_le _)).axisP
 let Y:= StackL (F+Z') T; let g:=pointW n j u M; have hd:g Y=0:=by
    unfold Y; change g (StackL (F+(xq+Xp)) T)=_; rw [mark_T,mark_T,w,add_zero,D',map_add,show g _= - Z from vaultY χ r' u dm (fun i h=>mem_filter.mpr ⟨mem_univ _,h⟩)]
    change g (StackL F T)+ -g (StackL F T)=0; abel
 have hn: τ_ j M Y=0 := by rw [←pointCash u hk,hd]; rfl
 let v:=normalization j u M hk; refine ⟨v.1,fun i=>(((Psy j u M hk).age i).hasDerivAt).congr_deriv ?_⟩
 change zest j M (WW Y) i=0; rw [v.2.2]; change _⊗ₖ τ_ j M Y=0; simp only [hn,Matrix.kronecker_zero]
end TestW
end Test
end YM.CF.Py.Rate
