import Weft.Hut
import Finance.Price
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Moto Neon Tune Ione Nacre Both Compass ThinGauge
local notation "mH"=>mid N B
variable {uτ Δτ χτ g0 g1 g2 κτ Q1 Q2 Q3 Oτ:ℝ}{kκ:ℕ}(C0:Headquarters V U X Y S G G₀ G₁ Xi q kL Hh Vp Va χτ Δτ uτ g0 g1 g2 κτ Q1 Q2 Q3 Oτ kκ)
variable (P':Bool→Pin (mid N B))
local notation "dT"=> duty_Q X.p.order X.p.power
variable {AΦ rP rC:ℝ}
structure Rates (L:Side) (A Δ χ h g0 g1 g2 rP rC:ℝ)(X:GramM (mid N B))(Y:GramM (mid P B))(G:Ratio (mid N B) (mid P B))(P':Bool→ Pin (mid N B)):Prop where
  cash_o:ThinGauge.Open g0 Δ (Ione.duty_Q X.p.order X.p.power) A ((L.val:ℝ)⁻¹)
  night:0<rP
  noon:rP≤rC
  day:rC≤2*rP
  wallet:0≤χ
  discount:χ≤ ((L.val:ℝ)⁻¹)^5*rP
  mentor:((L.val:ℝ)⁻¹)^4/4≤ Compass.tint0 L X.p Y.p
  value:Compass.tint0 L X.p Y.p ≤4*((L.val:ℝ)⁻¹)^4
  red :∀ (b:Bool)(o:Site (mid N B)),αPrice L h (A*rP) χ g0 g1 g2 (soot rP b) (coat (P' b).blade) X.p Y.p (nun_ω Y.F (Hove.heel G o))
-- rulers,P.Capt on absolute.. not controlling rates varying? |β^-1|.
abbrev Xη (L:Side):=(L.val:ℝ)⁻¹
abbrev invmain : ℝ:=4*Real.exp 1 + ThinGauge.slope/2
structure Niche (L:Side)(U Z:ℝ):Prop where
  non:U≠ 0
  amp:|U|≤ Bmain / Xη L ^ 4
  tax:|Z|≤1/8
  back:|U⁻¹| ≤ invmain * Xη L^4
local notation "D0"=> Xη R.L
local notation "W0"=> κBill Y G R.L χτ Hh
variable (pR:Rates R.L AΦ Δτ χτ Hh g0 g1 g2 rP rC X Y G P')
    (hT:IncX primeU Y.F Y.p Hh 1)(tY:Pant_W (N:=P) Y)(hX:1 ≤ Hh)
include pR hT hX tY
lemma crateS :∃ U' Z':ℝ, Niche R.L U' Z' ∧
    (let a:= boost (Xη R.L); let r:=AΦ*rP; let z:= (P' false).blade; let w:= (P' true).blade
     U'*z=rC ∧ Z'*z+w=0 ∧ (∀ o:Site mH,let k(b:Bool):=dT*Δτ* W0 o r (soot rP b); |U'| *k false≤AΦ*rC/4∧ a*(|Z'| *k false + k true)≤AΦ*rC/4)):=by
 obtain ⟨μ,m⟩:= Bolten Y tY; let ζt:= D0; let r:=rP; let Q:=rC; let z:=(P' false).blade; let w:=(P' true).blade; let U':=Q/z; let Z':= -w/z; let a:= boost D0
 let ψ:=χτ
 have h0:=pR.cash_o; have ht:=h0.credit; have hx:=pR.discount; have h':= κLife (N:=P) (B:=B) (0:Site (mid P B)) Y hT hX; rw [m,Complex.norm_real,Real.norm_eq_abs] at h'
 let t:=Compass.tint0 R.L X.p Y.p
 have hk:=pR.red false 0; have hv:=pR.red true 0; rw [m] at hk hv; have hx0:=pR.night; have hp:=pR.cash_o.asset; have ha:0≤ AΦ:=by linarith
 have hw0 : ‖z-t*μ*r‖ ≤ ThinGauge.lowerCost g0 AΦ * D0^5*r:= (Real.norm_eq_abs _).trans_le (κRate R.L hx0.le ha pR.wallet hx rP h'.2 (abs_of_pos hx0).le Hh hk)
 have hw1 : ‖w‖ ≤ ThinGauge.lowerCost g0 AΦ * D0^5*r:=by
    have e:=κRate (A:=AΦ) R.L hx0.le ha pR.wallet hx 0 h'.2 (by rw [abs_zero]; linarith) Hh hv; rw [mul_zero,sub_zero] at e; rw [Real.norm_eq_abs]; exact e
 obtain ⟨hz,hu,hv,er,eq,Lt,Ut⟩:= soloKing h0 pR.night pR.day pR.noon t z w hw0 hw1 pR.mentor h'.1
 have hq:Q>0:=pR.night.trans_le pR.noon; have hr:r>0:=pR.night
 refine ⟨U',Z',⟨div_ne_zero hq.ne' hz,hu,hv.trans ?_,?_⟩,er,eq,fun o=>?_⟩; · rw [mul_comm]; exact h0.peak
 · have hd:0<D0:=h0.hm; have hb:0≤ t:= (by have h:0<D0^4/4:=(by positivity); exact h.le.trans pR.mentor)
   rw [inv_div,abs_div,div_le_iff₀ (abs_pos.mpr hq.ne'),abs_of_pos hq]
   have hF:= h0.faith; have he:D0^4>0:=pow_pos h0.hm _
   calc
     |z| ≤ |z-t*μ*r| + |t*μ*r|:= by have ht: z=z-t*μ*r+t*μ*r:= (sub_add_cancel z _).symm; nth_rw 1 [ht]; exact abs_add_le ..
     _ ≤ (ThinGauge.lowerCost g0 AΦ * D0^5*r) + ((4*D0^4)*Real.exp 1)*r:=by
        rw [Real.norm_eq_abs] at hw0; rw [abs_mul,abs_mul,abs_of_nonneg hr.le,abs_of_nonneg hb]; exact add_le_add hw0 (mul_le_mul_of_nonneg_right (mul_le_mul pR.value h'.2 (abs_nonneg _) (by positivity)) hr.le)
     _ ≤ invmain*D0^4*r:=by unfold invmain; nlinarith only [mul_le_mul_of_nonneg_right hF (mul_nonneg he.le hr.le)]
     _ ≤ _:=mul_le_mul_of_nonneg_left pR.noon (show 0≤ invmain*D0^4 from by unfold invmain; have h:=slope_live; positivity)
 intro k
 have hm:= mint_R (r:=r) (q:=Hh) R.L h0 hr.le h'.2 pR.wallet hx
 have he: k false≤ yolk Δτ dT*D0^4*r ∧ k true≤ ThinGauge.shell Δτ dT AΦ *D0^5*r:=by unfold k κBill; rw [m]; simp_rw [mul_assoc (Ione.duty_Q X.p.order X.p.power) Δτ]; exact hm
 exact ⟨(mul_le_mul_of_nonneg_left he.1 (abs_nonneg U')).trans Lt, (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he.1 (abs_nonneg Z')) he.2) (show 0≤boost D0 from (div_pos gain_pos (pow_pos h0.hm _)).le)).trans Ut⟩
#print axioms crateS
end Dyad
end YM.CF.Py
end
