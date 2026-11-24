import YM.CF.Vp929.Match.Caboose
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
variable {d e η t z g B':ℝ} {j k k' m n l:ℕ}
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
open Trees Footprint Iva Eire
open Jade
open Sour Haro Tap Ione Larch Nor Glyph SupportP
set_option maxHeartbeats 800000
variable (P_:BudgetPoint)(F G H:ℝ→ℝ)
local notation "Pz"=> hall_P P_
local notation "gL"=> Scales.g SU.group R.L
local notation "zP"=> rainX R 1
open Py.Rate
abbrev catap (W:ℝ):ℝ:=512*W
local notation "Zv"=> rainX R 2

lemma altPulse {r a b c W γ d S' v u θ z ζ W':ℝ}{P':BudgetPoint}(R:Pace P' a b c W r γ d S' v u θ z ζ (512*W'))(p:0 ≤ r):Pace P' a b c W r γ d S' v u θ z ζ W':=by
 refine {R with sale:=?_ }; let Z:= tiltB W' P'*(u+φcape P' a b c W+tintK P' (rentΦ P' γ d) θ z) / W^2; have he: (512:ℝ)*Z≤r:=by
    apply le_trans ?_ R.sale; unfold Z tiltB; exact le_of_eq (by ring)
 change Z≤r; linarith

-- use ores with twice the reservation argument. Can then invoke nova_X also to
-- prepay *double kernel prices* (for the projection kernel); with time=2 in its Timer (not
-- doubling again). This still gets the real/open invocation with Pace itself.
lemma lobes {A b c a h:ℝ}(p:0 < A)(L:lobe (2*A) h (γ₀ P_ a b c 0 h) P_): lobe A h (γ₀ P_ a b c 0 h) P_ ∧ lobe A h (γ₀ P_ a (2*b) (2*c) 0 h) P_:=by
 have he:γ₀ P_ a (2*b) (2*c) 0 h= 2*γ₀ P_ a b c 0 h:=by unfold γ₀ cap2; ring
 unfold lobe at *; have hx:= desire P_ p; rw [show tiltB (2*A) P_=2*tiltB A P_ from (by unfold tiltB; ring)] at L
 constructor
 · refine L.trans ?_; gcongr; linarith
 rw [he]; refine (mul_le_mul_of_nonneg_left L (by norm_num : (0:ℝ)≤2)).trans_eq ?_; field

structure Mood (P:BudgetPoint)(A W a b c r g S' v u z ζ Ψ₁ Γ₁ Θ₁ D₁ Γ₂ Θ₂ D₂:ℝ):Prop where

 team: 0 < g
 leo:0<A
 radius:0<r
 leg:1≤ζ
 lead:0<z
 speed: Pace P a (b*r) (c*r) W r Γ₁ D₁ S' v u Θ₁ z ζ A
 transit: Pace P a (2*b*r) (2*c*r) W r Γ₂ D₂ S' v u Θ₂ z ζ A
 dust: Dq P a (b*r) (c*r) u Θ₁ z W Γ₁ D₁ r ≤ Ψ₁
 lens: 2*tintK P (rentΦ P Γ₂ D₂) Θ₂ z ≤ g^2
 plume: φcape P a (b*r) (c*r) W≤ u+g^2
 cap: u+φcape P a (b*r) (c*r) W+g^2+Glyph.cap1 P (BondL.øK r) W ≤ Ψ₁
 sky: tiltB (A/512) P*(3*(u+g^2))/W^2 < r/256
 mark_r: r=Rone (tiltB A P) u g W
variable (A W a b c:ℝ)(p:0 < a)(q:0 <A)(u:1 ≤ W)(L_:lobe (2*A) W (γ₀ P_ a b c 0 W) P_)
include R p q u L_
abbrev echoes (R:Patch)(P:BudgetPoint)(A:ℝ)(U:ℝ→ℝ)(x:ℝ):=νC P A * (U x+(Scales.g SU.group R.L x)^2)
local notation "rD"=> Rtor P_ R A W F
lemma event_mood (f:sizeK R.L 2 F)(g:sizeK R.L 1 G)(h:sizeK R.L 3 H)(v:∀ᶠ x in atTop,0 ≤ F x):∃ Γ' Θ' D' Γ₂ Θ₂ D₂:ℝ→ℝ,sizeK R.L 2 rD ∧ sizeK R.L 1 Γ' ∧ sizeK R.L 1 Θ' ∧ sizeK R.L 2 D'∧ sizeK R.L 1 Γ₂∧ sizeK R.L 1 Θ₂∧ sizeK R.L 2 D₂∧ ∀ᶠ x in atTop, Mood (Pz x) A W a b c (rD x) (gL x) (G x) (H x) (F x) (zP x) (Zv x) (echoes R P_ A F x) (Γ' x) (Θ' x) (D' x) (Γ₂ x) (Θ₂ x) (D₂ x) := by
 obtain ⟨T,T'⟩:=lobes P_ q L_
 obtain ⟨X,Y,D',hX,hY,hD,hv,_,wP⟩:= nova_X (R:=R) P_ F G H A W a b c p q u T f g h
 obtain ⟨X',Y',D0,hX',hY',hD',_,_,wP2⟩:= nova_X P_ F G H A W a (2*b) (2*c) p q u T' f g h
 let Λ(x):=tintK (Pz x) (rentΦ (Pz x) (X' x) (D0 x)) (Y' x) (zP x); have hΛ:sizeK R.L 3 Λ:= σΩ P_ Y' _ hY' (pole_Q P_ _ _ hX' hD')
 refine ⟨X,Y,D',X',Y',D0,hv,hX,hY,hD,hX',hY',hD',?_⟩
 filter_upwards [wP,wP2,v,pill_R (k:=2) _ zero_lt_one (hΛ.scale 2),spice_R (R:=R)] with x w w' t h v
 obtain ⟨hr,_,_,pR,H⟩:=w; let L:=Rone (tiltB A P_) (F x) (gL x) W; let P:=Pz x
 have hT: tiltB A P=tiltB A P_:=by unfold P tiltB; rw [(let_X ..).2.1]
 have he:= probate_0 (x:=x) P_ F q u v.2.2 T (gL x^2) le_rfl;
 refine ⟨v.2.2,q,hr,v.2.1,v.1,pR,w'.2.2.2.1,H t,h.le.trans (le_of_eq (one_mul _)), he.1.trans_eq ?_, he.2.2 t, ?_,?_ ⟩
 · rw [abs_of_nonneg t]
 · let C:= tiltB (A/512) P; have hc: tiltB A P_=512*C:=by rw [←hT]; unfold tiltB C; ring
   have hp:C>0:= desire P (by positivity)
   have l:(rD x)=512*4*C*(F x+gL x ^2)/W^2:=by unfold Rtor Rone; rw [hc,abs_of_nonneg t]; ring
   rw [l]; change C*(3*(F x+gL x^2))/W^2< _; have hg:=v.2.2; set V:=F x+(gL x)^2; have hV:0 < C*V/W^2:=by unfold V; positivity
   rw [show C*(3*V) / W^2=3*(C*V/W^2) from (by ring),show 512*4*C*V/W^2/256=8*(C*V/W^2) from (by ring)]; linarith only [hV]
 rw [show (Pz x)=P from rfl,hT]
end YM.CF.Py
