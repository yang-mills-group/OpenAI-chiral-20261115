import YM.CF.DPress.Act.Amber
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {x:ℝ}{C:Tew W}{β:ℝ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}
 {P_:Campus C}
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Arco WagesC
open UVNext.PricedKernels Work.F03 WilsonStartup
namespace Act
open Harvester WagesC Urban
variable {A:Harvester P_}{ξ:ℝ→ℝ}
structure Silo (A: Harvester P_)(ξ:ℝ→ℝ)(Q:Maud x C G S)(O: Shore0) where
 p : Penny Q O
 u : Urban P_ Q O
 Y : Harvester.Field A Q
 v : Amber (Q:=Q) u.docks A ξ O
variable (T: Silo A ξ Q O){α:ℝ}
local notation "vΠ"=> mid N B
local notation "vℓ"=> Q.X.p
local notation "Nre"=> ‖Complex.reCLM‖
namespace Silo
variable (Wν:Blend (mid N B) A.μ)(α:ℝ)
abbrev Can(Q:Maud x C G S)(P_:Campus C)(p α:ℝ):Prop:= |α|≤ phase_v Q.X.p (P_.tax p)
abbrev ok_turn (s: Sweep (mid N B)):Prop:= α=0∨ Wν.even s
variable (t:Can Q P_ b α)
include Q in
lemma equδ : (S.patch.L:ℕ)= R.L.val:= Q.pact
include T in
lemma Lone : 1 < R.L.val:=by have ht:=V.tallX; omega
lemma base0 (h:0≤b): Can Q P_ b 0:=by unfold Can phase_v; unfold Campus.tax; rw [abs_zero]; have hp:= P_.posC; positivity
lemma ease{d':ℝ}(p:b≤d') (t:Can Q P_ b α):Can Q P_ d' α:=by
 apply t.trans; unfold phase_v; apply div_le_div_of_nonneg_right _ (by positivity); apply mul_le_mul_of_nonneg_left _ (by positivity); apply mul_le_mul_of_nonneg_left p; have he:= P_.posC; positivity
include t T
abbrev δτ (A:Harvester P_)(v:ℝ):= A.C_H*‖Complex.reCLM‖* P_.tax v -- charge α swell
lemma ferr_a {v:ℝ}(p:v≤ A.C_H) : v*|α| * (vℓ).threshold^2 ≤ δτ A b:=by
 refine ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right p (abs_nonneg _)) (sq_nonneg _))).trans ?_; unfold δτ; have h:=mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos Q.X.p.threshold_pos 2)).1 (show _ ≤ phase_v (vℓ) _ from t)) A.Hpos.le; rw [mul_assoc,mul_assoc]; exact h
lemma wE : IncX Utrue (αLan (n:=vΠ) α) Q.X.p C.h (δτ A b):=by
 have he:= widthP Q.X.p T.Y.wings (h:=C.h) α; refine Tutor.loosen he (ferr_a T α t ?_); rw [A.payW (Q:=Q)]; unfold Harvester.ferr; linarith [abs_nonneg (Blend.ζP (vℓ) A.Γ A.μ),le_abs_self (ρtax A.Γ A.μ (vℓ)),abs_nonneg (ρtax A.Γ A.μ (vℓ))] -- tune arg. t overlap binder {t}. merge
lemma wS : IncX (ok_turn Wν α) (Wν.Sα α) Q.X.p C.h (δτ A b):=by
 let U:= Wν.priceS _ T.Y.wings C.uB α; constructor
 · refine let Z:IncX primeU (Wν.Sα α) Q.X.p C.h (δτ A b):=(billP (n:=vΠ) _ C.uB).toReceipt.relax (⟨U.weight,fun _ t=>False.elim t⟩:IncX primeU _ _ _ _ ) (ferr_a T α t ?_); Z.weight
   rw [A.payW (Q:=Q)]; unfold Harvester.ferr; linarith [abs_nonneg (Blend.ζP (vℓ) A.Γ A.μ),le_abs_self (ρtax A.Γ A.μ (vℓ)),abs_nonneg (ρtax A.Γ A.μ (vℓ))]
 intro s q; rcases q with p | v; rw [p,Wν.s0]; exact rust (Q:=Utrue) s trivial; exact U.face s v
lemma wZ : ZL Q.X.p C.h (lev2 Q.X.p) (Wν.Zα α) (δτ A b):=by
 have he: ZL Q.X.p C.h (lev2 Q.X.p) (Wν.Zα α) (Blend.ζP (vℓ) A.Γ A.μ * |α| * (vℓ).threshold^2):=(mantle _ _ _ C.uB _).2 ⟨_,Wν.rentQ _ T.Y.wings C.uB _,Wν.Ωbig Q.X.p T.Y.wings C.uB α⟩; refine (νreg (n:=vΠ) _ _ _ false C.uB).toReceipt.relax he (ferr_a T α t ?_); rw [A.payW (Q:=Q)]; unfold Harvester.ferr; linarith [le_abs_self (Blend.ζP (vℓ) A.Γ A.μ),abs_nonneg (ρtax A.Γ A.μ (vℓ))]
lemma δalpha : aora Q.X.p R.L.val (αLan (n:=vΠ) α) = α:= δPawn Q.X.p T.Y.wings α T.Lone -- t intentionally used? omit
omit t T
lemma τZ : honest (ok_turn Wν α) (Wν.Zα α):=by
 intro s hp i v; rcases hp with p|v'; · rw [p,Wν.z0]; exact fun _ _ _ _=> (map_zero _).symm
 exact fun j K _ _=> Wν.colorZ α s v' j i K
end Silo
end Act
end YM.CF.Py.Kay
