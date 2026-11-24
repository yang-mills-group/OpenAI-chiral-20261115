import YM.CF.DPress.Crew.Issue
import YM.CF.DPress.Crew.Over
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay Glyph Nacre Docket Tutor
variable {N:Side}{P:BudgetPoint}{h W a b c t M L u e:ℝ}{T S:BeatL N}{D:Docket P}{q:ℕ}{F:Scree.Loom N}(A:BondL T S (body_Q 1) b c a e)(v:Room F P e u h q)
variable {K:ℝ}{X Y:Cusp N}(G:RegBudget N)(τ:Ids N) (j:ℕ)(m:Male)(χ:Finset (Scree.Hub N))
open Flight -- ASCII
namespace Resident
local notation "rΩ"=> Tutor.RadP P W h K
local notation "Ld"=> StackL
variable (H:Tutor P h W a b c)(p:pureB A 1) (w0:0<K)(tK:Ride P h a b c M D)(hK:Tutor.RadP P W h K≤M)(hk:D.Tr≤K/32) (uK:1≤j)(hc0:liveB χ)(hz:∀ i:Scree.Hub N,coverNumber P.B i.val.2≤1 → i∈χ) (Q: Resident D X q h)
open LinearT DPress.Fees.Moral
variable {ε:ℝ}(U V:ΘS (RadP P W h K))(Z: Resident D Y q h)(G':RegBudget N)
variable (g:IncX Utrue (G'-G) P h (K*ε/4)) (E:D.Pair h ε X Y (cipherK q))
local notation "ht0"=> H.bright w0
local notation "α"=> (Flight.hΔ V U)
include H p Q w0 tK hK g E hk Z
abbrev Ψk(K ε αv:ℝ):= K*(9*ε+3*αv)/32
lemma τacct : IncX Utrue (DE A v G' τ Y V.val-DE A v G τ X U.val) P h (Ψk K ε (hΔ V U)):=by
 let t:=RadP P W h K; have hν:= χW A v Z H p hK tK (H.bright w0).le V; have hz:= χW A v Q H p hK tK (H.bright w0).le U; have hf:= (curvePower A v E U V ht0 (H.generous A v ht0 hK tK)).feeE
 have hC:= receiptR v.heil τ (LinearT.Bsym hν.1 hz.1) (TurfB hν.2.1 hz.2.1) hf; let z:=Flight.debt V U ε; let D':=(DE A v G' τ Y V.val-DE A v G τ X U.val)
 unfold DE; rw [add_sub_add_comm,add_sub_add_comm,←LinearT.stepUp,←map_sub]; refine Tutor.loosen (Ione.addT _ (Ione.addT _ g (H.pt_W A v)) hC) ?_
 have hv':0 < W:=H.first; have ht:= lt_of_lt_of_le zero_lt_one H.boot; let β:=tiltB W P; have ht':str W P h ‖V.val-U.val‖ = K*α/16:=by
    rw [←Flight.balance V U ht0]; unfold str; field_simp [hv'.ne']; unfold RadP; field_simp [hv'.ne']; ring -- heartbeat
 change K*ε/4+_+Nor.reserveT P.power P.order P.B 1*(D.Nr*z) ≤ _; rw [ht',←mul_assoc (Nor.reserveT ..)]; have hu:D.Tr*z≤K/32*z:=mul_le_mul_of_nonneg_right hk (add_nonneg E.gear0 (Flight.nn V U ht0)); change _+ D.Tr * z ≤ _; unfold z Flight.debt at *; unfold Ψk; linarith
include uK hc0
lemma αQt : ‖Resident.scaleZ A v G' τ j m χ Y V.val - Resident.scaleZ A v G τ j m χ X U.val‖/RadP P W h K ≤ (9*ε+3* (hΔ V U))/256 :=by
 let L:=ionX (n:=N) j uK m; let Y':=DE A v G' τ Y V.val; let X':=DE A v G τ X U.val; change ‖L _-L _‖/ _ ≤ _; rw [←map_sub L,←Kay.stack_sub]
 have hp:= τacct A v G τ H p w0 tK hK hk Q U V Z G' g E; have hv:= Haro.axeK χ P m (Y'-X') H.lens hp hc0 H.boot H.order j uK; apply (div_le_iff₀ ht0).2; have he:= lt_of_lt_of_le zero_lt_one H.boot; refine hv.2.2.trans_eq ?_; unfold Ψk RadP tiltB; ring -- ring inverse exponents
-- assignment when solved, not applying maps continuity yet. witness spec.
omit H p Q w0 tK hK hk g E uK hc0 Z
abbrev flatK (X:Cusp N)(U:Θ) : RegBudget N:= DE A v G τ X U+v.L_Q A U
abbrev Settle (X:Cusp N)(U: Θ): Prop:= U.val=Resident.scaleZ A v G τ j m χ X U
variable (hx:Settle A v G τ j m χ X U.val)(hy:Settle A v G' τ j m χ Y V.val)
include H p Q w0 tK hK hk g E uK hc0 Z hx hy
lemma σοl : hΔ V U ≤ 2*ε:=by
 obtain ht:= αQt A v G τ j m χ H p w0 tK hK hk uK hc0 Q U V Z G' g E; rw [←show (U.val).val=_ from hx,← show (V.val).val=_ from hy] at ht; change hΔ V U ≤ _ at ht; apply show ∀ z:ℝ,z≤(9*ε+3*z)/256→z≤ 2*ε from fun z h=> (by linarith only [h,E.gear0]); exact ht
abbrev Ωf(K ε h t CL:ℝ):= K*ε+CL*(2*ε*t)*h^2 -- K*t? Ψk ≤ 1/2 K ε
open Docket
lemma σωl : IncX Utrue (flatK A v G' τ Y V.val-flatK A v G τ X U.val) P h (Ωf K ε h (RadP P W h K) (Sp P)):=by
 unfold flatK; rw [add_sub_add_comm,←map_sub]; refine Tutor.loosen (Ione.addT P (τacct A v G τ H p w0 tK hK hk Q U V Z G' g E) (H.pt_L A v p)) ?_
 have hp:=σοl A v G τ j m χ H p w0 tK hK hk uK hc0 Q U V Z G' g E hx hy; refine add_le_add ?_ (show Tutor.spot P h _≤ _ from ?_)
 · unfold Ψk; let H:∀ z:ℝ,z≤2*ε→ _ := fun z (p:z≤2*ε) => show K*(9*ε+3*z)/32 ≤ K*ε from by nlinarith [E.gear0]
   exact H _ hp
 unfold Tutor.spot; gcongr; exact mul_nonneg (abs_nonneg _) Cad.pos.le; apply (div_le_iff₀ ht0).1 hp -- gcongr
end Resident
end YM.CF.Sour.Heath
