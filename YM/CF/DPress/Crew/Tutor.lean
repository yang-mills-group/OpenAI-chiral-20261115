import YM.CF.DPress.Rise.Wove
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
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay Glyph Nacre
open scoped YM.CF.Mew
variable {P:BudgetPoint}{h W a b c:ℝ}
structure Tutor (P:BudgetPoint)(h W a b c:ℝ) : Prop where
 first: 0 < W
 lens : Haro.Lens W
 boot : 1 ≤ h
 posA : 0<a
 year : a≤1
 ny : 2*P.supportExponent*Fief.tileN 1 ≤ a/2*P.B
 nf : 2*(wu P+2)*Fief.tileN 1 ≤ a/2/2*P.B
 order : 1 ≤ P.power
 lobeQ : Py.lobe ((32*Cad.rent)*W) h (γ₀ P a b c 0 h) P
namespace Tutor
abbrev Lc (P:BudgetPoint)(h t:ℝ) := cap1 P (BondL.øK (Cad.rent*t)) h
abbrev Sp (P:BudgetPoint) := |u0 P| *Cad.rent
abbrev spot (P:BudgetPoint)(h t:ℝ) := Sp P * t *h^2
abbrev Wc (P:BudgetPoint)(h a b c t:ℝ) := Glyph.cap2 P (Mercer.priceN t c) h a+ Glyph.cap2 P (Mercer.priceN t b) 1 a
abbrev str (W:ℝ)(P:BudgetPoint)(h t:ℝ) := h^2/(128*tiltB W P)* t
lemma seize (t:ℝ)(u:0≤t): Lc P h t ≤ spot P h t:=by
 rw [show Lc P h t = u0 P*Cad.rent*t*h^2 from by unfold Lc u0 cap1 BondL.øK; ring]; unfold Tutor.spot Sp; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self ..) Cad.pos.le) u) (by positivity)
variable (T:Tutor P h W a b c)
include T
lemma heat : 0< tiltB W P := by unfold tiltB; have hg:=T.first; positivity
lemma κpc(t:ℝ)(v:0≤t): Wc P h a b c t ≤ str W P h t:=by
 rw [show Wc P h a b c t = γ₀ P a b c 0 h*(Cad.rent*t) from (by unfold Wc γ₀ cap2 Mercer.priceN; ring)]; refine (mul_le_mul_of_nonneg_right T.lobeQ (mul_nonneg Cad.pos.le v)).trans_eq ?_; change h^2/(4*tiltB _ _)*_= _; rw [show tiltB (32*Cad.rent*W) P=32*Cad.rent*(tiltB W P) from (by unfold tiltB; ring)]; unfold str; have he:=T.heat; have ht:=Cad.pos; field_simp; ring
abbrev RadP (P:BudgetPoint)(W h K:ℝ):= 8* (tiltB W P)* K/h^2
lemma bright {K:ℝ}(s:0<K): 0 < RadP P W h K:=by unfold RadP; have he:=T.heat; have hp:= lt_of_lt_of_le zero_lt_one T.boot; positivity
lemma affordable (D:Docket P){K:ℝ}(s:0<K)(u:D.Tr ≤ K/32): tiltB W P*(K+ Wc P h a b c (RadP P W h K)+ D.Tr)/h^2 ≤ RadP P W h K:=by
 unfold RadP; let t:= RadP P W h K; let V:=tiltB W P; have he:=T.heat; have hK:V>0:=he; have hp:=lt_of_lt_of_le zero_lt_one T.boot; apply div_le_div_of_nonneg_right _ (by positivity); have ht: str W P h t= K/16:=by unfold str t RadP; field_simp [T.first.ne'] <;> first|ring|skip
 have hq: Wc P h a b c t ≤ K/16:= (T.κpc t (T.bright s).le).trans_eq ht; change V*(K+Wc P h a b c t+D.Tr) ≤ 8*V*K; nlinarith [hq]
end Tutor
end YM.CF.Sour.Heath
