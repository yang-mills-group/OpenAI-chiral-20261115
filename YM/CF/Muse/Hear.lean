import YM.CF.Muse.Wight
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Haro Feu Feu.Corset Nor
open Levier Haro Feu Feu.Corset Nor
abbrev pitchP (s a:ℝ)(l n:ℕ):ℝ:= lorp s (l+90) n (population*a)
abbrev slashP (H G:ℝ)(σ n k:ℝ)(u v W:ℝ):=H/(G^2)+(σ*n*W^2)+k*u^2+v*H -- remove
lemma lorp_v(s A:ℝ)(L:Side)(l n:ℕ):lorp s (l+90) n (population*(A*followV [] L))=pitchP s A l n * (L.val:ℝ)⁻¹^3:=by
 let t:ℝ:=L.val; have ht:0<t:=by unfold t; positivity
 have hh: followV [] L ^2=t⁻¹^3:=by unfold followV; change (Real.sqrt t/t^2)^2=_; rw [div_pow,Real.sq_sqrt ht.le]; field_simp <;> ring
 unfold pitchP lorp; rw [←hh]; ring
lemma levy_m(k:ℕ)(ε e:ℝ): levyC k 1 (ε*e)= levyC k 1 ε * e:=by unfold levyC θ_I; ring
abbrev priceW (s v k h:ℝ)(l n:ℕ):=v*h -- remove
abbrev keyS (s a t D:ℝ)(l n k:ℕ):=2+ t^2*pitchP s a l n * levyC k 1 D
local notation "Lr"=> (R.L.val:ℝ)
local notation "ζr"=> gritY
lemma rate_v (A0 A1 A2:ℝ)(v:0 < A1):∀ᶠ z:ℝ in atTop,A0 / z^2 ≤ A1:=by
 have he:= tendsto_pow_atTop (n:=2) (α:=ℝ) (by decide :2≠0); have hv:= he.inv_tendsto_atTop; have hX:Tendsto (fun z:ℝ=> A0 / z^2) atTop (𝓝 0):=by simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using hv.const_mul A0
 exact hX.eventually (ge_mem_nhds v)
abbrev waveG (x Q V s A ρ a ε:ℝ)(p n l:ℕ)(L:Side):ℝ:=(Real.exp (s*Yaw.χ (l+90))*(lip (p+2)*(population*a)) + Real.exp (-(ρ/2)*(radiusB x:ℝ))* lorp s (l+90) n (population*(A*followV [] L))*(V^2*lip (p+2)^2) + lorp s (l+90) n (population*(A*followV [] L))*(V^2*levyC p 1 ε))/Q^2
lemma tariffS (s A D e a r:ℝ)(k n l:ℕ)(L:Side)(p:0 < r): ∀ᶠ Q in atTop,∀ᶠ x:ℝ in atTop, waveG x Q (D*Q) s A r a (e*(L.val:ℝ)⁻¹^2) k n l L ≤ keyS s A D e l n k*gritY L.val:=by -- keyS args t D yes tune
 let Hp:= lorp s (l+90) n (population*(A*followV [] L)); let B0:=Real.exp (s*Yaw.χ (l+90))*(lip (k+2)*(population*a)); let I:ℝ:= L.val; let J:= D^2*pitchP s A l n * levyC k 1 e; have h:0< I:=by unfold I; positivity
 have hV:0<gritY I:=by unfold gritY; positivity
 filter_upwards [rate_v B0 (gritY I) 0 hV,eventually_gt_atTop (0:ℝ)] with Q kW hq
 let f(x:ℝ):= (radiusB x:ℝ); let Y(x):=Real.exp (-(r/2)*f x); let A':= D^2*lip (k+2)^2; have hz:Tendsto Y atTop (𝓝 0):= Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto).const_mul_atTop_of_neg (neg_neg_of_pos (half_pos p)))
 have he:Tendsto (fun x=>Y x*Hp*A') atTop (𝓝 0):=by simpa using ((hz.mul_const Hp).mul_const A');
 filter_upwards [he.eventually (ge_mem_nhds hV)] with x t
 have heL: Hp*((D*Q)^2*levyC k 1 (e*I⁻¹^2))/Q^2= J*gritY I:=by
    unfold Hp J gritY; rw [lorp_v,levy_m]; field_simp; unfold I; ring -- tune denominators
 calc
    _ = B0/Q^2+Y x*Hp*A'+ J*gritY I:=by unfold waveG; rw [← heL]; simp only [add_div]; unfold Y Hp f I B0 A'; field_simp <;> ring
    _ ≤ (gritY I)+gritY I+J*gritY I:=add_le_add (add_le_add kW t) le_rfl
    _ = _:=by unfold keyS J I; ring
end YM.CF.Oath
