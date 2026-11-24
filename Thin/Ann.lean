import Thin.PaysSpan
import YM.CF.Fans.Fate
import YM.CF.Fans.Tela
import YM.CF.Roots.Cane
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
-- For fixed R. Smaller notation context
open Pitching Pitching.Focus
open Appel.Rate Stockpile

open Neon PhysicalNext.JointLoad
abbrev thinAllot (M:ℝ)(R:Patch)(x:ℝ):ℝ:= M*Scales.g SU.group R.L x ^ 2
-- version with constant allot multiple requested large enough in advance (no need φ/uμ -> ∞). All fixed before x.
abbrev tollR (R:Patch)(κr:ℝ→ℝ)(b x:ℝ):= Tenant.quota^2*(b*κr x)
abbrev hft (R:Patch)(P:ℝ):=P*gritY R.L.val
variable {R:Patch}{K:Teller SU.group}
open Nor Hove
lemma acquireAnn (J:Hove.Grant K.j 2)(P:BudgetPoint)(t nT κC κD a b c h:ℝ) -- t DayT, nT Pay
    (n:ℕ)(Ce:Estimate)(M X G σ M0 :ℝ→ℝ) -- M = φ here
    (uM:sizeK R.L 2 M)(he:Chill_v M0)(hc:sizeK R.L 1 X)(hj:Jade.warmK X)
    (hu:sizeK R.L 2 G)(hσ:sizeK R.L 3 σ)(hP:0<a)(hC:Ce.Economic R)(cJ:Jade.warmK Ce.F):
    ∃ Z Wξ V1 T:ℝ→ℝ,BladeQ R Z Wξ V1 T ∧∀ᶠ x in atTop, Ann_S (hall_P P x) P R n 2 6 5 x (M x) t (hft R nT) h (tintW P P 6 2 5 K.j J nT κC t) a (tollR R G b x) (tollR R G c x) (cappedBar Ce X x) (raisedB R Ce X σ x) (εLeaf R.L x) (T x) (V1 x) (M0 x) (Z x) (Wξ x) :=by
  obtain ⟨hB,hT,vB,vD⟩:= affordLend R Ce X σ hC cJ hj hc hσ
  have hk:sizeK R.L 1 (fun x=> hft R nT * (R.L.val:ℝ)^4*εLeaf R.L x+ raisedB R Ce X σ x):= (((Stockpile.low (R:=R)).scale _).accrue (vB.low (by omega))).low (by omega)
  let θ:= tintW P P 6 2 5 K.j J nT κC t
  obtain ⟨Z,Wξ,V1,T,hZ,hW,hV,hL,cp,an⟩:= acF P (cappedBar Ce X) G n 6 2 5 t θ a (Tenant.quota^2*b) (Tenant.quota^2*c) h (hft R nT) (εLeaf R.L) (raisedB R Ce X σ) M M0 hB vB hT hu he uM hP (Neon.Ψage _ _ _ _ _ _ _ hk hT hB) -- order #check
  refine ⟨Z,Wξ,V1,T,⟨hZ,hW,hV,hL,cp⟩,?_⟩
  unfold tollR; simp_rw [←mul_assoc (Tenant.quota^2) b, ←mul_assoc (Tenant.quota^2) c]; exact an

-- seeded capacities use below. Both inequalities allowing φ arbitrarily constant-multiple. g^2 is Litt 2.
lemma smallForM (R:Patch)(M D:ℝ):sizeK R.L 2 (thinAllot M R) ∧∀ᶠ x in atTop,3*dleaf R.L x+thinAllot M R x≤ εLeaf R.L x∧D*thinAllot M R x≤ εLeaf R.L x∧3*dleaf R.L x≤1:=by
  let f:=allotΨ R.L
  have hL:Litt R 2 f:=subsidy_K R
  let P:= max (max (D*M) M) 1
  have hv:0<P:= lt_of_lt_of_le zero_lt_one (le_max_right ..)
  have hx:= tenor_Q (1/P) f hL (one_div_pos.mpr hv)
  refine ⟨((sizeK.main R.L).square 2).scale M,?_⟩
  have hm:= (((Stockpile.low (R:=R)).scale 3).low (by norm_num : 1≤2)).spine
  filter_upwards [hx,stockpile_ν (R:=R),hm.eventually (ge_mem_nhds zero_lt_one)] with x y hy E
  have N:0≤f x:=sq_nonneg _
  have he:P*f x ≤ dleaf R.L x:=by
     apply (mul_le_mul_of_nonneg_left y hv.le).trans_eq
     field_simp
  have hQ:= (mul_le_mul_of_nonneg_right ((le_max_right (D*M) M).trans (le_max_left _ 1)) N).trans he
  have hR:= (mul_le_mul_of_nonneg_right ((le_max_left (D*M) M).trans (le_max_left _ 1)) N).trans he
  have hl:0≤εLeaf R.L x:=hy.2.2.1.le
  change 3*εLeaf R.L x ≤ 1 at E
  change 3*dleaf R.L x + M*f x≤ εLeaf R.L x ∧ D*(M*f x) ≤ εLeaf R.L x ∧ 3*dleaf R.L x ≤1
  rw [←mul_assoc D]; unfold εLeaf at *
  exact ⟨by linarith only [hQ,hl],by linarith only [hR,hl],by linarith only [E,hl]⟩
#check acF
#check Neon.Ψage
end YM.CF.Py.Rate
