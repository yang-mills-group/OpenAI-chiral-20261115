import YM.SU5.LitCurrent.Spun
import YM.SU5.SatinWard.Resolution.Jungfrau
import Anomaly.Separate.Pumps
import YM.SU5.SatinWard.Resolution.Cameo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
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
open YM.CF.BPress (PL NPL)
variable {F G:ℝ→ℝ}
open Vow Sour Swell Ione
namespace Rate
namespace LocalLimit
open Jet
namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
local notation "xt" => hat P.R.L P.x
local notation "Aκ" v:max=> Y.meter.a v
local notation "Rt" i:max k:max s:max => (RootBook Y i k s)
local notation "Ω" i:max k:max=> cell (Y.ir i) P.block P.R.L k
open LitCurrent
local notation "gr" i:max k:max s:max=> (Rt i k s)
local notation "loom" i:max s:max=> (tape i).CapeT s
local notation "ΩB" i:max k:max s:max=> (Rt i k s).p
local notation "pro" i:max k:max s:max=> funde P.K.j (Rt i k s).J.M (Ω i s)
local notation "link" i:max k:max s:max=> Moire.bloom (Rt i k s).J.P
variable {r i k s:ℕ}{a b c v w:ℝ}
lemma requestJ (bI:Chamber.Division) (E: MaskPoint Y r s i k a b)(x:Site (Ω i s))(F:Pattern (pro i k s) (link i k s) r P.d a v)(w:ℝ)(e:FaceDir) : let Q:= (ΩB i k s); let g:= E.C; let d:=Q.B/10
 let Z:=legOut 24 Q 32 P.h w a b r * LitCurrent.expiry (4*a) v; let A:=fun v:Orbit (Ω i s)=> Chamber.jewelCostLeg bI (loom i s) Q d w x F e (v.1,(loom i s) v); ∃ M:Sour.Bag (Ω i s), Hold P.U (Rt i k s) (loom i s) P.J.n 24 (node x) P.h (rScale Q) A M (Z+τΓK Q P.R.L (xt s) Z) (Z+τΓK Q P.R.L (xt s) Z):=by
 intro p g d Z A'; have hB:0 ≤ rScale p:=by unfold rScale; positivity
 let D:= (p.B:ℝ)⁻¹; have h':0<D:=by unfold D; have hp:=p.B_pos; positivity
 have hp:a≤100*(4*a):=by have hv:=g.hint; linarith
 have ht:=Chamber.pilot_cost bI _ _ _ w x F E.C e E.pulse (E.ppm.drop hp) (E.term.drop hp) (by norm_num)
 obtain ⟨W,X⟩:= grab_hold P.U _ _ E.pulse.roof E.hK E.slip hB h' (downFence (m:=0) ht (rateEx p)) E.spend -- tune
 refine ⟨W,?_⟩; unfold D at X; simp only [inv_inv] at X; exact X
local notation "Q"=> (RootBook Y i k s)
local notation "P1"=> funde P.K.j (Q).J.M (Ω i s)
local notation "T1"=> Moire.bloom (Q).J.P
local notation "y"=> (xt s)
local notation "Yh"=> (Y.voyage i).CapeT s
local notation "Yp"=> (Y.meter.a 0)
-- `hueW` already includes the production factor (129)
local notation "ρ0" => hueW P.R.L (xt s)
abbrev chillInt (x:ℝ):ℝ:= (BPress.drift x^4 :ℝ)⁻¹
lemma intLive (x:ℝ): 0< chillInt x:=inv_pos.mpr (pow_pos (BPress.drift_pos _) _)
lemma intPrice: NPL chillInt:= by apply (BPress.npl_drift 4 (by norm_num)).mono; filter_upwards with x; unfold chillInt; norm_num
abbrev jHull (L:Side)(x:ℝ):ℝ:= pinpr L x *chillInt x
abbrev bold_C (P:BudgetPoint)(r:ℕ)(x a b v w:ℝ):ℝ:= legOut 24 P 32 x w a b r * LitCurrent.expiry (4*a) v
abbrev trail_S (P:BudgetPoint)(r:ℕ)(L:Side)(x a b v w:ℝ)(i:ℝ):ℝ:= chillInt i* (bold_C P r x a b v w+ ZxT L P i (bold_C P r x a b v w))
lemma trail_lawn (P:BudgetPoint)(r:ℕ)(L:Side)(x a b v w:ℝ): NPL (trail_S P r L x a b v w):=by
 let W:= bold_C P r x a b v w; exact intPrice.mul ((PL.const W).add ((tallCostP _ _ _ (PL.const W)).pl)) -- check tall arguments
lemma jHull_star (bI:Chamber.Division) (w:ℝ)(h:MaskPoint Y r s i k a b)(x:Site (Ω i s))(E:Pattern P1 T1 r P.d a v)(g:0< pinpr P.R.L (xt s))(e:FaceDir) : let C:= (↑(jHull P.R.L (xt s)):ℂ) • Chamber.jewelCostLeg bI Yh (Q).p ((Q).p.B/10) w x E e
 let f:= trail_S (Y.meter.a 0) r P.R.L P.h a b v w (xt s); let d:=f*pinpr P.R.L (xt s); ∃ M:Sour.Bag (Ω i s), Hold P.U Q Yh P.J.n 24 (node x) P.h (rScale (Q).p) (fun v=> C (v.1,Yh v)) M d d:=by
 intro C f d; obtain ⟨M,M'⟩:= requestJ Y bI h x E w e
 let L:=P.R.L; let u:= bold_C (Yp) r P.h a b v w; let z:= bold_C (Q).p r P.h a b v w
 have hx:(Yp).order=(Q).p.order:=(Y.meter.boot 0).2.2.2.2.trans h.V0.symm; have hb: u=z:=by unfold u z bold_C legOut treeEarnings reefCost; rw [hx]
 have ht: jHull L y>0 := mul_pos g (intLive _); let aS:=jHull L y
 let hM:= scale_hold P.U Q Yh M' (↑aS:ℂ);
 have hh: ‖(↑aS:ℂ)‖ * (z + τΓK (Q).p L y z)=d:=by
    unfold d f trail_S; rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht)]; rw [← hb, (lifeS P.R.L P.h a b r (Q).p (Y.meter.a 0) hx.symm (xt s) h.B0 u v).1]; unfold L u jHull; ring
 refine ⟨_, rise_hold P.U Q Yh hM hh.le hh.le⟩
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
