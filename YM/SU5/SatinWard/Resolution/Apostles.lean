import YM.SU5.LitCurrent.Spun
import YM.SU5.SatinWard.Resolution.Jungfrau
import Anomaly.Separate.Pumps
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
lemma requestS (bI:Chamber.Division) (E: MaskPoint Y r s i k a b)(x:Site (Ω i s))(F:Pattern (pro i k s) (link i k s) r P.d a v)(w:ℝ) : let Q:= (ΩB i k s); let g:= E.C; let d:=Q.B/10
 let t:= wholeTail 24 Q 32 P.h a b w r*(Real.exp (-a*(d:ℝ))*LitCurrent.expiry (4*a) v); let Z:=seaFront 24 Q 32 P.h a b r+t+dropout 24 Q 32 P.h a b w v r; let A:=fun v:Orbit (Ω i s)=> Chamber.jewelT bI x F (loom i s) Q d w (v.1,(loom i s) v); ∃ M:Sour.Bag (Ω i s), Hold P.U (Rt i k s) (loom i s) P.J.n 24 (node x) P.h (rScale Q) A M (Z+τΓK Q P.R.L (xt s) Z) (t+τΓK Q P.R.L (xt s) Z):=by
 intro p g d t Z A'; have hB:0 ≤ rScale p:=by unfold rScale; positivity
 let D:= (p.B:ℝ)⁻¹; have h':0<D:=by unfold D; have hp:=p.B_pos; positivity
 have hp:a≤100*(4*a):=by have hv:=g.hint; linarith
 have ht:=Chamber.local_fence bI w E.C x F E.pulse E.permit (E.ppm.drop hp) (E.term.drop hp) (le_trans (by omega) E.reach)
 obtain ⟨W,X⟩:= grab_hold P.U _ _ E.pulse.roof E.hK E.slip hB h' (downFence (m:=0) ht (rateEx p)) E.spend -- tune
 refine ⟨W,?_⟩; unfold D at X; simp only [inv_inv] at X; exact X
section
variable (L:Side)(p:BudgetPoint)(r:ℕ)(H w a b v:ℝ)
private abbrev slateJ (x:ℝ):=wholeTail 24 p 32 H a b w r*(exponentialR a x*LitCurrent.expiry (4*a) v)
private abbrev slateT (x:ℝ):=seaFront 24 p 32 H a b r+slateJ p r H w a b v x+dropout 24 p 32 H a b w v r
local notation "ΣT"=>slateT p r H w a b v
local notation "ΣJ"=>slateJ p r H w a b v
private lemma quantG_press (p':BudgetPoint)(he:p.order=p'.order)(x:ℝ): ΣT x=slateT p' r H w a b v x∧ ΣJ x=slateJ p' r H w a b v x:=by
 unfold slateT slateJ dropout seaFront wholeTail legOut treeEarnings cometPrice treeEarnings reefCost; rw [he]; exact ⟨rfl,rfl⟩
end

variable {r i k s:ℕ}{a b c v:ℝ}
local notation "Q"=> (RootBook Y i k s)
local notation "P1"=> funde P.K.j (Q).J.M (Ω i s)
local notation "T1"=> Moire.bloom (Q).J.P
local notation "y"=> (xt s)
local notation "Yh"=> (Y.voyage i).CapeT s
local notation "Yp"=> (Y.meter.a 0)
-- `hueW` already includes the production factor (129)
local notation "ρ0" => hueW P.R.L (xt s)
lemma commits_star (bI:Chamber.Division) (w:ℝ)(h:MaskPoint Y r s i k a b)(x:Site (Ω i s))(E:Pattern P1 T1 r P.d a v)(g:0< pinpr P.R.L (xt s)) : let C:= budded P.R.L (xt s) (Chamber.jewelT bI x E Yh (Q).p ((Q).p.B/10) w)
 ∃ M:Sour.Bag (cell (Y.ir i) P.block P.R.L s), Hold P.U Q Yh P.J.n 24 (node x) P.h (rScale (Q).p) (fun v=> C (v.1,Yh v)) M (mintedJ P.R.L (Y.meter.a 0) r P.h w a b v (xt s)) (mintedB P.R.L (Y.meter.a 0) r P.h w a b v (xt s)* pinpr P.R.L (xt s)):=by
 intro C0; obtain ⟨M,hM⟩:=requestS Y bI h x E w
 let T':= scale_hold P.U Q Yh hM (↑ρ0:ℂ)
 refine ⟨_, rise_hold P.U Q Yh T' ?_ ?_⟩
 all_goals
   have hx:(Yp).order=(Q).p.order:=(Y.meter.boot 0).2.2.2.2.trans h.V0.symm
   have hz:((Q).p).order=6:= h.V0
   have hg:‖(↑ρ0:ℂ)‖=ρ0:=by
      have hv:0 < temp (hat P.R.L P.x s):= h.V1 ▸ (Q).p.threshold_pos
      unfold hueW; rw [Complex.norm_real,Real.norm_of_nonneg]; exact mul_nonneg (div_nonneg g.le (by positivity)) (Real.rpow_nonneg (BPress.drift_pos ..|>.le) _)
   obtain ⟨hc,hT⟩:= quantG_press Yp r P.h w a b v (Q).p hx (xt s)
   have hw:∀ J:ℝ,τΓK (Q).p P.R.L (xt s) J= ZxT P.R.L Yp (xt s) J :=fun J=> (lifeS P.R.L P.h a b r (Q).p (Y.meter.a 0) hx.symm (xt s) h.B0 J v).1
   first | unfold mintedJ|unfold mintedB; rw [div_mul_cancel₀ _ g.ne']
   rw [hg,hw]
   first | change _ ≤ ρ0*(slateT Yp r P.h w a b v y + ZxT P.R.L (Yp) y (slateT Yp r P.h w a b v y)) | change _ ≤ ρ0*(slateJ Yp r P.h w a b v y + ZxT P.R.L Yp y (slateT Yp r P.h w a b v y))
   rw [hc]; try rw [hT]
   unfold slateT slateJ exponentialR
   rw [← h.B0]
-- section h.positive before filters.
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
