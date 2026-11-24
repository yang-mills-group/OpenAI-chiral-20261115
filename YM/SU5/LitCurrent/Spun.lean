import YM.SU5.LitCurrent.Patrol
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
section
variable (L:Side)(p:BudgetPoint)(r:ℕ)(H w a b v:ℝ)
private abbrev slateJ (x:ℝ):=wholeTail 24 p 32 H a b w r*(exponentialR a x*LitCurrent.expiry (4*a) v)
private abbrev slateT (x:ℝ):=seaFront 24 p 32 H a b r+slateJ p r H w a b v x+dropout 24 p 32 H a b w v r
abbrev mintedJ (x:ℝ):=hueW L x*(slateT p r H w a b v x+ZxT L p x (slateT p r H w a b v x))
abbrev mintedB (x:ℝ):=hueW L x*(slateJ p r H w a b v x+ZxT L p x (slateT p r H w a b v x))/pinpr L x
local notation "ΣT"=>slateT p r H w a b v
local notation "ΣJ"=>slateJ p r H w a b v
/-- No loss of Q (pinpr) even spending the bump `drift^(1/4)`. -/
lemma prices (ha:0<a): NPL (mintedJ L p r H w a b v)∧ NPL (mintedB L p r H w a b v):=by
-- adapted from Culture.coatMoney
 let γ:=pinpr L; let Z:=hueW L; let F(x):ℝ:=spanV (radiusB x)*(radiusB x:ℝ); have ht:PL F:=PL_spanV.mul PL_radiusX
 have hu:PL ΣJ:=(PL.const _).mul ((expConst a ha).mul (PL.const _)); have hv:PL ΣT:=((PL.const _).add hu).add (PL.const _)
 refine ⟨(coolQ L).mul (hv.add ((tallCostP _ _ _ hv).pl)),?_⟩
 have hx:NPL (fun x=>Z x*rNPLΓ L p x /γ x):=by
    apply ((((coolDivPiece L).mul (PL_radiusX.pow 10)).const_mul ((16*(16*Sour.fernL 4)*(Real.exp 1 * (Real.exp 20 + 1)) / 1000)* chi_f p.order))).mono ?_
    filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold Z rNPLΓ γ Ione.annual; unfold Ione.taxIns; ring
 let M(x):= 2*(F x* ΣT x*rNPLΓ L p x)
 have hp:NPL (fun x=> Z x*M x / γ x):=by
    refine (((ht.mul hv).times hx).const_mul 2).mono ?_; filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold M; ring
 have ht':NPL (fun x=> Z x * ΣJ x/γ x):=by
    apply ((tailω L a 10 ha (by omega)).const_mul (wholeTail 24 p 32 H a b w r*LitCurrent.expiry (4*a) v)).mono ?_; filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold Z slateJ γ exponentialR; ring
 apply (ht'.add (hp.add ((((ht.times hp|>.mul ((rentNPL L p).pl)).const_mul 2).const_mul (2:ℝ)⁻¹)))).mono ?_
 filter_upwards with i; apply le_of_eq; apply congrArg abs; unfold mintedB ZxT Z M γ F; ring
private lemma quantG (p':BudgetPoint)(he:p.order=p'.order)(x:ℝ): ΣT x=slateT p' r H w a b v x∧ ΣJ x=slateJ p' r H w a b v x:=by
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
def budded {w:Side}(L:Side)(x:ℝ)(V:CF.Buffered.Mark w):CF.Buffered.Mark w:= (↑(hueW L x):ℂ) • V
lemma commits (w:ℝ)(h:MaskPoint Y r s i k a b)(x:Site (Ω i s))(E:Pattern P1 T1 r P.d a v)(g:0< pinpr P.R.L (xt s)) : let C:= budded P.R.L (xt s) (surrogate Yh (Q).p ((Q).p.B/10) w x E)
 ∃ M:Sour.Bag (cell (Y.ir i) P.block P.R.L s), Nest P.U Q Yh P.J.n 24 (node x) P.h (rScale (Q).p) (fun v=> C (v.1,Yh v)) M (mintedJ P.R.L (Y.meter.a 0) r P.h w a b v (xt s)) (mintedB P.R.L (Y.meter.a 0) r P.h w a b v (xt s)* pinpr P.R.L (xt s)):=by
 intro C0; obtain ⟨M,hM⟩:=requestW Y h x E w
 let T':= nestScale P.U Q Yh (↑ρ0:ℂ) hM
 refine ⟨_, nestUp P.U Q Yh ?_ ?_ T'⟩
 all_goals
   have hx:(Yp).order=(Q).p.order:=(Y.meter.boot 0).2.2.2.2.trans h.V0.symm
   have hz:((Q).p).order=6:= h.V0
   have hg:‖(↑ρ0:ℂ)‖=ρ0:=by
      have hv:0 < temp (hat P.R.L P.x s):= h.V1 ▸ (Q).p.threshold_pos
      unfold hueW; rw [Complex.norm_real,Real.norm_of_nonneg]; exact mul_nonneg (div_nonneg g.le (by positivity)) (Real.rpow_nonneg (BPress.drift_pos ..|>.le) _)
   obtain ⟨hc,hT⟩:= quantG Yp r P.h w a b v (Q).p hx (xt s)
   have hw:∀ J:ℝ,τΓK (Q).p P.R.L (xt s) J= ZxT P.R.L Yp (xt s) J :=fun J=> (lifeS P.R.L P.h a b r (Q).p (Y.meter.a 0) hx.symm (xt s) h.B0 J v).1
   first | unfold mintedJ|unfold mintedB; rw [div_mul_cancel₀ _ g.ne']
   rw [hg,hw,hc]
   try rw [hT]
   unfold slateT slateJ exponentialR
   rw [← h.B0]
-- section h.positive before filters.
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
