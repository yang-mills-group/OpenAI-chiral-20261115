import YM.SU5.WakeFields.TimeAward
import YM.SU5.LitCurrent.History
import YM.SU5.Exchange.Force.Band
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
open LitCurrent Buffered Sault Vow.TreasuryFog
variable {i k s r:ℕ}{a b c v w:ℝ}
open Furrow Roots Sour.Ledger Mew Rive Wray Larch
open scoped YM.CF.Mew
local notation "pin" => pinpr P.R.L
local notation "m0"=>cell (Y.ir i) P.block P.R.L s
local notation "Λ"=> P.R.L
local notation "Q"=>RootBook Y i k s
local notation "Qp"=>(Q).p
local notation "ℒ"=> (Y.voyage i).CapeT s
-- availability on every appointed step (nonterminal) of this run. ℒ not promoted hops.
-- 'Z' looks for exactly these costs. epoch-majorizer separate.
structure BirthWorld (s i k t :ℕ)(a b X : ℝ) : Prop where
    stage : let QT:=RootBook Y i k s; let p:= QT.p; let L:=P.R.L; let N:=cell (Y.ir i) P.block L s; ∃ v : ℝ,FlagWidth p QT.K (cipherK P.J.n) ∧ SanB QT.K (giftK p (p.supportExponent+(1:ℝ)/2)) p P.h (fun _=>v) ∧
        2*Crawl.till p L.val≤ (More N).val ∧ ∃ C,generation p t L.val |a| (|b| *pinpr P.R.L (hat P.R.L P.x s)) v X 2 C
    «pin» : 0 < pinpr P.R.L (hat P.R.L P.x s)
variable (U:Sweepcraft Y Tξ Pay ξC Γϕ n u)
include U
lemma pillarStage (t:ℕ)(a b:ℝ→ℝ)(ha:NPL a)(hb:NPL b) : ∃ X:ℝ→ℝ,NPL X∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<Y.uv k→ BirthWorld Y s i k t (a (xt s)) (b (xt s)) (X (xt s)*pin (xt s)):=by
 obtain ⟨Z,W,V1,Kf,QT,h⟩:=U.scene; let X:= Sour.Ledger.wageBorn Λ 6 2 t (Λ).val b Kf
 have v:NPL fun x=> Kf x /pin x := Sour.Ledger.plume _ QT.mint
 refine ⟨X,Sour.Ledger.brightW _ _ _ _ _ _ _ hb v,?_⟩
 filter_upwards [h,(turnover P).eventually (Sour.Ledger.april Λ 6 2 t (Λ).val a b Kf ha hb.pl v.pl)] with s h g
 let p:=Y.meter.a s; let β:=xt s; let N:=2*Crawl.till p (Λ).val
 filter_upwards [h, Y.ir_grows.tendsto_atTop.eventually_ge_atTop N] with i h ρN k q
 let Q0:= RootBook Y i k s; have ht: Q0.p= p:= (((Y.voyage i).X (Y.uv k)).pull.owns s q.le).width.symm
 let V:=h k q
 have hB:p.B=radiusB β:= (Y.meter.boot s).2.1; have hO:p.order=6:= (Y.meter.boot s).2.2.2.2; have he:p.supportExponent=1:=(Y.meter.boot s).2.2.1; have hu : p.power=2:=(Y.meter.boot s).2.2.2.1
 have hh: Crawl.till Q0.p (Λ).val=Crawl.till p (Λ).val:=by rw [ht]
 -- use radius already paid of THIS call
 obtain ⟨aw,ab⟩:= AstroFunding.radius P.V P.U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V
 -- conn estimate period.State only
 refine ⟨?_,g.1⟩; refine ⟨Kf (xt s),aw,ab,?_,g.2 Q0.p (ht.symm ▸ hB) (ht.symm ▸ hu) (ht.symm ▸ hO) (ht.symm ▸ he)⟩
 change 2*Crawl.till Q0.p (Λ).val ≤ _; rw [hh]; apply le_trans ρN _ -- tune `N` abbreviated local X replacing
 apply le_trans (amplit (Y.ir i) P.block Λ s); change _ ≤ (cell (Y.ir i) P.block (Λ) s).val*2
 omega
omit U

variable {I:Type} [LinearOrder I] [Fintype I]
variable (o:I→Site (cell (Y.ir i) P.block P.R.L s))(τ:Ids (cell (Y.ir i) P.block P.R.L s))
local notation "Z0"=>pin (xt s)
abbrev currentRoof (M : I→Bag m0) : Key I→ Bag m0:= lug (fun i _=>Crawl.aurora Qp (node (o i)) (Λ).val (M i))
structure Armed (M:I→Bag m0)(D:I→Orbit m0→FC (Single m0))(t u:ℕ)(W:ℝ)(K : Key I→ Cadre.Rinse (Seat m0) (Copy m0)) : Prop where
    bill : ∃ (C: Occlus Qp), BirthAward (h:=P.h) P.U ℒ o D P.J.n P.R.L t P.R.L.val C u (currentRoof Y (i:=i) (k:=k) (s:=s) o M) τ K 2 W
lemma ofWorldBorn {t:ℕ} (W:ℝ)(p:BirthWorld Y s i k t a b W) (G : Force_M (RootBook Y i k s).p.B (Cube.node ∘o) t) (u:ℕ)(hu:1≤u)(D:I→Orbit m0→ FC (Single m0))(M:I→ Bag m0) (q:∀ j,Nest P.U Q ℒ P.J.n r (node (o j)) P.h (rScale Qp) (D j) (M j) a (b*Z0)) :
    ∃ K, Armed (Y:=Y) (k:=k) (i:=i) (s:=s) o τ M D t u W K := by
 obtain ⟨v,Fq,Vq,θ,C,w⟩:=p.stage
 let D0(x:I):Nest P.U Q ℒ P.J.n r (node (o x)) P.h (rScale Qp) (D x) (M x) |a| (|b| *Z0):= nestUp _ _ _ (le_abs_self _) (mul_le_mul_of_nonneg_right (le_abs_self _) p.pin.le) (q _)
 obtain ⟨K,Z⟩:=birthRoot (R:=Q) P.U ℒ u o W 2 Λ t τ M D (Λ).val Fq Vq w G r D0 P.height (show (Λ).val ≤ (Λ).val^3 from le_self_pow₀ (by have h:=P.R.coarse; omega) (by norm_num)) θ hu
 exact ⟨K,⟨C,Z⟩⟩
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.pillarStage
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.ofWorldBorn

