import YM.CF.Sour.Star
import YM.CF.Milo.Spear
import YM.CF.Milo.Table
import YM.CF.Sour.Plate
import YM.CF.Ione.Tape
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
-- real quarry stitches, frame max constants preserve before.L. Only Real lemma Focus perf stencils, new Lawn.s sigma orientation.Open τ.
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {T' S':BeatL n}{Z':χL n κ}{d e v w a κ':ℝ}
local notation "B"=> Tenant.quota
lemma halo_keep(E:Elm n κ d e v)(H: Branch.Ledger e E.W κ') : Branch.Ledger e (loopF E true).W (B^2*κ'):=by
 let A(S:Sweep n):Elm n κ d e (B^2*κ'):= {F:=(E.Utar S true).F,W:= testV S true E.W, coat:=(E.Utar S true).coat, bank:= wardK S d E.W true E.coat H}; exact (chime A).bank
lemma halo_off(E:Elm n κ d e v)(H:∀ S:SO,S.card≠1→E.W S=0) :∀ S:SO,S.card≠1→ (loopF E true).W S=0:=by
 intro S t; have hp(s:Sweep n):testV s true E.W S=0:=by
    have u:=H (Salt.actY s S) (by simpa [actY] using t); funext i j; unfold testV; split <;> simp [tagR,u,Function.swap, noteU] -- tune
 funext i j; change ‖(Sour.avg n:ℂ)‖*((∑ s:Sweep n,testV s true E.W) S i j)=0
 simp only [Finset.sum_apply,hp,Pi.zero_apply,sum_const_zero,mul_zero]
local notation "C₀"=> wingRent (Fir.Aop-(1/2:ℂ) • 1) 1
abbrev pureB(A: BondL T' S' Z' v w e d)(k0:ℝ):Prop:= Ledger e A.ela.W (Tenant.quota^2*(wingRent (Fir.Aop-(1/2:ℂ) • 1) 1*k0))∧∀ S:Support (More n),S.card≠1→A.ela.W S=0
-- Mark pure with cost beacon.K beyond Lens alpha. Open body Θ.Bar Obs.Finite.Conv. Vol Theta. roots.
lemma ember(A: LedgerS T' S' Z' e v w d) (p: TagT T' S' Z' d)(x:Continuous Z')(q:∀ i,Mind (Z' i))(t:0 ≤ κ')(g:∀ i,‖Z' i‖ ≤ κ')(h:e≤1)(vV:C₀*κ' ≤ v):∃ B':BondL T' S' Z' (B^2*v) (B^2*w) e d,pureB B' κ':=by
 obtain ⟨F,W⟩:= (boldL (a:=e) d n Z' κ' t x g q h).has
 let Y:= {A with openX:= ⟨F.F,F.W,F.coat,F.store.book vV,F.shape⟩}
 exact ⟨compD Y p, halo_keep _ (show Ledger e (hull Y.openX).W _ from F.store), halo_off _ (show ∀ S:SO,S.card≠1→(hull Y.openX).W S=0 from W)⟩
end YM.CF.Sour
