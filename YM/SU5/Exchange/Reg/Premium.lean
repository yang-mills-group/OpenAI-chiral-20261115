import YM.SU5.Exchange.Reg.Roll
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
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
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
namespace MatchW
open Py.Rate Haro Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
open scoped Mew
local notation "Qu"=> Tenant.quota^2
variable (T S:BeatL n) {p:BudgetPoint}{v W e:ℝ}{B:ℕ}{L:Scree.Loom n}
open Technique
variable {T S} (Ω:Technique p W e d B L T S a b c r)
namespace Technique
local notation "Xp"=> Ω.note + Ω.note
local notation "Kr"=> Rinse (Seat n) (Copy n)
local notation "Er"=> ΘS r
local notation "λχ" i:max=> Ω.bond.litB Ω.H Ω.pay W Ω.floor Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize i
local notation "πχ"=> Pair (ΘS r)
local notation "I_"=> Complex.I
open Ione Glyph BondL Py
variable {M Z W0 ψ₁ θ₁ ξ₁ ψ₂ θ₂ ξ₂ g u0 vδ r' Λ m₁ m₂:ℝ}
variable (Th: Py.Mood p (512*M) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r g m₁ m₂ u0 vδ r' Λ ψ₁ θ₁ ξ₁ ψ₂ θ₂ ξ₂)

abbrev premiumRoll (R:BudgetPoint)(W a b c r g:ℝ):ℝ:=
 φcape R a (Tenant.quota^2*b*r) (Tenant.quota^2*c*r) W + g^2 + Glyph.cap1 R (BondL.øK r) W
/-- Roll of a pin, omitting the unrolled part. -/
def rollExtra (i:Pair Er)(F:Pair (Vow.Cusp n))(τ:Ids n): RegBudget n :=
 Ω.lerW i.1 + cast_E (Ω.νpoint i F).1 τ + Ω.ler i.1
include Ω Th
lemma issueRoll (i:Pair Er)(F:Pair (Vow.Cusp n))(pA:Coverable p W B F m₁ m₂)(hZ:Both Cash.poise (Ω.νpoint i F))(τ:Ids n)
 (s:2*(raiseRate p).supportExponent * Fief.tileN 1 ≤ a/2*p.B) :
 IncX Utrue (Ω.rollExtra i F τ) (raiseRate p) W
   (premiumRoll (raiseRate p) W a b c r g):=by
 obtain ⟨u,x,y⟩:= ((Ω.project_K Th i F pA).1.1)
 have hw:IncX Utrue (cast_E (Ω.νpoint i F).1 τ) (raiseRate p) W (tintK p (rentΦ p ψ₂ ξ₂) θ₂ vδ):=
    worthRaised p (Ω.νpoint i F).1 τ hZ.1.2 hZ.1.1 (zero_le_one.trans Ω.floor) x y
 let v:=Ω.bond; let K:= (raiseRate p)
 have H:= v.starInc Ω.H Ω.pay W Ω.floor i.1 Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.economic Ω.pos s
 have J:= v.payInc Ω.H Ω.pay W Ω.floor i.1 Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos s Ω.raw
 have T:= v.payZInc Ω.H Ω.pay W Ω.floor i.1 Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos s Ω.raw
 have C:IncX Utrue _ K W (g^2):=Fixed.Voltage.upgradeI _ _ hw (by linarith only [Th.lens,sq_nonneg g])
 unfold rollExtra premiumRoll
 rw [mul_assoc Qu b _,mul_assoc Qu c _]; exact Ione.addT K (Ione.addT K (Ione.addT K J T) C) H
end Technique
end MatchW
end YM.CF.Sour
