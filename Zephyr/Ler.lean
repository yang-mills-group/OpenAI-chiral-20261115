import YM.CF.Vp929.Match.Rays
import Zephyr.Scarf
import Zephyr.Cast
import Zephyr.Dust
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
variable {Wk f m₁ m₂ u0 Λ ψ δ θ x g γΓ θΓ dΓ vδ r₁ s:ℝ}
local notation "Pk"=> cap1 p (BondL.øK r) W
local notation "VK"=> Vow.Cusp n
local notation "Θp"=> Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ
variable (Th: Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ)

include Ω Th
open Py Zephyr
local notation "omC"=> tintK p (rentΦ p γΓ dΓ) θΓ vδ
local notation "αΒ"=> p.supportExponent+1+1

lemma castCharge (i:πχ)(F:Pair VK)(pA:Coverable p W B F m₁ m₂)(hZ:Cash.poise (Ω.νpoint i F).1)(τ:Ids n):
    IncX Utrue (cast_E (Ω.νpoint i F).1 τ) (plusP p) W (s^2):=by
  obtain ⟨h,m,f⟩:=(Ω.project_K Th i F pA).1.1
  have hx: IncX Utrue (cast_E (Ω.νpoint i F).1 τ) (plusP p) W omC := worthRplus p _ τ hZ.2 hZ.1 (zero_le_one.trans Ω.floor) m f
  apply Fixed.Voltage.upgradeI _ _ hx
  linarith only [Th.lens,sq_nonneg s]

lemma lerCharge (i:Er)(h0:p.order=6)(h1:p.power=2)(h2:p.supportExponent=1):
 IncX Utrue (Ω.lerW i) (plusP p) W (iceRent p.B+iceRent p.B) ∧
 IncX Utrue (Ω.ler i) (plusP p) W (iceRent p.B):=by

 let D:= Th.speed
 have hc:0 ≤ βB c r := Ω.bond.elt.bank.posP
 have hb:0 ≤ βB b r := Ω.bond.ela.bank.posP
 have xc:=D.capPoint Ω.pos (βB c r) hc (by
   rw [mul_assoc Qu b _,mul_assoc Qu c _]
   change βB c r ≤ 5*βB b r + βB c r
   linarith only [hb]) h0 h1 h2
 have xb:=D.capPoint Ω.pos (βB b r) hb (by
   rw [mul_assoc Qu b _,mul_assoc Qu c _]
   change βB b r ≤ 5*βB b r + βB c r
   linarith only [hb,hc]) h0 h1 h2
 have scx:= Ω.bond.raiseScarf Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos D.addRate Ω.raw
 have fy:= Ω.bond.raiseFloat Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos D.addRate Ω.raw
 have l:= Ω.bond.raiseLine Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos D.addRate Ω.raw
 exact ⟨Ione.addT (plusP p) (Fixed.Voltage.upgradeI _ _ fy xc) (Fixed.Voltage.upgradeI _ _ scx xb), Fixed.Voltage.upgradeI _ _ l xb⟩
#print axioms castCharge
#print axioms lerCharge
end Technique
end MatchW
end YM.CF.Sour
