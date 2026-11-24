import YM.SU5.Intrinsic.Rate.Bond
import YM.SU5.Intrinsic.Rate.Cast

/-!
# R124. `Match/Rays:incXG` companions. Separated core assembly bill.
Not changing the Operation, Mask/Profile or $T=Weather$ by an existence.
-/
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
local notation "opV" I:max k:max=> Timer (Cadre.chip (cribR (Ω.note+Ω.note)) I) (Ω.note+Ω.note) r₁ (wu p) wΨ (widthK n p.B) (spanV p.B) γΓ dΓ (spanV p.B*dΓ) dΓ k (Ω.note+Ω.note)
local notation "gΨ"=> degreePrice p.B θΓ wΨ
local notation "Upp"=> uk_b (rentΦ p γΓ dΓ) vδ θΓ gΨ
local notation "αΒ"=> p.supportExponent+1+1
include Ω
lemma rollHSurcharge (i:Er)(fα:2*(p.supportExponent+1)*Fief.tileN 1 ≤ a/2*p.B):IncX Utrue (Ω.lerW i) (plusOneRate p) W (φcape (plusOneRate p) a (Qu*b*r) (Qu*c*r) W)∧ IncX Utrue (Ω.ler i) (plusOneRate p) W (cap1 (plusOneRate p) (BondL.øK r) W):=by
 rw [mul_assoc Qu b _,mul_assoc Qu c _]; let A:= Ω.bond;  exact ⟨Ione.addT (plusOneRate p) (A.float_surcharge Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos fα Ω.raw) (A.scarf_surcharge Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos fα Ω.raw), A.star_surcharge Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.economic Ω.pos fα⟩

local notation "omC"=> tintK p (rentΦ p γΓ dΓ) θΓ vδ
local notation "κX"=> (u0+φcape (plusOneRate p) a (Qu*b*r) (Qu*c*r) W+s^2)

open Py
include Th
lemma nu_more (i:πχ)(F:Pair VK)(pA:Coverable p W B F m₁ m₂)(hZ:Both Cash.poise (Ω.νpoint i F))(τ:Ids n): IncX Utrue (cast_E (Ω.νpoint i F).1 τ) (plusOneRate p) W (s^2):=by
 obtain ⟨h,m,f⟩:= (Ω.project_K Th i F pA).1.1
 have p':=hZ.1
 let hx:IncX Utrue (cast_E (Ω.νpoint i F).1 τ) (plusOneRate p) W omC:= worth_surcharge p _ τ p'.2 p'.1 (zero_le_one.trans Ω.floor) m f
 apply Fixed.Voltage.upgradeI _ _ hx; linarith only [Th.lens,sq_nonneg s]
end Technique
end MatchW
end YM.CF.Sour
#print axioms YM.CF.Sour.MatchW.Technique.rollHSurcharge
#print axioms YM.CF.Sour.MatchW.Technique.nu_more
