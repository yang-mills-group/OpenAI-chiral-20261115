import YM.SU5.Interaction.Reg.Glyph

/-! Strong payment at exponent+1 for the later rollT expenses. -/
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
include Ω Th

def differentialCost (p:BudgetPoint) (a b c W r s:ℝ):ℝ := φcape (ups p) a (Qu*b*r) (Qu*c*r) W + s^2 + cap1 (ups p) (BondL.øK r) W

-- literally rollT with the new U.
lemma rollPay (i:πχ)(F:Pair VK)(pA:Coverable p W B F m₁ m₂)(hZ:Both Cash.poise (Ω.νpoint i F))(τ:Ids n)(U0:Pair (RegBudget n))(p':IncX (fun _=>False) U0.1 (ups p) W x): IncX (fun _=>False) (Ω.rollT i F U0 τ).1 (ups p) W (x+differentialCost p a b c W r s) := by
 obtain ⟨A,T⟩:=rollHigh Ω Th i.1
 obtain ⟨v,m,f⟩:=(Ω.project_K Th i F pA).1.1
 have hx:IncX Utrue (cast_E (Ω.νpoint i F).1 τ) (ups p) W (tintK p (rentΦ p γΓ dΓ) θΓ vδ):=worthHigh p _ τ hZ.1.2 hZ.1.1 (zero_le_one.trans Ω.floor) m f
 let U:= Fixed.Voltage.upgradeI _ _ hx (show _ ≤ s^2 from by linarith only [Th.lens,sq_nonneg s]);
 unfold differentialCost; rw [←add_assoc,←add_assoc]
 exact Larch.add_v _ _ _ (Larch.add_v _ _ _ (Larch.add_v _ _ _ p' A) (show IncX (fun _ => False) (cast_E _ τ) (ups p) W (s^2) from ⟨U.weight,fun _ u=>u.elim⟩)) T

lemma rolledCost (hu:0 ≤ u0) : differentialCost p a b c W r s ≤ Real.exp (Fief.tileN 1:ℝ) * Λ := by
 have h : (Sour.κY (ups p)) = Real.exp (Fief.tileN 1:ℝ) * Sour.κY p := by
   unfold Sour.κY tollL0; simp only [ups, editRate]; rw [add_mul,one_mul,Real.exp_add]; ring
 unfold differentialCost φcape cap1 cap2; rw [h]
 have k:=Th.cap; unfold φcape cap1 cap2 at k -- check parse Qu: nat???
 let ℓ:= Real.exp (Fief.tileN 1:ℝ)
 have b0:1 ≤ ℓ:= Real.one_le_exp (by positivity)
 have u:=mul_le_mul_of_nonneg_left k (Real.exp_pos (Fief.tileN 1:ℝ)).le
 simp only [ups, editRate, numV] at * -- maybe coinK not in scope
 nlinarith only [u, mul_nonneg (Real.exp_pos (Fief.tileN 1:ℝ)).le hu, mul_le_mul_of_nonneg_right (show 1 ≤ Real.exp (Fief.tileN 1:ℝ) from b0) (sq_nonneg s)]
end Technique
end MatchW
end YM.CF.Sour
