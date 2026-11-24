import YM.CF.BProof.Digit.Sticks
import YM.CF.BProof.Axial.Kernel
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Digit
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
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral Axial
open scoped YM.CF.Mew YM.CF.Sour.Axial
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁:ℝ}{q:ℕ}
local notation "δ"=> cipherK q
variable (k:Arbor P U q t d W z₀ z₁) (F:BondL T S (body_Q (N:=n) 1) b c a d)
variable (s:0≤R)[Nonempty (ΘS R)](x: ΘS R)
local notation "A₀"=> (orchard F R s)
local notation "μ"=> (bead (A₀) W P) -- scoped open
open BondL
lemma kernel_p : wire P W (cipherK q) (Axial.stack k F x.val) ((A₀).bead W P) (tuneB k F x.val):=by
 rw [←goalB k F s x,←goalJ k F s x]; exact ((A₀).litB k.tile k.pos W k.hw k.paid k.hv k.y k.hx k.v k.w x).buys k.w (zero_le_one.trans k.hw)
-- burst all real guesses; x∈ball for proof below
include s
lemma kernel_v : Burst P (Axial.stack k F x.val) (tuneZ k F x.val):=by
 rw [←goalZ k F s x,←goalJ k F s x]; exact fun Y=> funext fun i=> ((A₀).city k.tile k.pos W k.hw i x Y k.paid k.hv k.y k.hx k.v k.w).symm
omit s
lemma hot_w (y:SpaceM){A:Set ℂ}: PlayC A (fun _=>Axial.stack k F y):=by
 let κ:=Axial.stack k F y; intro X D Y i H p; let g(z:ℂ):= κ X D Y (H z) i
 have ht: Hol A fun z=>(g z).val:=by
    simp_rw [g, κ,orbit_price]; unfold hotP; split; swap; exact differentiableOn_const _
    next p'=> exact (LinearMap.toContinuousLinearMap (Pastry.cane (Dwell n)).eval).differentiable.comp_differentiableOn ((differentiableOn_const _).mul ((LinearMap.toContinuousLinearMap (eat_c (n:=Dwell n))).differentiable.comp_differentiableOn p))
 exact SubHol.font (subhol_dough (f:=fun z=> g z.val) ⟨_,ht,fun _=>rfl⟩) _ (fun _=>rfl)
-- homogeneity.
theorem tone (u:ℝ)(p:0≤u)(y:SpaceM)(h:‖y‖≤ u*R)(R':ΘS R) : ∃ x:ΘS R,y=u • x.val:=by
 by_cases q:u=0; · subst u; rw [zero_mul] at h; exact ⟨R',by rw [zero_smul,norm_le_zero_iff.mp h]⟩
 let Y:=u⁻¹ • y; have he:u>0:= lt_of_le_of_ne p (Ne.symm q); refine ⟨⟨Y,?_⟩, (smul_inv_smul₀ q y).symm⟩; unfold Y; rw [norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ he]; exact h
include s
lemma sounds (u:ℝ)(v:0≤u)(y:SpaceM)(h:‖y‖≤ u*R) : wire P W δ (Axial.stack k F y) (u • (A₀).bead W P) (tuneB k F y) ∧ Burst P (Axial.stack k F y) (tuneZ k F y):=by
 obtain ⟨x,rfl⟩:= tone u v y h (Classical.arbitrary _); rw [map_smul,map_smul,map_smul,←Complex.coe_smul u (Axial.stack k F x.val),←Complex.coe_smul u (tuneB k F x.val),←Complex.coe_smul u (tuneZ k F x.val)]; constructor
 · have he:= wire.lamp_c (kernel_p k F s x) (u:ℂ); rw [Complex.norm_real,Real.norm_of_nonneg v] at he; exact he
 exact (kernel_v k F s x).sail _
theorem fee_bead (ht:0<a)(u: 2*(wu P+2)*Fief.tileN 1 ≤ a/2/2*P.B) : HiveQ ((A₀).bead W P) P (wu P+2) (feeΨ P a (knot R b) (knot R c) W):=by
 intro i; have he:= (A₀).duty W P (wu P+2) ht (by unfold wu; linarith [P.exponent_pos]) u i; rw [←parse,mul_zero,sub_zero] at he; exact he
end YM.CF.Sour.Digit
