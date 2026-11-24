import YM.CF.BProof.Axial.Grace
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Axial
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
open Mew Floral BondL
open scoped YM.CF.Mew
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁:ℝ}{q:ℕ}
variable (k:Arbor P U q t d W z₀ z₁) (F:BondL T S (body_Q (N:=n) 1) b c a d)
local notation "u"=> k.tile
local notation "hD"=> k.pos
variable (s:0≤R)[Nonempty (ΘS R)](x: ΘS R)
local notation "Fq"=> (orchard F R s)
abbrev tuneL : SpaceM→ₗ[ℝ]RegBudget n:= stitch fun i=> lineH F (p:=P) u hD (pole i)
abbrev tuneW : SpaceM→ₗ[ℝ]RegBudget n:= leafR k F.elt (faceD true false) + leafR k F.coreS (fun A=> Matrix.trace A • 1)
abbrev tuneZ:= tuneL k F+tuneW k F
lemma goalL : lineH (Fq) (p:=P) u hD x= tuneL k F x.val := bill k F.ela (pal_v W k.hw) s x
lemma goalW : floatH (Fq) (p:=P) u hD x+scarf (Fq) (p:=P) u hD x= tuneW k F x.val:=congrArg₂ (·+·) (bill k F.elt (pal_v W k.hw) s x) (bill k F.coreS (oreV W k.hw _) s x)
lemma goalZ : seekB (Fq) (p:=P) u hD x=tuneZ k F x.val:=by rw [seekB,add_assoc,goalW k F s x,goalL k F s x]; rfl
def tuneB : SpaceM→ₗ[ℝ]Bag n:= vine k F.ela (faceD true false)+vine k F.elt (faceD true false)+vine k F.coreS (fun A=> Matrix.trace A • 1)+vine k (F.cosY false) (Sault.crib false)+vine k (F.cosY true) (Sault.crib true)+ vine k F.heel (Sault.urn (trailM false) (trailM true))
lemma goalB : choir (Fq) (p:=P) u hD x=tuneB k F x.val:=congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg₂ (·+·) (plant k F.ela (pal_v W k.hw) s x) (plant k F.elt (pal_v W k.hw) s x)) (plant k F.coreS (oreV W k.hw _) s x)) (plant k (F.cosY false) (tail_k W k.hw) s x)) (plant k (F.cosY true) (leg_k W k.hw) s x)) (plant k F.heel (less_k W k.hw) s x)
def hotP(X Y:Aura n)(D:Support (More n))(i:Orbit n)(b:Bag n)(v:Cipher n): FC (Dwell n):=if Bias.αt Y X D q then Sault.rind (coll_T P X D (b Y) i*v.val) else 0
theorem hot_sum (i:Orbit n)(b:Tiles→Bag n)(r:Tiles→ℝ)(v:Cipher n): hotP (q:=q) (P:=P) X Y D i (∑ j,r j • b j) v=∑ j,r j • hotP (q:=q) (P:=P) X Y D i (b j) v:=by
 unfold hotP; split; swap; simp; -- tune
 rw [Finset.sum_apply]; simp_rw [Pi.smul_apply]; rw [gloss_sum,sum_mul]; simp_rw [Matrix.smul_mul]; change (Pastry.cane (Dwell n)).eval.restrictScalars ℝ _= _; rw [map_sum]; exact sum_congr rfl fun j _=> map_smul ..
abbrev stack : SpaceM→ₗ[ℝ]Rinse (Seat n) (Copy n) := stitch fun i=>(F.litB k.tile k.pos W k.hw k.paid k.hv k.y k.hx k.v k.w (pole i)).payX
local notation "ξ" => hotP (P:=P) (q:=cipherK q)
lemma hot_r {Q:Bag n}{C:Aura n→ℝ}(p:Sour.Bias q Q P W C)(A:Copy n)(i:Orbit n): (p.payX X D Y A i).val= hotP (q:=q) (P:=P) X Y D i Q (A i):=by
 unfold hotP; split
 next e=> exact p.truth _ _ _ _ e _
 next e=> rw [Bias.payX,dif_neg e]; rfl
lemma vine_x (x: SpaceM): tuneB k F x= ∑ i:Tiles,cloth i x • F.choir (p:=P) k.tile k.pos (pole i):=by unfold tuneB vine; simp_rw [LinearMap.add_apply,sit,BondL.choir,smul_add,sum_add_distrib]
lemma orbit_price (p: SpaceM)(A:Copy n)(i:Orbit n): (stack k F p X D Y A i).val=ξ X Y D i (tuneB k F p) (A i):=by
 rw [vine_x,hot_sum,stack,sit]; simp_rw [Finset.sum_apply,Pi.smul_apply]; change eat_c.restrictScalars ℝ _= _; rw [map_sum]; exact sum_congr rfl fun j _=>by rw [map_smul]; exact congrArg (cloth j p • ·) (hot_r _ A i)
lemma goalJ : ((Fq).litB u hD W k.hw k.paid k.hv k.y k.hx k.v k.w x).payX= stack k F x.val:=by
 funext X D Y A i; apply Subtype.ext; rw [hot_r,goalB k F s x,orbit_price]
end YM.CF.Sour.Axial
