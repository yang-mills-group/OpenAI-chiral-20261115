import YM.CF.BProof.Temple.Route
import YM.CF.BProof.Mask.Burst
set_option autoImplicit false
set_option maxHeartbeats 290000
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
open Arbor
open Wager Frost Half Leg Rush Tulip Peaks TripD Scree Tap Haro ArborW RillW
namespace Gale
attribute [local instance] Wager.measureVal Wager.billVal
open Push.SectorMeasure Phase Brace Girt Vault Paige Drapes
variable {N P M C H L:Side}{R:Patch}{r l k j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e t:ℝ}
variable {U:Grasp Y H e}
local notation "Λ" => mid M H
local notation "Λ₁"=> mid C H
variable {F:Scree.Loom (mid M H)}{F₁:Scree.Loom (mid C H)}(i:Axis)(X:ClockD R r l k){α n:ℕ}{c z:ℝ}
variable {q:Chi}{G:Ratio (mid M H) (mid C H)} {T:StepData (Domain M H) (Domain C H)} {R':GramM (mid C H)}(E: Girt.BaseL U G R' F F₁ q z)
local notation "νβ"=> R'.beta
local notation "Pβ"=>R'.J.M
variable (L0:Roof (mid M H) c e l F) (Q:Vogue.Quartz (mid M H) α c l F) (p:T.patch.Branches T.kernel SU.group)(A: SpaceM) (h:T.ratio=ratio G) (hr:T.patch=R) (hu:G.count=R.L)
local notation "λS"=> integrated U F R' F₁ G T q z A.val
local notation "D_"=> stove U F R' F₁ G T q z A.val
variable {B:Body (mid M H)} (b:Soul i X B) (V:Rider (shade (mid M H) i true X.uF) (Leg.reach G (shade (mid M H) i true X.uF) k) i G j R'.J.M A)
namespace Soul
local notation "Λv"=>poleM i X G b V
local notation "Ωv"=> Travel i Λv * Λv
local notation "Ψ"=>wince G q z Ωv
local notation "ΛX"=>wince G q z Λv
local notation "βΓ"=> fuel T νβ F
local notation "κc"=> sqR i B
local notation "f_" x:max => (denZ R' U F₁ x)
-- wear in two parts. no assumption positivity.
variable (x:Orbit (mid M H))(y:Orbit (mid C H))
local notation "XT"=>poke F x
local notation "YT"=>F₁ y
-- change order of integration using Step budget, not bound on f(X). offset uniform cost not requested here. Spatial read fully Furn.
section
variable (χ:Pane N→ℝ)(W:Body N)
abbrev weighted(χ:Pane N→ℝ)(W:Body N):Body N:=fun x=>χ x.1 • W x
lemma weights (p:Mask.device i X χ)(t:Soul i X W) : ∃ P:Body N,Soul i X P∧ ∀ z:PairD N,sqR i P z=χ z.1 • sqR i W z:=by
 obtain ⟨F,h,v,g⟩:=p; refine ⟨weighted F W,t.hookup h v,fun z=>?_⟩; rw [g]; unfold sqR mant; simp only [Pi.mul_apply,weighted, Fock.theta_rsmul]; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul]; rfl
end
variable (qZ: Part Λ Λ₁) -- unused
local notation "ö"=> L
include L0 Q E T p h hr hu
-- combine matched mask device caveat: Lift with same q. k here EXACT Leg stencil units.
include b
lemma pact (nK:ℕ)(t:SetK j G.count nK)(w:k=units G.count nK)(χ:Pane (mid M H)→ℝ)(u:Mask.device i X χ)(ι:Orbit Λ→ Phys Λ)(t':∀ᵐ U∂city Λ,ι U=χ U.1 • (D_) U):∃ P:Body Λ₁,Soul i X P∧ cup ι F (sqR i B)=cup (denZ R' U F₁) F₁ (sqR i P) :=by
 obtain ⟨P,y,EP⟩:= weights i X χ B u b; have hG: Odd G.count.val:=E.power ▸ o; letI:Nonempty (Forest (ratio G)):=Tree.select _ hG
 have hv : cup ι F (sqR i B)=cup D_ F (sqR i P):=by
    apply integral_congr_ae; filter_upwards [t'] with x t; unfold pass; rw [t,EP]; let y:=D_ x
    have he(C:FC (Single Λ))(b:ℝ): acts (b • C) y = b • acts C y:= by simp_rw [←Complex.coe_smul]; exact act_smul .. -- tune simp direction
    change beamL _ (acts _ (χ x.1 • y))=beamL _ (acts (χ x.1 • _) y) -- typo tune
    rw [he]; exact congrArg (beamL Λ) (map_smul ((acts ((κc) (poke F x))).restrictScalars ℝ) _ _)
 subst k
 obtain ⟨V⟩:= Leg.train G j A Pβ i (shade Λ i true X.uF) hG t
 exact ⟨_,learnC i X G q z hr h hu E.legal.1 E.legal.2 L0 Q p νβ y V, hv.trans (together i X E L0 Q p A h hu (b:=y) V)⟩ -- argument test
end Soul
end Gale
end YM.CF.BProof.Bide
