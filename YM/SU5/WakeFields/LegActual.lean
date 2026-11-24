import YM.SU5.WakeFields.Furrow
import YM.SU5.Exchange.Seed.Transit

/-! # Actual leg through both Forces. Converting the cassette identity to
an identity on the physical pilot. This one is pointwise (parameters and orbit). -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Rue
namespace TreasuryFog

open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open scoped YM.CF.Mew
open Jet Yaw Nor Prism Font Wray Roots Oise Dial
namespace Furrow
variable {N B : Side} {L₀ : Side}{j:ℕ}{ho:Odd L₀.val}{Y₁:Pricing j L₀ ho (Thread j)}{e u h:ℝ}
variable {I : Type} [LinearOrder I] [Fintype I]
local notation "m"=> mid N B
variable {R:GramM (mid N B)}
variable (U:Grasp Y₁ B e)(A:Scree.Loom (mid N B))(V:Orbit (mid N B))
variable {C:Occlus R.p} {σ : I → Seat (mid N B)} {q : ℕ}
variable {F : Key I→ ForceBudget (mid N B)} {K : Key I→ Rinse (Seat (mid N B)) (Copy (mid N B))}
variable {Y W : Key I → Aura (mid N B)→ ℝ}{J : Key I → Aura (mid N B)→ Support (More (mid N B))→ℝ} {M : Key I→ Bag (mid N B)}
variable (L : Furrow σ C q F h K Y W J M) (c : ℕ)(p : 1 ≤ h)(v : IsStarProjection (spar j R.J.M (A V)))
section
-- perturbed previous Gram.
variable (R F K) (P' : Key I→ RegBudget (mid N B)) (τ : Ids (mid N B))
def prevGram (z:Key I) : GramM (mid N B) := color_b R R.beta (R.F+P' z) R.slip (F z) R.v
def charged (z:Key I) : GramM (mid N B) := color_b R R.beta (R.F+(P' z+spaceD R.p F K c τ z)) R.slip (F z+placePort R.p F K c z) R.v
end
variable (P' : Key I→ RegBudget (mid N B))
-- beware binder order.
local notation "G"=> prevGram R F P'
local notation "HH"=> pilotH U R A V v
local notation "DZ"=> (flags R.p.threshold V.1)
local notation "Θ"=> spaceCells F K c
local notation "S'"=> Phys m
local notation "fL'"=> FleetS R.p.threshold V.1
variable (t : FleetS R.p.threshold V.1) (τ:Ids (mid N B))
open Bake
abbrev poseY (v : IsStarProjection (spar j R.J.M (A V))) : Cipher (mid N B) →L[ℂ] Phys (mid N B) :=
 (pilotH U R A V v).comp (LinearMap.toContinuousLinearMap {
    toFun := fun i=>Cadre.poseL _ i, map_add' := fun x y=> act_add .., map_smul' := fun x y=> act_smul ..})
-- actual covariance transfer of the cashflow on this grammar; pigment etc. no measure assumption.
lemma cling (z:Key I) (Y:Cipher m): pilotH U (G z) A V v (Cadre.poseL _ Y) = poseY U A V v (exp (exponentL R.p (P' z) V.1)*Y):=by
 let A₁ := exponentL R.p R.F V.1; let b := exponentL R.p R.slip V.1; let Y₀:=exponentL R.p (P' z) V.1; let L:=Sault.ballL (nursery _ v) (relV U R.J (A V)); let s:= Complex.exp (R.betaL A V)
 change s • L (acts (exp (exponentL R.p (R.F+P' z) V.1 + b)).val (Cadre.poseL _ Y))= s • L (acts (exp (A₁+b)).val (Cadre.poseL _ (exp Y₀*Y)))
 have h: exponentL R.p (R.F+P' z) V.1+b=(A₁+b)+Y₀:= by rw [(exp_gain (P:=R.p) (i:=V.1) R.F (P' z) 0).2,add_right_comm _ (exponentL _ _ _)]
 -- may need let NormedAlgebra
 letI :NormedAlgebra ℚ (Cipher m):= NormedAlgebra.restrictScalars ℚ ℂ _
 rw [h,exp_add]; unfold Cadre.poseL; rw [Subalgebra.coe_mul,Subalgebra.coe_mul,act_mul,act_mul _ Y.val] -- tune

include p t L
-- anchored at this V, k varies (width etc), no reuse of unperturbed
lemma chargeTape (z:Key I)(w:z∈hill I) : denZ (charged (N:=N) (B:=B) R F K c P' τ z) U A V=poseY U A V v (exp (exponentL R.p (P' z) V.1)*hGas (flags R.p.threshold V.1) (hailV (flags R.p.threshold V.1) (Θ z) V)) := by
 let E₀:= spaceD R.p F K c τ z; let W':= placePort R.p F K c z; let E':=P' z+E₀; let J':=F z+W'
 let zL:= exponentL R.p (P' z) V.1; let G':= hGas (flags R.p.threshold V.1) (hailV (flags R.p.threshold V.1) (Θ z) V)
 have he: exp (exponentL R.p E' V.1)*fueled R.p J' V=exp zL* G':=by
    let A0:= exponentL R.p E₀ V.1; have hr:G'=exp A0*fueled R.p J' V:= Furrow.spaceCash (n:=m) (P:=R.p) (F:=F) (K:=K) L c p τ z V t w
    letI :NormedAlgebra ℚ (Cipher m):= NormedAlgebra.restrictScalars ℚ ℂ _
    rw [hr,show exponentL R.p E' V.1=zL+A0 from (exp_gain (P:=R.p) (i:=V.1) (P' z) E₀ 0).2, exp_add, mul_assoc]
 calc _ = poseY U A V v (exp (exponentL R.p E' V.1) * fueled R.p J' V) := showUp (R:=R) U A V v E' J'
      _ = poseY U A V v (exp zL* G') := congrArg (poseY U A V v) he

open PowerSeries
local notation "Ψμ" z:max => cumQ (settleK (F z)) (K z) V R.p
variable (D : I→ FC (Single (mid N B)))
-- a pose.Open output on fleet pen; locality from the physical registrations below.
structure Costume (R:GramM (mid N B))(V:Orbit (mid N B))(A:Scree.Loom (mid N B))
    (v : IsStarProjection (spar j R.J.M (A V)))
    (U : Grasp Y₁ B e)(M : Key I→ Bag (mid N B))(D : I→ FC (Single (mid N B)))
    (F : Key I→ ForceBudget (mid N B))(P' : Key I→ RegBudget (mid N B)) : Prop where
 passage : ∀ z ∈ hill I,∀ X:Wave (Dwell (mid N B)),pilotH U (prevGram R F P' z) A V v (acts (∑ i:Aura m,M z i V) X)=acts (Liss.waveΦ D z) (pilotH U (prevGram R F P' z) A V v X)
variable (α : Costume R V A v U M D F P')

private lemma paint_v (z:Key I)(w:z∈hill I) : coeff 0 (hGas DZ (cumQ (settleK (F z)) (K z) V R.p)) = fueled R.p (F z) V:= by
 let X:Aura m→ PowerSeries (Cipher m):= Ψμ z; let H:= settleK (F z); let Y' := hailV DZ H V
 have heX:(coeff 0) ∘ X=Y':=Stax.star_L (P:=R.p) (n:=m) H (J z) (L.pigment z w) (K z) (Y z) (L.price z w) (zero_le_one.trans p) V t
 have hu:hGas DZ Y'= fueled R.p (F z) V:= (Furrow.totGas (P:=R.p) (n:=m) (F z) V).trans (settleSelf (P:=R.p) V t (F z))
 change coeff 0 (hGas DZ X)=_; rw [Cadre.car_v,heX,hu]
include α
lemma actTape (z:Key I)(w:z∈hill I) : let s:= hGas (flags R.p.threshold V.1) (cumQ (settleK (F z)) (K z) V R.p); poseY U A V v (exp (exponentL R.p (P' z) V.1)*(coeff c s))=acts (Liss.paper D c z) (denZ (G z) U A V):=by
 intro s; let B' := exp (exponentL R.p (P' z) V.1); let H:= pilotH U (G z) A V v
 have hp:H (Cadre.poseL _ (coeff c s))=acts (Liss.paper D c z) (H (Cadre.poseL _ (coeff 0 s))):= Stax.ledger_n (M:=(fun i Y'=>M z Y' i)) (P:=R.p) (n:=m) (settleK (F z)) (J z) (L.pigment z w) (K z) (Y z) (L.price z w) (zero_le_one.trans p) V t H (Liss.waveΦ D z) (α.passage z w) c
 let f:=fueled R.p (F z) V; have he:coeff 0 s=f:= paint_v V L p t z w
 rw [he] at hp
 calc _ = H (Cadre.poseL _ (coeff c s)) := (cling U A V v P' z _).symm
      _ = acts (Liss.paper D c z) (H (Cadre.poseL _ f)) := hp
      _ = acts (Liss.paper D c z) (denZ (G z) U A V) := congrArg (acts (Liss.paper D c z)) (show H (Cadre.poseL _ f) = denZ (G z) U A V from
        (show H (Cadre.poseL _ f)=poseY U A V v (B'*f) from cling U A V v P' z _).trans ((showUp (R:=R) U A V v (P' z) (F z)).symm))
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.actTape
