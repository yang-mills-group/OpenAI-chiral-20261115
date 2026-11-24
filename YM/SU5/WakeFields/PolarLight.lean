import YM.SU5.WakeFields.Costumes
import YM.SU5.WakeFields.Tallies
import YM.SU5.Exchange.Seed.Pension

/-!
# More On Key: diagram through the actual re-polarized program
-/
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
variable (P' : Key I→ RegBudget (mid N B))
local notation "G"=> prevGram R F P'
local notation "HH"=> pilotH U R A V v
local notation "DZ"=> (flags R.p.threshold V.1)
local notation "Θ"=> spaceCells F K c
variable (t : FleetS R.p.threshold V.1) (τ:Ids (mid N B))
open Bake

variable (D : I→ FC (Single (mid N B)))
variable (α : Costume R V A v U M D F P')
variable (l : List I)(tl : l.length ≤ c)
variable (u' : ∀ i:Scree.Hub (mid N B),River (fun z=> P' z i V.1))
include p t L α u'
omit t α
variable (E : I→ RegBudget (mid N B))
open Py Neon
variable (e₀ : ∀ i U, exponentL R.p (E i) U = exponentL R.p (νΦX (spaceD R.p F K c τ) {i}) U)
variable (ρ : ψS σ l)
include ρ e₀
local notation "ΔE"=> awake σ (spaceD R.p F K c τ) E
local notation "ΔF"=> bustle σ (placePort R.p F K c)
section
variable (R σ F K)
def polarized (z:Key I) : GramM (mid N B) := color_b R R.beta (R.F+(P' z+ΔE z)) R.slip (F z+ΔF z) R.v
-- Keep R explicit in cash.T.Color.β tangent accounted separately.
end
lemma former : Soft l
    (fun z=>fueled R.p (F z+placePort R.p F K c z) V) (fun z=> fueled R.p (F z+bustle σ (placePort R.p F K c) z) V) := by
 let T:= placePort R.p F K c
 have hv : T 0=0:= (L.setup c τ).2
 refine softFuel R.p V l (uS_b σ ρ) (F:=fun z=>F z+T z) (F':=fun z=>F z+ΔF z) (fun i=>?_)
 have p':=Soft.idem l ((L.settleQ i).2 V)
 change Soft l (fun z=> F z i V+T z i V) (fun z=>F z i V+bustle σ T z i V)
 have be:= softMolten (n:=m) σ (fun z=>T z i V) ((L.deltaPort c p i).2 V) l ρ
 simp only [hv,Pi.zero_apply,zero_add] at be; simp_rw [costF σ T]; exact p'.plus be
include v
lemma softPose : Soft l (fun z=>denZ (polarized (N:=N) R σ F K c P' τ E z) U A V) (fun z=>denZ (charged R F K c P' τ z) U A V) := by
 let g:= poseY U A V v
 let P:= R.p; let B':= fun z:Key I=>F z+ΔF z
 have h0(x: Key I)(X:RegBudget m)(Y:ForceBudget m):denZ (color_b R R.beta (R.F+(P' x+X)) R.slip Y R.v) U A V=
    g (exp (exponentL R.p (P' x) V.1+exponentL R.p X V.1)*fueled R.p Y V) := by
      rw [←(exp_gain (P:=R.p) (i:=V.1) (P' x) X 0).2]; exact showUp U A V v _ _
 unfold charged polarized; simp_rw [h0]; have hx:= castEra (P:=R.p) σ (spaceD R.p F K c τ) E (L.setup c τ).1 (fun i V=> (L.regPort c p τ i).2 V) e₀ l ρ V.1
 let C:=(((Soft.idem l (readingSum P P' V.1 u')).plus hx).expΩ (uS_b σ ρ)).mul (former V L c p P' τ l u' E e₀ ρ) (uS_b σ ρ)
 exact (C.graph g).back
omit ρ e₀ p
lemma formerR : River (fun z=>denZ (prevGram R F P' z) U A V) := by
 let V':=poseY U A V v; apply (sc_V ((readingSum R.p P' V.1 u').exp_V.mul_T ((softFuel (F:=F) (F':=F) R.p V [] (by simp) (fun i=>Soft.idem _ ((L.settleQ i).2 V))).leftR)) V').cong
 intro z w; exact showUp U A V v (P' z) (F z)
include p ρ e₀ t tl α
lemma chargedTransfer (hD : l.Pairwise (fun i j=>Commute (D i) (D j))) :
    tipI (fun z=>denZ (polarized (N:=N) R σ F K c P' τ E z) U A V) l =
    Mew.puzzleRecharge (fun x y=> acts (x.map D).prod (tipI (fun z=> denZ (prevGram R F P' z) U A V) y)) l :=
    (((L.softPose U A V c p v P' τ l u' E e₀ ρ).follows (L.accounting U A V c p v P' t τ D α l tl u')).tip l (List.Sublist.refl _)).trans (Mew.legRecharge _ (L.formerR U A V v P' u') D c l tl (uS_b σ ρ) hD)
omit t ρ α tl e₀ v u'

-- new notice on the additional input E (then can add to the one on the earlier input)
lemma noticeRecharge (o:I→Site (mid N B))(r:σ=Cube.node∘o)(T:∀ i (X:Scree.Hub (mid N B)), E i X≠0 → σ i ∈ X.val.2):
    Notice o ΔE ΔF ∧ (∀ i:I,νTip (ΔE) i=E i ∧ emberTip (ΔF) i = νΦK (placePort R.p F K c) {i}) := by
 let D:= spaceD R.p F K c τ; let F':= placePort R.p F K c -- syntax tune
 let be:= L.regPort c p τ; let W:= L.deltaPort c p
 have he(i:I):νTip ΔE i=E i:=value_E σ E D i; have hv(i:I): emberTip ΔF i = νΦK F' {i}:= value_F σ F' i
 refine ⟨⟨cash0 σ E D F',fun i=>?_, eReady σ E D, fun i=> ?_, fReady σ F', fun i w=>by rw [he,hv]; exact ⟨crest_E σ E D i w,crest_K σ F' i w⟩⟩,fun i=>⟨he i,hv i⟩⟩
 · nth_rw 1 [←r]; exact quietE σ E D be T _
 nth_rw 1 [←r]; exact quietF σ F' W _
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.chargedTransfer
#print axioms YM.CF.Vow.TreasuryFog.Furrow.noticeRecharge
