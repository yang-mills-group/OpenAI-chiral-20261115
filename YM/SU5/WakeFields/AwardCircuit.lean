import YM.SU5.WakeFields.Depot
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
variable {a b f : ℝ} (P' : Key I→ RegBudget (mid N B))
-- actual perturbation record; shapes from each health; Sigma_L unspecified synchronization.
variable (o:I→Site (mid N B))
-- `science` only on FleetS, ties or tag etc can require.Probe purchases everywhere for now.
open Py Neon Sault Sour Crawl Swell
local notation "𝒢"=> prevGram R F P'
local notation "Γ"=> Cube.node ∘ o
variable (V₁:I→ Key I → Bag (mid N B))(D:I→Orbit (mid N B)→ FC (Single (mid N B)))
-- Stable Vacancy crossing. Ask for applications with old+density_P arbitrary at all knots.
-- note no charge-rotation certificate here, `r`: root coordinates. caps on further θ spending can be added.
variable (X g : ℝ) (δ : Side) (t : ℕ) (τ:Ids (mid N B))
structure OfficeAward (o : I→Site (mid N B))(δ:Side)(t q c:ℕ)(C : Occlus R.p)(τ:Ids (mid N B))(g X:ℝ)(D:I→Orbit (mid N B)→ FC (Single (mid N B)))
    (K : Key I→ Rinse (Seat (mid N B)) (Copy (mid N B)))
    (Y W : Key I → Aura (mid N B)→ ℝ)(J : Key I → Aura (mid N B)→ Support (More (mid N B))→ℝ) (M : Key I→ Bag (mid N B))
    (E : I→ RegBudget (mid N B))(X₁ : I→ ArcΦ) : Prop where
    badge : Furrow (Cube.node ∘ o) C q F h K Y W J M
    spends : ∀ i:I, Axon δ.val (o i) R.p (E i) h X (X₁ i)
    poseEntry : ∀ i:I, SpanTip R.p (E i) (node (o i)) K τ i
    ancestry : Notice o (awake (Cube.node ∘o) (spaceD R.p F K c τ) E) (bustle (Cube.node ∘o) (placePort R.p F K c))
    jet : ∀ i:I, νTip (awake (Cube.node ∘o) (spaceD R.p F K c τ) E) i = E i ∧
       emberTip (bustle (Cube.node ∘o) (placePort R.p F K c)) i= νΦK (placePort R.p F K c) {i}
    castWidth : ∀ z:Key I, FlagWidth R.p (bustle (Cube.node ∘o) (placePort R.p F K c) z) (cipherK q)
    paid : ∀ z:Key I,(∀ i, ‖z i‖ ≤ 2) →
       IncX primeU (awake (Cube.node ∘o) (spaceD R.p F K c τ) E z) R.p h
          ((2*X*t)+ sigma (C.η+C.η) R.p.B*yσE R.p C) ∧
       Dark primeU (bustle (Cube.node ∘o) (placePort R.p F K c) z) R.p h
          (Real.exp (g*t)*(yσF R.p C+yσF R.p C))
    honors : ∀ l:List I, l.length ≤ c → ψS (Cube.node ∘o) l →∀ V:Orbit (mid N B), FleetS R.p.threshold V.1 → IsStarProjection (spar j R.J.M (A V)) → l.Pairwise (fun i j=> Commute (D i V) (D j V)) →
       tipI (fun z=> denZ (polarized R (Cube.node ∘o) F K c P' τ E z) U A V) l =
          Mew.puzzleRecharge (fun x y=> acts (x.map (fun i=>D i V)).prod (tipI (fun z=>denZ (prevGram R F P' z) U A V) y)) l

variable (B' : CompatOffice (R:=R) U A (F:=F) P' o V₁ D (careRate C) (q:=q) (h:=h) (a:=a) (b:=b))
variable (Ge : FuelTag (R:=R) F o f C q h) (Z₀ : ∀ i x,River (fun z=>P' z i x))
variable (T : Mentor C t a b f) (D' : Force_M R.p.B (Cube.node∘o) t)
variable (wx:4 ≤ Real.exp g)(vA:0 ≤ g)(wC:9*g*t ≤ C.η*(R.p.B:ℝ)^2)
variable (uc:1≤c)
include p wx vA wC D' Z₀ uc
-- now crossing with first-tip assignment on `SpanTip`
lemma redeem (L : Furrow (Cube.node ∘ o) C q F h K Y W J M) (Q : ∀ V,∀ v:IsStarProjection (spar j R.J.M (A V)),Costume R V A v U M (fun i=> D i V) F P')
    (E : I→ RegBudget (mid N B))(Z : I→ ArcΦ)(tE:0 ≤ X)
    (vE : ∀ i, Axon δ.val (o i) R.p (E i) h X (Z i) ∧ SpanTip R.p (E i) (node (o i)) K τ i) :
    OfficeAward (h:=h) U A (F:=F) P' o δ t q c C τ g X D K Y W J M E Z := by
 have ht (i:I) (Y:Scree.Hub m) (f:E i Y≠0): Cube.node (o i) ∈ Y.val.2:= (not_not.mp (_root_.mt ((vE i).1.site Y) f)) ▸ Y.property
 obtain ⟨f,q'⟩:= L.noticeRecharge (R:=R) c p τ E o rfl ht
 refine ⟨L,fun i=> (vE i).1,fun i=>(vE i).2,f,q', L.portalWidth p c,?_,?_⟩
 · intro z hz; exact ⟨Larch.add_v R.p _ _ (lean_C R o t p δ E Z D' (fun i=> (vE i).1) z hz tE) (L.deepShelf p c τ z g wx vA wC D' hz), L.litShelf p c z g wx vA ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num: (6:ℝ)≤9) vA) (Nat.cast_nonneg _)).trans wC) D' hz⟩
 intro l tl r V v t e
 exact L.chargedTransfer U A V c p t P' v τ (fun i=>D i V) (Q V t) l tl (fun i=> Z₀ i V.1) E (fun i W=> L.conducts c p i uc τ E (vE i).2 _) r e

omit wx vA wC Z₀ uc
include T B' Ge
lemma buildOffice :
    ∃ (K : Key I→ Rinse (Seat m) (Copy m)),∃ Y W J, Furrow (Cube.node ∘ o) C q F h K Y W J (lug V₁) ∧ ∀ (V:Orbit m)(v:IsStarProjection (spar j R.J.M (A V))),Costume R V A v U (lug V₁) (fun i=> D i V) F P':= by
 obtain ⟨K,Y,W,J,h⟩:= fundingMint T V₁ (o:=Cube.node ∘o) B'.pack p B'.locale F Ge.quota Ge.article D'
 exact ⟨K,Y,W,J,h,fun V v=>poseCompat U A V v P' o V₁ D B'⟩
omit T

-- a particular useful alternate application: somebody with TWO cool bills can receive an empty-shape reply directly.
variable (s:ℕ)
variable (uΓ : Mentor C t (Crawl.costLoss s (careRate C)*a) (Crawl.costLoss s (careRate C)*b) f)
include wx vA wC uc Z₀ uΓ
lemma upwardPrize 
    (uH: δ.val ≤ s^3) (tar : 2*Crawl.till R.p s ≤ (More (mid N B)).val) (v:0 ≤ careRate C):
    let M := lug (fun i z=> aurora R.p (node (o i)) s (V₁ i z))
    ∃ (K : Key I→ Rinse (Seat m) (Copy m)),∃ Y W J, OfficeAward (h:=h) U A (F:=F) P' o δ t q c C τ g (payAnchor R.p C) D K Y W J M (countRoot R.p (Cube.node ∘ o) (spaceD R.p F K c τ) (fun _=>outerRoom R.p s)) 0 := by
 intro M; let t':= widenDepot U A P' o V₁ D s v B'; obtain ⟨K,Y,W,J,H,B⟩:= buildOffice (h:=h) U A p P' o _ D t t' Ge uΓ D' -- tune
 refine ⟨K,Y,W,J, redeem U A c p P' o D (payAnchor R.p C) g δ t τ Z₀ D' wx vA wC uc H B _ _ ?_ ?_⟩
 exact H.anchor_nonneg p -- check parameters
 exact fun i=> H.noClaim (R:=R) c p o τ s rfl tar ⟨V₁,rfl⟩ uc δ.val uH i
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.redeem
#print axioms YM.CF.Vow.TreasuryFog.Furrow.upwardPrize
