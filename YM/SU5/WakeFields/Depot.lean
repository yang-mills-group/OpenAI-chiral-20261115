import YM.SU5.WakeFields.Crawl
import YM.SU5.Exchange.Stack.Nest
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
-- root provider on exactly old Key. 
structure CompatOffice (V':I→Key I → Bag (mid N B))(D:I→Orbit (mid N B)→ FC (Single (mid N B))) (u : ℝ) : Prop where
 pack : ∀ i z,z∈hill I→ Barrage R.p q ({node (o i)}:Support (More (mid N B))) h (V' i z) u a b
 locale : ∀ i:I,∀ X:Aura (mid N B), Hush (Cube.node ∘ o) X.val (fun z : Mew.Key I=> V' i z X) ∧ ∀ V:Orbit (mid N B),River (fun z=> V' i z X V)
 matchB (V:Orbit (mid N B)) (v:IsStarProjection (spar j R.J.M (A V))) :
    ∀ i:I,∀ z∈hill I,∀ X:Wave (Dwell m),pilotH U (prevGram R F P' z) A V v (acts (giveB (V' i z) V) X)=acts (D i V) (pilotH U (prevGram R F P' z) A V v X)
local notation "𝒢"=> prevGram R F P'
local notation "Γ"=> Cube.node ∘ o
variable (V₁:I→ Key I → Bag (mid N B))(D:I→Orbit (mid N B)→ FC (Single (mid N B)))
lemma poseCompat (Q : CompatOffice (R:=R) U A (F:=F) P' o V₁ D u (q:=q) (h:=h) (a:=a) (b:=b)) :
    Costume R V A v U (lug V₁) (fun i=> D i V) F P' := by
 constructor; intro z w X
 have he(i:Key I): (∑ (Y:Aura m), lug V₁ i Y V)=∑ j:I,i j • (giveB (V₁ j i) V):=by
    unfold lug agenda; simp_rw [Finset.sum_apply,Pi.smul_apply]; rw [sum_comm]; refine sum_congr rfl fun j _=> ?_; rw [Finset.smul_sum]
 rw [he]; rw [Liss.waveΦ, act_sum,act_sum,map_sum]; exact sum_congr rfl fun i _=>by simp_rw [act_smul,map_smul,Q.matchB V v i z w]

-- ticket exposing only increments. e0 costs from lower. true first tips synchronized later.
structure FuelTag (F : Key I→ForceBudget (mid N B))(o : I→ Site (mid N B))(k : ℝ) (C : Occlus R.p)(q : ℕ)(h:ℝ) : Prop where
 quota : ∀ z∈hill I,SanB (F z) (giftK R.p C.uΓ) R.p h (fun _=>k) ∧ FlagWidth R.p (F z) (cipherK q)
 article : ∀ i: Force (mid N B), Hush (Cube.node∘o) i.val.1.val.2 (fun z=> F z i) ∧ ∀ V:Orbit (mid N B),River (fun z=> F z i V)

lemma widenDepot (l:ℕ) (g:0≤u)(B': CompatOffice (R:=R) U A (F:=F) P' o V₁ D u (q:=q) (h:=h) (a:=a) (b:=b)) :
 CompatOffice (R:=R) U A (F:=F) P' o (fun i z=> aurora R.p (node (o i)) l (V₁ i z)) D u (q:=q) (h:=h) (a:=costLoss l u *a) (b:=costLoss l u*b) := by
 let W(z):= node (o z); let G(i:I)(z):= aurora R.p (W i) l (V₁ i z)
 refine ⟨?_,?_,?_⟩
 · intro i z h; exact Crawl.retreatCore (bloomC R.p l (W i)) _ _ (planted _ _ (B'.pack i z h) g) (singleton_subset_iff.mpr (Crawl.host _ _ _))
 · intro i X; constructor
   · intro z v w x p; refine sum_congr rfl fun j w'=>?_
     apply (B'.locale i j).1 z v w x; intro i u; apply p i; rw [←(mem_filter.mp w').2]; exact mem_union_left _ u
   intro V; unfold aurora; simp_rw [Finset.sum_apply]; exact (tip_bank _ _ (fun i' _=>(B'.locale _ i').2 V)).1
 intro V v i z w X; apply Eq.trans _ (B'.matchB V v i z w X); rw [show giveB (aurora R.p _ l (V₁ i z))=giveB (V₁ i z) from Crawl.sameModel _ _] -- maybe pattern with lhs?
variable (τ:Ids (mid N B)) (s:ℕ)
abbrev outerRoom {n:Side} (P:BudgetPoint) (s:ℕ) : Finset (Aura n):= univ.filter (fun i=> s ≤ coverNumber P.B i.val)
lemma noResidue (p:∃ V₁:I→ Key I→Bag (mid N B),M=lug (fun i z=> aurora R.p (node (o i)) s (V₁ i z))) (w:2*Crawl.till R.p s ≤ (More (mid N B)).val)(z:Key I)(X:Aura m)(u:X∉ outerRoom R.p s): M z X=0 := by
 obtain ⟨V₁,rfl⟩:=p; unfold lug agenda; rw [Finset.sum_apply]; apply sum_eq_zero; intro i _
 change z i • aurora R.p (node (o i)) s (V₁ i z) X= (0:Firing m); rw [rescue _ w X,smul_zero]; exact Nat.lt_of_not_ge (fun v=> u (mem_filter.mpr ⟨mem_univ _,v⟩))

local notation "κS"=> countRoot R.p Γ (spaceD R.p F K c τ) (fun _=>outerRoom R.p s)
-- diploma: empty-shape birth price here; requires correspondingly tiny fees before election merits. Can ask and use in motion preserving replant (symmetric).
include L p
lemma noClaim (pσ : σ = Cube.node∘o)
    (w:2*Crawl.till R.p s ≤ (More (mid N B)).val)
    (α:∃ V₁:I→ Key I→Bag (mid N B), M = lug (fun i z=> aurora R.p (node (o i)) s (V₁ i z)))
    (uBe:1 ≤ c) (δ:ℕ) (J:δ ≤ s^3) :
    ∀ i:I,Axon δ (o i) R.p (countRoot R.p (Cube.node∘o) (spaceD R.p F K c τ) (fun _=>outerRoom R.p s) i) h (payAnchor R.p C) 0 ∧ SpanTip R.p (countRoot R.p (Cube.node∘o) (spaceD R.p F K c τ) (fun _=>outerRoom R.p s) i) (node (o i)) K τ i := by
 subst σ; intro i; refine ⟨?_, L.rootShape c p τ (fun _=>outerRoom R.p s) i uBe (fun X _ t U z=> L.deadAt p X (fun y _=> noResidue o s α w y X t) i (U,τ))⟩ -- tune order
 refine ⟨L.anchorCircuit c p τ _ i,fun X p=>?_,fun X p=>?_⟩
 · exact if_neg (fun t=>p t.1)
 change Taxi.lifeH (κS i X) _= _ ∧ Neon.pillar _ _ _=_
 rw [show κS i X=0 from if_neg (fun t=>p.not_ge (J.trans (Nat.pow_le_pow_left (show s ≤ coverNumber R.p.B (Bake.lagE X).val from (mem_filter.mp (show Bake.lagE X∈outerRoom R.p s from t.2)).2) _))), Pill_0]; exact ⟨rfl, by split<;>rfl⟩
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.noClaim
#print axioms YM.CF.Vow.TreasuryFog.Furrow.widenDepot
