import YM.SU5.WakeFields.LegActual
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

namespace Soft
variable {I E : Type} [Fintype I] [LinearOrder I] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g h : Mew.Key I→ E} (l : List I)
lemma idem (v : River f) : Soft l f f:=⟨v,v,fun _ _=>rfl⟩
lemma addFlood {h : ℕ} (t : l.length ≤ h) (p : River f)
    (q : Flood (h+1) (fun z=>g z-f z)) : Soft l g f := by
 let G(z):=g z-f z
 have ht : g = fun z=> G z+f z:=funext fun z=> by unfold G; rw [sub_add_cancel]
 rw [ht]; refine ⟨dub_V (f:=G) q.riv p,p,fun i v=>?_⟩
 rw [tip_A (f:=G) q.riv p, show tipI G i=0 from q.ebb i (Nat.lt_succ_of_le (v.length_le.trans t)),zero_add]
variable {l}
lemma follows (p : Soft l f g) (v : Soft l g h) : Soft l f h := ⟨p.1,v.2,fun x t=> (p.tip x t).trans (v.tip x t)⟩
lemma back (p : Soft l f g) : Soft l g f := ⟨p.2,p.1,fun x t=> (p.tip x t).symm⟩
end Soft
namespace Furrow
variable {I : Type} [Fintype I] [LinearOrder I]
variable {n : Side} {P : BudgetPoint}
    {F F' : Mew.Key I→ ForceBudget n}
    {K : Key I→ Rinse (Seat n) (Copy n)}
    {Y W : Key I → Aura n→ ℝ}{J : Key I → Aura n→ Support (More n)→ℝ} {M : Key I→ Bag n}
    {C:Occlus P} {q : ℕ} {h : ℝ} {σ : I→Seat n}
variable (L : Furrow σ C q F h K Y W J M) (c : ℕ)(p : 1 ≤ h)
open Bake
include L p
lemma regPort (τ:Ids n)(i:Scree.Hub n) : Hush σ i.val.2 (fun z=> spaceD P F K c τ z i) ∧ ∀ V:Pane n,River (fun z=> spaceD P F K c τ z i V) := by
 let T (x):= spaceG P F K c x; let g:= lagE i
 have ht:Hush σ g.val (fun z=>T z g):= lore_H (spaceSimple F K c) P σ (fun i=> L.layerStay c _ ∅ (empty_subset _)) g -- defeq transparency
 refine ⟨?_,fun V=>?_⟩
 · intro x hx y hy p; funext V; exact congrArg (fun g':Copy n=> bassH g • g' (V,τ)) (ht x hx y hy p)
 exact bScale (fun z=>T z g (V,τ)) (L.simpleFlow c p g (V,τ)) (bassH g)
lemma pathPort (i : Force n) : Hush σ i.val.1.val.2 (fun z=> spacePort P F K c z i) ∧ ∀ V,River (fun z=> spacePort P F K c z i V) := by
 let G:=lordD i; let D:= extraD i; let Q:= spaceK P F K c
 refine ⟨fun z hz x hx v=>?_,fun V=>?_⟩
 · refine congrArg (bassH G • ·) ?_
   exact moto_H P (spaceCells F K c) 0 σ (L.layerStay c) (fun _ _ _ _ _ _ _ _=>rfl) G D z hz x hx v -- tune Binder order
 exact bScale (fun z=> Q z G D V) (moto_R P (spaceCells F K c) 0 (L.layerFlow c) (fun _ _ _ V=>zeroR _) (L.simpleFlow c p) _ _ V) (bassH G) -- tune

lemma deltaPort (i : Force n) : Hush σ i.val.1.val.2 (fun z=> placePort P F K c z i) ∧ ∀ V,River (fun z=> placePort P F K c z i V) := by
 let Z:= L.pathPort c p i; let W:= L.pathPort 0 p i
 exact ⟨fun z hz x hx v=>congrArg₂ (·-·) (Z.1 z hz x hx v) (W.1 z hz x hx v), fun x=> river_minus _ _ (Z.2 x) (W.2 x)⟩
omit L p
variable (P)
lemma readingSum (F : Mew.Key I → RegBudget n) (U:Pane n)(p : ∀ i:Scree.Hub n,River (fun z=> F z i U)) : River (fun z=> exponentL P (F z) U) := by
 unfold exponentL; refine tick_sum _ _ (fun i _=>?_)
 by_cases h:pingS P.threshold i.val.2 U
 · unfold numbE; simp_rw [Set.indicator_of_mem (show U∈{U|pingS P.threshold i.val.2 U} from h)]; exact p i
 unfold numbE; simp_rw [Set.indicator_of_notMem (show U∉{U|pingS P.threshold i.val.2 U} from h)]; exact zeroR _
lemma softFuel (V:Orbit n)(l : List I)(t : l.Nodup) (p : ∀ i : Force n,Soft l (fun z=>F z i V) (fun z=>F' z i V)) : Soft l (circF (P:=P) V F) (circF (P:=P) V F') := by
 unfold circF fueled; refine Soft.sum' univ (fun i v=>?_); split; swap; exact Soft.same_t ..
 refine Soft.gain _ _ _ (fun j v=>?_) t; unfold clamp; split; exact p j; exact Soft.same_t ..
end Furrow
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
open PowerSeries
local notation "Ψμ" z:max => cumQ (settleK (F z)) (K z) V R.p
variable (D : I→ FC (Single (mid N B)))
variable (α : Costume R V A v U M D F P')
variable (l : List I)(tl : l.length ≤ c)
variable (u' : ∀ i:Scree.Hub (mid N B),River (fun z=> P' z i V.1))
include p t L α u'
lemma actualEnd :
    Flood (c+1) (fun z=>denZ (charged R F K c P' τ z) U A V -
        ∑ r∈range (c+1),acts (Liss.paper D r z) (denZ (prevGram R F P' z) U A V)) := by
 let O:= flags R.p.threshold V.1; let X(z):= Θ z; let Q(z):= cumQ (settleK (F z)) (K z) V R.p; let G'(z):= hGas O (Q z); let H(z):= hGas O (hailV O (X z) V)
 let E(z):= NormedSpace.exp (exponentL R.p (P' z) V.1)
 have hz(j:Aura m)(r:ℕ): Flood r (fun z=> (coeff r (Q z j))) := by
    unfold Q cumQ; simp_rw [Stax.fP]; exact L.floods r j _ inter_subset_right V
 let g:= poseY U A V v
 let R'(z):=H z-Cadre.slice c (G' z)
 have e : Flood (c+1) R':=by
    refine (Cadre.wakeGas Q hz O c).cong (fun z _=>?_)
    have b: hailV O (X z) V= Cadre.slice c ∘ Q z:= by
       funext i; unfold hailV X spaceCells layerN Cadre.slice Q cumQ; rw [Finset.sum_apply]; simp_rw [Function.comp_apply, Stax.fP]; rfl
    unfold R' H; rw [b]
 have uB:= Flood.transport ((Flood.ground (readingSum R.p P' V.1 u'|>.exp_V)).times e) g; rw [Nat.zero_add] at uB
 refine uB.cong (fun z w=>?_)
 change _=g (E z*R' z); unfold R'; rw [mul_sub,map_sub]
 apply congrArg₂ (·-·)
 · exact L.chargeTape U A V c p v P' t τ z w
 rw [Cadre.slice,mul_sum,map_sum]; exact Finset.sum_congr rfl (fun i qi=> (L.actTape U A V i p v P' t D α z w).symm)

-- keep an equality at the level of Soft prefer in estimator
include tl
lemma accounting : Soft l (fun z=> denZ (charged R F K c P' τ z) U A V) (fun z=> ∑ i∈range (c+1), acts (Liss.paper D i z) (denZ (prevGram R F P' z) U A V)) := by
 refine Soft.addFlood l tl ((tip_bank (range (c+1)) (fun i z=> acts (Liss.paper D i z) (denZ (G z) U A V)) (fun i _=>?_)).1) (L.actualEnd U A V c p v P' t τ D α u')
 let O:=flags R.p.threshold V.1; let Q(z):= cumQ (settleK (F z)) (K z) V R.p
 let s (z):= coeff i (hGas O (Q z))
 have hx: River s:= (Cadre.gasCoeff Q (fun j v=>?_ ) O i).riv; rotate_left
 · unfold Q cumQ; simp_rw [Stax.fP]; exact L.floods v _ _ inter_subset_right V
 exact (sc_V ((readingSum R.p P' V.1 u'|>.exp_V).mul_T hx) (poseY U A V v)).cong (fun z w=> (L.actTape U A V i p v P' t D α z w).symm)
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.accounting
