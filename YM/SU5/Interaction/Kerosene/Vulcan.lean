import YM.SU5.Interaction.Kerosene.Casework
import YM.SU5.Interaction.Kerosene.Stoke
import YM.CF.Stax.Flow

/- Act once with an anchored kernel. Momentum and cost lemma. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 720000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{h:ℝ}{δ:ℕ}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(C C':Aura n→ℝ)
variable (M:Orbit n→Aura n→ FC (Dwell n))(T:Pitch P h δ K C M)
structure WickL (P:BudgetPoint)(h:ℝ)(δ:ℕ)(K:Rinse (Seat n) (Copy n))(C C':Aura n→ℝ)(M: Orbit n→ Aura n→ FC (Dwell n))(D: Finset (Seat n)) : Prop extends Pitch P h δ K C M where
 birth (X:Aura n): Fray P h δ X ∅ (K X ∅ X 1) (C' X)
 overlayRoom : ∀ (X Y:Aura n)(U: Support (More n)), ¬ D⊆ Y.val → ∀ F:Copy n, K X U Y F=0
variable {D₀:Finset (Seat n)}(g: WickL P h δ K C C' M D₀)(u:0 ≤ h)
local notation "Bl"=> charglass C C' r

def volta (K:Rinse (Seat n) (Copy n))(F:Cusp n) := F + Cadre.Stoke K F
section utility
variable {X:Aura n}{D:Support (More n)}{U V:Copy n}{a b:ℝ}
lemma Fray.crossAdd (p:Fray P h δ X D U a)(q:Fray P h δ X D V b):Fray P h δ X D (U+V) (a+b):=⟨p.merit.plus q.merit,fun i g=>by by_contra f; exact g (by rw [Pi.add_apply,show U i=0 from Classical.byContradiction fun z=> f (p.loaf i z),show V i=0 from Classical.byContradiction fun z=> f (q.loaf i z),zero_add])⟩
end utility
include hF T u
lemma chokeVert (X:Aura n)(D:Support (More n))(p:D⊆ X.val) (Y:Aura n)(G:hook (Seat n))(v:G∈drum X Y D) : let U(j:Aura n) := F j (D∩j.val); let V:= ∏ j∈G,U j; Fray P h δ X D (K X D Y V) (C Y*wedgeL r D G) := T.plays X D p Y ((drum_p ..|>.mp v).2.2 ▸ subset_union_left) _ _ (Fray.vert G v _ _ (fun i _=> hF i _ inter_subset_right) u)
omit T
include g
lemma markStroke(X:Aura n)(D:Support (More n))(u':D⊆ X.val): Fray P h δ X D (Cadre.Stoke K F X D) (Bl X D) := by
 rw [stoke_energy]; unfold charglass
 apply Fray.crossAdd
 · split_ifs with t
   · exact ⟨Medal.zeroT,fun i v=>(v rfl).elim⟩
   rw [not_nonempty_iff_eq_empty.mp t]; exact g.birth X
 apply Fray.sumP; intro Y _; unfold Cadre.blast; rw [mul_sum]; apply Fray.sumP; intro G p; exact chokeVert F r hF K C M g.toPitch u X D u' Y G (mem_inter.mp p).1
-- Advancement
lemma markVolta(X:Aura n)(D: Support (More n))(u':D⊆X.val): Fray P h δ X D (volta K F X D) ((r+Bl) X D):= (hF X D u').crossAdd (markStroke F r hF K C C' M g u X D u')
variable (x:Orbit n)(p:FleetS P.threshold x.1)
local notation "Ωx"=> flags P.threshold x.1
include p
lemma advanceL (e: D₀.Nonempty) : acts (hGas Ωx (hailV Ωx (volta K F) x)).val (vacuum (Dwell n))=acts (1+∑ Y:Aura n,M x Y) (acts (hGas Ωx (hailV Ωx F x)).val (vacuum (Dwell n))):=by
 let R:=hailV Ωx F x; let Z:=hailV Ωx (Cadre.Stoke K F) x; let V(X Y:Aura n)(G:hook (Seat n)):= (let D:=Ωx∩X.val; K X D Y (∏ j∈G,F j (D∩j.val)) x)
 have he(X:Aura n): Z X=∑ Y:Aura n,∑ G∈ drum X Y (Ωx ∩ X.val), V X Y G:= by unfold Z hailV Cadre.Stoke V; simp_rw [Finset.sum_apply]
 obtain ⟨w,e⟩:=e
 have hx(X Y:Aura n)(G:hook (Seat n))(v:G∈drum X Y (Ωx∩X.val)): let D:=Ωx∩X.val; (V X Y G).val = Sault.rind (M x Y*(∏ j∈G,R j).val):=by
    intro D; let N:=∏ j∈G,F j (D∩j.val)
    have hg:= (drum_p ..|>.mp v).2.2; have ht:N x = ∏ j∈ G,R j:=by
       unfold N; rw [Finset.prod_apply]; unfold R hailV; refine prod_congr rfl fun j u=>?_; unfold D; rw [inter_assoc,inter_eq_right.mpr ((coneL u).trans (hg ▸ subset_union_right))]
    rw [← ht]; exact g.body X Y x p (hg ▸ subset_union_left) (wedgeL r D G) N (Fray.vert G v (fun i=>F i (D∩i.val)) (fun i=>r i (D∩i.val)) (fun i _=> hF i _ inter_subset_right) u)
 let C0:= fun i:Aura n=> camp (n:=n) i.val; have ht: hailV Ωx (volta K F) x= R + Z:= rfl
 rw [ht]; apply stoke_hGas Ωx w C0 (M x) R Z V he hx (g.edge x) _ (fun X=> (hF X _ inter_subset_right).merit.lit _)
 · intro Y h; unfold Z hailV; rw [stoke_zero _ _ K F D₀ (fun X Y U F t=>g.overlayRoom X Y U t F)]; rfl; exact fun y=>h (y e)
 intro X Y q; exact Finset.disjoint_left.mpr fun {i} g p=>Finset.disjoint_left.mp q (mem_filter.mp g).2 (mem_filter.mp p).2
end YM.CF.Stax
#print axioms YM.CF.Stax.advanceL
