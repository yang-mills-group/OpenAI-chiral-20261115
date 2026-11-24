import YM.CF.Sour.Rate
import YM.CF.Sour.Millet
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
structure Glyph (H:Op (Single n)→ FC (Dwell n))(Z:Single n→Single n→FC (Dwell n))(h:ℝ):Prop where
 whirl (K:Op JS) : H K=∑ i,∑ j,K i j • Z i j
 arc i j: Ark (Z i j) h (h^2)
 rod(S: SO)(i j:Single n): node i.1.1 ∈ S → node j.1.1 ∈ S→ Sector (camp S) false (Z i j)
 stamp(g: Seat n→SU.E)(K:Op JS): H (twist (tradew n g) K)=sauce false false (tradew n g) (H K)
namespace Glyph
variable {J:Op (Single n)→FC (Dwell n)}{Z:Single n→ Single n→ FC (Dwell n)}{h:ℝ}(q:Glyph J Z h){S:Support (More n)}{t d m a:ℝ}{r:ℕ}{L:Scree.Loom n}(p:Roof n t d r L)(v:0<d){F: Raw (Openc (More n) d) (Single n)}{C:Toll (Single n)} (f: Suite (badge _) (bail n d) (bail n d) S C F)
def cure (J:Op JS→Γ)(p:Roof n t d r L)(v:0<d)(F:Raw (Openc (More n) d) (Single n)):Firing n:=fun x=> J (F (roller v p x))
local notation "M"=> cure J p v F
include p v q f
lemma pays : Measurable M:=by
 have hp: Measurable (F∘roller v p):= f.toTicket.cont.measurable.comp (roll_m v p)
 unfold cure; simp_rw [q.whirl]; apply Finset.measurable_fun_sum; intro i _; apply Finset.measurable_fun_sum; intro j _; exact ((((show Continuous (fun x:Op JS=> x i j) from continuous_id.matrix_elem i j).measurable).comp hp).smul measurable_const)
lemma stencil (i:Orbit n):Sector (camp S) false (M i):=by
 unfold cure; rw [q.whirl]; apply Sector.sumS; intro j _; apply Sector.sumS; intro k _; let u:= roller v p i; by_cases g:F u j k=0; · rw [g,zero_smul]; apply Sector.zero
 obtain ⟨l,t,z⟩:= (f.expo j k).triggered (ne_of_gt ((norm_pos_iff.mpr g).trans_le ((f.expo ..).bounded _))); exact (q.rod S j k t z).scale _
lemma fra(V:Orbit n)(t:Seat n→ SU.E): M (Lattice.gauge t V.1,threadG t V.2)=sauce false false (tradew n t) (M V):=by
 let x:=roller v p V; unfold cure; rw [roller,show (⟨_,_⟩:Openc (More n) d)= _ from roll_g v p t V, show F _=twist (tradew n t) (F x) from ?_, q.stamp] -- tune
 rw [Inter.frame f.toTicket.frame t (roller v p V),twist_formula]; rfl
variable (b:P.threshold ≤ t)(g₀:halo (cipherK r) D⊆X.val)(hs:cipherK r≤5*P.B)(ht:3≤ P.B)(w:halo (r+10) S ⊆ Y.val)(u:Y.val⊆X.val)(e: HopeT d m a P.order)(e0:P.threshold ≤ a)
def vest (P:BudgetPoint)(h:ℝ)(C:Toll JS):ℝ:=(P.order+1:ℝ)* ledgerV C*h^2
include b g₀ w u
lemma horn :Crate P X D Y M:=by
 refine ⟨pays q p v f,fun i=>lift_v (stencil q p v f i) ?_, fun i j x y z t=> ?_,fun i g _=> fra q p v f i g⟩
 · intro k t; exact mem_filter.mpr ⟨mem_univ _,w (halo_subset _ _ (mem_filter.mp t).2)⟩
 exact congrArg J (pact_p v p f i j (poli p b g₀ x S (w.trans u) y z t))
include hs ht e e0
lemma sail_p : Marque P X Y D M h (vest P h C):=by
 refine ⟨horn q p v f b g₀ w u,?_⟩
 let H(i j:JS)(x:Orbit n):= F (roller v p x) i j • Z i j; let G(i j:JS):=(P.order+1:ℝ)*C i j*h^2
 have hp(i j): AuraOp P X D (H i j) h (G i j):=by apply AuraOp.sat h (P:=P) (fun i'=>F (roller v p i') i j) (Z i j) (q.arc i j) (mul_nonneg (by positivity) (f.nonn i j)); intro V s R m; exact bare_p _ _ (earn_b v p b f e V X (w.trans u) e0 g₀ hs ht s m _ _)
 have hs':M=∑ i:JS,∑ j:JS,H i j:=by funext i; unfold cure; rw [q.whirl,Finset.sum_apply]; simp_rw [Finset.sum_apply]; rfl
 rw [hs', show vest P h C= ∑ i:JS,∑ j:JS,G i j from ?_]; exact (AuraOp.sumR _ _ _ _ fun i _=> AuraOp.sumR _ _ _ _ fun j _=> hp i j).pay
 unfold vest ledgerV G; simp_rw [mul_sum,sum_mul]
end Glyph
end YM.CF.Sour
