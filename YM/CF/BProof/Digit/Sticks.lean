import YM.CF.BProof.Digit.Twirl
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
open Push.AbsoluteSums Trees Mew Floral
open scoped YM.CF.Mew
variable {B G:Cusp n}{U:Set ℂ}{Q:blazeK n}{W z₀ z₁:ℝ}{δ:ℕ}{F H: Copy n} {Fa Ga: Bag n}{K J:Rinse (Seat n) (Copy n)} {μ γ:Aura n→ℝ}{R L:RegBudget n}
lemma lives_sum(p:Lives P δ X D F)(q:Lives P δ X D H):Lives P δ X D (F+H):=fun i v=> by by_cases u:F i=0; exact q i (fun h=>v (by simp [u,h])); exact p i u
lemma lives_c(p:Lives P δ X D F)(c:ℂ):Lives P δ X D (c • F):=fun i u=> p i fun q=>u (by rw [Pi.smul_apply,q,smul_zero])
lemma porch (c:ℂ)(p:Fray P W δ X D F z₀):Fray P W δ X D (c • F) (‖c‖*z₀):=⟨medal_scale c p.merit,lives_c p.loaf c⟩
lemma porch_a (p:Fray P W δ X D F z₀)(q:Fray P W δ X D H z₁): Fray P W δ X D (F+H) (z₀+z₁):=⟨p.merit.plus q.merit,lives_sum p.loaf q.loaf⟩
abbrev wire (P:BudgetPoint)(W:ℝ)(δ:ℕ)(K:Rinse (Seat n) (Copy n))(μ:Aura n→ℝ)(F:Bag n) := Pitch P W δ K μ (fun i Y=> F Y i)
namespace wire
variable (p:wire P W δ K μ Fa)(v:wire P W δ J γ Ga)
include p
lemma lamp_c (c:ℂ):wire P W δ (c • K) (‖c‖ • μ) (c • Fa):=by
 refine ⟨fun x=>mul_nonneg (norm_nonneg _) (p.dice x), fun X D Y=>by simp_rw [Pi.smul_apply,p.start, smul_zero],fun X D t Y v i F u=>?_,fun i Y=>(p.edge i Y).scale _,fun X Y i u v l F d=> ?_⟩
 · have he:=porch c (p.plays X D t Y v i _ u); rw [←mul_assoc] at he; exact he
 change c • (K X _ Y F i).val= Sault.rind (c • Fa Y i * (F i).val); rw [p.body X Y i u v l F d,Matrix.smul_mul, Sault.rind,Sault.rind,map_smul]
include v
lemma lamp_a:wire P W δ (K+J) (μ+γ) (Fa+Ga):=by
 refine ⟨fun x=>add_nonneg (p.dice x) (v.dice x),fun X D Y=>by simp_rw [Pi.add_apply,p.start,v.start,add_zero],fun X D z Y d x F w=> ?_,fun i Y=>(p.edge i Y).add (v.edge i Y),fun X Y i l t r U w=>?_⟩
 · have e:= porch_a (p.plays X D z Y d x _ w) (v.plays X D z Y d x _ w); rw [←add_mul] at e; exact e
 change (K X _ Y U i).val+(J X _ Y U i).val= Sault.rind ((Fa Y i+Ga Y i)*(U i).val); rw [p.body X Y i l t r _ w,v.body X Y i l t r _ w,add_mul,Sault.rind, Sault.rind, Sault.rind,map_add] -- tune
end wire
namespace Burst
variable (p:Burst P K R)(u:Burst P J L)
include p
lemma sail (c:ℂ): Burst P (c • K) (c • R):=by
 intro X; unfold birthL; rw [if_pos rfl]; funext i; simp_rw [Pi.smul_apply, orbV]; change c • (K X ∅ X 1 i) =_; rw [show K X ∅ X 1=orbV R X from (by simpa only [birthL, ite_true] using p X)]; unfold orbV; rw [smul_sum]; rfl
include u
lemma plus: Burst P (K+J) (R+L):=by intro X; funext i; change birthL K X ∅ i+birthL J X ∅ i= _; rw [p,u]; simp_rw [orbV,Pi.add_apply,sum_add_distrib] -- tune d
end Burst
lemma salute {F:Type*}[NormedAddCommGroup F][NormedSpace ℂ F](a b:F): Hol U fun z:ℂ=>a+z • b:= (differentiableOn_const a).add (differentiableOn_id.smul (differentiableOn_const _))
lemma maze {K J:ℂ→Rinse (Seat n) (Copy n)} (p: PlayC U K)(v: PlayC U J): PlayC U (fun z=>K z+z • J z):= fun X D Y i F T=> (p X D Y i F T).add (differentiableOn_id.smul (v X D Y i F T))
end YM.CF.Sour.Digit
