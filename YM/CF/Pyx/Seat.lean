import YM.CF.Pyx.Rent
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Pyx
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
open Girt
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable(E:Type*) (Q:Oracle n)
variable (F: BoundedT (n:=n) Q)
abbrev Track(n:Side):=Pane n→Phys n→L[ℝ]ℂ
abbrev tintK(W:Track n):Prop:=∀ x V,W x V=∫ y:Ids n,Q (x,y) V∂depot n
abbrev StampK(W:Track n):Prop:=∀ x,Envelope fun i=>W i x
abbrev CureP(W:Track n):Prop:=∀ g x V,W (gauge g x) (effectK (tradew n g).val V)=W x V
include F
lemma crus_e :∃ X: Track n, tintK Q X∧ StampK X:=by
 let f(U:Pane n)(x:Phys n):= ∫ y:Ids n,Q (U,y) x ∂depot n; have he(U: Pane n)(x:Phys n): Integrable (fun y=> Q (U,y) x) (depot _):= Env.integrableX (snap (F x) (X:=fun y=>(U,y)) (by fun_prop)) _
 let T (y:Pane n): Phys n→ₗ[ℝ]ℂ:={toFun:=f y,map_add':=fun i j=>by unfold f; simp only [map_add]; exact integral_add (he ..) (he ..), map_smul':=fun i j=>by unfold f; simp only [map_smul]; exact integral_smul ..}
 refine ⟨fun y=>(T y).toContinuousLinearMap,fun i v=>rfl,fun v=>?_⟩; let K(x:Ids n × Pane n):=Q x.swap v; have ht:= snap (X:=Prod.swap) (F v) (by fun_prop); exact Env.marginal (g:=K) ht _
variable (Wk:Track n)(u:tintK Q Wk)
include u
lemma bowK(V: Pane n→ Phys n)(p:Envelope V):(∫ y:Pane n,Wk y (V y)∂prior group (More n))=∫ x:Orbit n,Q x (V x.1) ∂city _:=by
 let f(x:Orbit n):= Q x (V x.1); have ht:Envelope f:=listen _ (show Measurable (fun x:Orbit n=>x) from measurable_id) (snap p measurable_fst) F; simp_rw [u]; exact (integral_prod f (Env.integrableX ht _)).symm
private abbrev tagD(g:Seat n→SU.group.El):MeasurableEquiv (Ids n) (Ids n):=⟨⟨threadG g,threadG g⁻¹,threads_T _,fun i=>by simpa only [inv_inv] using threads_T g⁻¹ i⟩,(threads g).measurable,(threads _).measurable⟩
omit F
lemma planet (p:Loyal Q): CureP Wk:=by
 intro g x V; rw [u,u]; rw [← (show MeasurePreserving (tagD g) (depot n) (depot n) from threads g).integral_comp' (fun i:Ids n=> Q (Lattice.gauge g x,i) _)]; apply integral_congr_ae; exact Eventually.of_forall fun i=> p g (x,i) V
omit u
-- Wilson link endpoint test actual without assuming physical correlation irreps in limit
open Graph Emu
variable {α:Type*} (O:Graph.Opt (α:=α) n)
def plume :Oracle n:= fun V=> ( (innerSL ℂ (mateK n)).comp (acts (muni O.o V.1 O.R O.f O.L))).restrictScalars ℝ
lemma hosted: BoundedT (plume O):=fun i=> earned O (fun _=> i) ⟨measurable_const,_,fun _=> le_refl ‖i‖⟩
lemma shield : Loyal (plume O):=by
 intro g x V; let N:=mateK n; let A:=muni O.o x.1 O.R O.f O.L; let c:=tradew n g; change inner ℂ N (acts _ (acts (quantU c).val V))= inner ℂ N (acts A V)
 rw [show muni O.o ((gird g x).1) O.R O.f O.L= twist (quantU c) A from teen ..,twist_formula,act_mul,act_unit,act_mul];
 have ht:=act_unit_inner (quantU c) N (acts A V); rw [show (acts (quantU c).val) N=N from mastC g] at ht; exact ht
end YM.CF.Pyx
