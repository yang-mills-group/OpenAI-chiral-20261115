import YM.CF.Lor.Ton
import YM.CF.Vale.Lake
/-! Replacement for Lor.Ton.sing_k; DON’T use old API (hypothesis quantified over order zero `Before`, cannot instantiate!). Here use `Push.Uniform.pre_order`. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief BoreP rates Braid Rel
variable(L:Side)(j n:ℕ){Q K F:ℝ→ℝ}{u v t:ℕ}{Z:ℝ}
variable(l:ℕ)(h:5 ≤ l)
variable (R:Patch)(T:Teller SU.group)(q:Chi)
include h in
lemma sing_kValid (hl:l≤18)(hg:l+78 ≤ j)(hp:5 ≤ n)(hv:R.Branches T.bind SU.group)(F:∀ i:ℕ,3 ≤ i → i ≤ n+3 →  Push.Uniform.Before SU.group T.top.width T.top.paths T.j T.bind i):∃ V W:ℝ→ℝ,∃ E X,∃ r:ℕ,∃ C D σ:ℝ,sizeK R.L 1 V∧sizeK R.L 3 W ∧ CapY E∧ nib X∧0<C∧0<D∧0<σ∧ j ≤r ∧∀ᶠ x:ℝ in atTop,let Z:= X (Cay.horn x l); let a:=D*temp x^(l+2-4); let p:=E (Cay.horn x l); p ≤ (r-1)*radiusB x∧∀{c f:Side}(S:StepData (More c) f)(T':Tube SU.group S), Arena.Prime R T S T' x → (r+r+101)*radiusB x ≤ (More c).val→∀ d:ℝ, let F:=fun t:Tab S=> fame T' t q x d l; ∃ O,Arena.Woven F O p 2 n σ (C*Z) (a*Z)∧∀ (β:ℝ),β∈Set.Icc (y SU.group R.L x/2) (2*y SU.group R.L x) →∀ M:Monk SU.group S, M.key.flags=flags (temp x) M.V→∀ i:Site (More c), let X':=fun y=> -β*Cloak.issueC T' x (M.atop y x) q d l j O r i
 Allows n X' 0 (V x) ∧(i∉ M.key.dome (p+r*radiusB x)→ Allows n X' 0 (W x)):=by -- beta inside ∃ O wrong continuation. adjust.
 obtain ⟨w,P,t,a,b,C,D,σ,H,H',hs,h1,h2,h3,h4,h5,hX⟩:=sagaValid T R q l n j h hl hg hp hv F; let L:=R.L; have hu:= satV L n l h a b C D w P H H'
 let Y(x):ℝ:=2*y SU.group L x; let p(x):ℕ:=P (Cay.horn x l); let B(x):= w (Cay.horn x l); let A(x):=D*temp x^(l+2-4); let u(x):= Arena.compass n 2 x (C*B x) (A x*B x) b; let q'(x):= plot (p x)*u x; let X(x):=Arena.compass n 2 x C (A x) a+(q' x+q' x); let X'(x):=Arena.compass n 4 x (C*B x) (A x*B x) b
 refine ⟨fun x=> Y x*X x,fun x=>Y x*X' x,P,w,t,C,D,σ,year_r L _ _ hu.2.1,year_r L _ _ hu.2.2,H',H,h3,h4,h5,hs,?_⟩
 filter_upwards [hX,(year SU.group L).eventually_gt_atTop 0] with x hx v; intro Z A' p'; refine ⟨hx.1, fun S T' i j' d=>?_⟩; intro F'; obtain ⟨O,a,p⟩:=hx.2 _ _ i d j'; refine ⟨O,a,fun β b M v' i=>?_⟩; intro X₀; obtain ⟨ht,hK⟩:= p i M.V (M.park,M.k) M.key v'; have he: |(-β)| ≤ Y x:=by rw [abs_neg,abs_of_pos ((half_pos v).trans_le b.1)]; exact b.2
 let U:= issued x j t F' O M.key (M.park,M.k) i ∘ Vmove x M.V
 have hp(G:ℝ)(p: Allows n U 0 G): Allows n X₀ 0 (Y x*G):=by
    apply (((p.linear Complex.reCLM (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=>by rw [one_mul]; exact Complex.abs_re_le_norm i))).mono (one_mul _).le).smul (-β)).mono (mul_le_mul_of_nonneg_right he p.nonneg) -- tune abs
 exact ⟨hp _ ht,fun i=>hp _ (hK i)⟩
end YM.CF.Lor
