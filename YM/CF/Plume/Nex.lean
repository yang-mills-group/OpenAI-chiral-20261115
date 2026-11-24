import YM.CF.Plume.Stream
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt Next.Fluctuations.Sector Dial
-- explicit product induction over real.S.Team.
lemma integral_P {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][Fintype F][MeasurableSpace F][MeasurableSingletonClass F](Y:F→ E): ∫ t,Y t∂paperMeas F=(Fintype.card F:ℝ)⁻¹ • ∑ i:F,Y i:=by
 rw [paperMeas,integral_smul_measure,integral_finsetSum_measure]; simp; exact fun _ _=> integrable_dirac (by simp)
section actuate
variable {J' W v x' e y Z A':ℝ}{ι:Type}[Fintype ι][DecidableEq ι]
def cort (U:Pane (mid N B))(s:Cord S): Monk G₀ S:= ⟨bareStores S,s.1.1,s.1.2,U,s.2.1.1,s.2.1.2⟩
variable{L:Side}{j o l D k r:ℕ}{hL:Odd L.val}{Y:Pricing j L hL (Thread j)}
variable (G:Ratio (mid N B) (mid P B))(C:GramM (mid N B))(R:GramM (mid P B))(T:Tube G₀ S)(P':Grasp Y B e)(V:Orbit (mid N B)) (F:Scree.Loom (mid N B))(F':Scree.Loom (mid P B))(Q:Op SU.Slot)(q h:Chi)(u:ℝ)
variable (X:Girt.BaseL P' G R F F' q u)(p:S.ratio= Rush.ratio G)(w:S.patch.Branches S.kernel SU.group)(K:Teller G₀)(Ω:ChartRatio G₀)(M:Girt.Flo S T K h Ω x W A' y R.beta o l)
local notation "Wμ"=> plummy S y
local notation "X⬝" => Monk G₀ S
local notation "D⬝"=> Cipher (mid N B)
local notation "ZΩ"=> Orbit (mid N B)
variable (Dμ:ι→Palot.leaf (Site (Domain N B)))
variable (U : (z:Cord S)→ Dress G S e r D (cort V.1 z) R k Dμ)
local notation "Δ"=> (shotM Ω y R.beta)
local notation "T₁"=> (upMale L hL R.J.M)
local notation "aL"=> (flags (temp x) V.1)
local notation "u₀"=> (F V)
local notation "m"=> (spar j (upMale L hL R.J.M) (F V)) -- binder err
-- conclusions of shone after specifying uniforms. no 0. require only fairness
abbrev primK (U:Op (Single (mid N B)))(x':IsStarProjection U)(y:Phys (mid N B))(c:ℝ)(z g:ℂ):D⬝→L[ℝ] Phys (mid N B):= LinearMap.toContinuousLinearMap {toFun:=fun t=> c • z • g • acts ((nursery _ x').eval t.val) y,map_add':= fun i j=> by rw [Subalgebra.coe_add,map_add,act_add]; simp only [smul_add],map_smul':= fun x t=> by dsimp only [RingHom.id_apply]; rw [show ((x•t:Cipher (mid N B))).val=x • t.val from rfl,(nursery _ x').eval_r,RCLike.real_smul_eq_coe_smul (K:=ℂ) x ( (nursery U x').eval t.val),act_smul,← RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [smul_comm g x (acts _ y),smul_comm z x,smul_comm c x]}
include X p w M
set_option maxHeartbeats 600000 in
lemma shuttle_s (z:ℂ)(F₀:Forest S.ratio) (wr:IsStarProjection (spar j T₁ (F V)))(ρ:∀ a:Cord S,Fairy S y a → (U a).pipe=T∧(U a).cloth=a.2.2∧(U a).wage=A'∧(U a).chi=h)(α:∀ a:Cord S,Fairy S y a →(∑ A:Stores S with A.flags= aL,(U a).boarding x l Ω P' V.2 A y W F F' q u)= (Δ^ Fintype.card a.1.1.Free) • Complex.exp (C.betaL F V-C.v+R.v) • z • acts ((nursery _ wr).eval (hGas aL (fun i=> mintF ((U a).blazon x l) (beamH i.val))).val) (Hive.nest P' C.J.P T₁ (F V)))
 (c:Arena.Tab S): let E:=primK m wr (Hive.nest P' C.J.P T₁ u₀) (Δ^Fintype.card F₀.Free) (Complex.exp (C.betaL F V-C.v+R.v)) z
 let f(a:Cord S):= hGas aL fun i=>mintF ((U a).blazon x l) (beamH i.val)
 ∫ y':TeamY (mid P B), E (f (c,y'))∂springT S y = (Fintype.card S.Choices:ℝ) • ∑ A:Stores S,(Δ^Fintype.card (Active A x c.1)) • ∫ z:TeamY (mid P B), yieldB P' G R F F' q u S p V c.1 T A c.2 h Ω x W A' l z∂springT S y :=by
    intro E B';
    let L'(A:Stores S)(z:TeamY (mid P B)):= (Δ^Fintype.card (Active A x c.1)*(Fintype.card S.Choices:ℝ)) • yieldB P' G R F F' q u S p V c.1 T A c.2 h Ω x W A' l z
    have hz:(∫ y':TeamY (mid P B), E (B' (c,y'))∂springT S y) = ∫ z:TeamY (mid P B),∑ A:Stores S,L' A z∂springT S y:=by
       apply integral_congr_ae; filter_upwards [tone_v (S:=S) M.year] with y' v; let Z:Cord S:=(c,y'); change E (B' Z)=_
       have hf: Fairy S y Z:=v; have he:= α Z hf
       rw [SectorNext.Vacuum.FlatTree.same_free_card Z.1.1 F₀] at he; rw [show E (B' Z)=_ from he.symm]; have ht:=ρ Z hf
       rw [sum_filter]; apply sum_congr rfl; intro A _; unfold L' yieldB; simp only; split
       next p'=> unfold Dress.boarding; simp_rw [ht.1,ht.2.2.1,ht.2.2.2]; unfold Dress.stories; simp only [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]; rfl -- align 派.S
       next p'=> rw [smul_zero]
    rw [hz,integral_finsetSum,Finset.smul_sum]; swap
    · intro i _; exact Integrable.smul (Δ^Fintype.card (Active i x c.1)*(Fintype.card S.Choices:ℝ)) (bait X S p w V c.1 T i c.2 h Ω x W A' y l K M).1
    apply sum_congr rfl; intro i _; unfold L'; rw [integral_smul, smul_smul,mul_comm]; -- mul_comm risks
end actuate
end YM.CF.Plume
