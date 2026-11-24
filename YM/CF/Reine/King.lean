import YM.CF.Reine.Mast
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
open Vol
variable (T:Tube G S)(x:ℝ)(M: Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(F' W:BudgetPoint)
local notation "V₀"=>M.V
local notation "a₀"=> M.key
local notation "m₀"=> M.park
local notation "Y₀"=>M.bush x
local notation "Z₀"=> M.bell x
local notation "Q₀"=> M.k
local notation "ξ"=>M.sent x T q d l β
local notation "T₂"=>tend T x M q d l β F' W
open Affine
variable(P:Patch)(C₀:Teller G)(R:ChartRatio G)(w s L:ℝ)(v₁ j:ℕ)(D D' C':ℝ)
local notation "χ₀"=> M.fuel x T q d l β
local notation "K₀"=>M.key
local notation "ε₀"=>embH T a₀ m₀ V₀ Q₀ q β d x Y₀ l Z₀
local notation "Ps"=> subU T x M q d l β R w s L j (r:=v₁)
local notation "pZ"=> keto T x M q d l β R w s j
local notation "drumJ"=> blip S a₀ v₁
variable{D D' C'}
local notation "bZ"=> ψ T x M q d l β R w L
-- include step full compatibility. Pf determinants. No logs caps yet
local notation "Δ"=>Real.log |(credW T a₀ m₀ Q₀ q d x Y₀ l V₀).det|
variable (α:ℝ)
def tenderU := T.up.inChannels T.high F' β ξ - T.down.inChannels T.low W (β+α) V₀
def riseP:= μL T x M q d l β F' W v₁ j + Δ - veer T x β F' W α ξ V₀
def yeoman:= pZ * (∏ i∈drumJ,treat T x M q d l β R w s L v₁ j i) * Real.exp (riseP T x M q d l β F' W v₁ j α)
local notation "τ"=> tenderU T x M q d l β F' W α
lemma plunge (K:Cert P C₀ S T x)(h:FuelG ℝ (fun _=>ξ) 0 n D)(he:shovel S.patch+10≤ radiusB x)(Hv:Volo S n s D' D C')(hf:0<fiery G x S.patch.L)(hk:fiery G x S.patch.L ≤ s/2)(hq:M.key.flags=flags (temp x) V₀)(hL:L ≠0)(hp:(j+110)*radiusB x+10 ≤ v₁)(hX:taxM x ≤ j*radiusB x)(hB:0<β)(hv:F'.threshold=fiery G x S.patch.L)(hV:W.threshold=temp x)(H:spanO T x)(Ht:spanC T x)(hZ:0<temp x)(hs:f0 T x a₀ m₀ Q₀ V₀ q d Y₀=Rows.source T x V₀ Q₀ (shots S x) a₀ m₀ q d Y₀): L ^ Fintype.card (Active a₀ x m₀) * (Fintype.card S.Choices:ℝ)*Girt.plight T x β q R d l w M * Real.exp (-τ)= L^ Fintype.card M.park.Free * yeoman T x M q d l β F' W R w s L v₁ j α :=by
 let a:=L^Fintype.card M.park.Free; let X(O:Hos S v₁):= ε₀ (whim x j O.val); let jP:= ∑ i∈drumJ,X i; let R':= riseP T x M q d l β F' W v₁ j α; let Z:= μL T x M q d l β F' W v₁ j; let f:= ε₀ (fun _=> Appel.globe S); let g:= β*wholeGap T x ξ V₀; let M':= f+Cay.adjust T x q d l β M+Δ+g-τ
 have hθ:= dawn_p T x M q d l β P C₀ R w s L v₁ j D D' C' K h he Hv hf hk hq hL hp
 have hg (i:Hos S v₁): treat T x M q d l β R w s L v₁ j i=Ps i* Real.exp (X i):=by
    unfold treat subU Monk.pep -- notation error
    by_cases h': M.silver x T s i.val q d l β w j=0; simp [h']
    simp_rw [wrap_e T x M q d l β P C₀ w s j D D' C' i.val K h H he Hv hZ hf hk hq hB hs h']; unfold X; ring
 unfold yeoman; rw [show L^_*↑(Fintype.card S.Choices)*Girt.plight T x β q R d l w M*Real.exp (-τ)= bZ * Real.exp M' from ?_]; swap
 · unfold Girt.plight Girt.glowV ψ M' f g Cay.adjust; simp_rw [Real.exp_sub,Real.exp_add] -- watch nested def
   rw [show putU β T M.park M.key M.V M.k x l q d (M.bush x) (M.bell x)= tape (χ₀) from rfl]; unfold sepB sepQ; rw [show fieldU β T m₀ a₀ V₀ Q₀ x l q d Y₀ Z₀=ξ from rfl, Real.exp_neg]; ring_nf -- tune
 simp_rw [hg,Finset.prod_mul_distrib]; rw [← Real.exp_sum]; change bZ * _= a*(pZ* ((∏ i∈drumJ,Ps i)*Real.exp jP)*Real.exp R'); rw [show a*(pZ*((∏ i∈drumJ,Ps i)*Real.exp jP)*Real.exp R')= bZ * Real.exp (jP+R') from ?_]; swap; · rw [hθ,Real.exp_add]; unfold a; ring
 by_cases hx:bZ=0; · simp [hx]
 have ht:= priceW T x M q d l β F' W P C₀ R w L v₁ j hx hp hX hf hB hv hV H Ht hq hs K ; let t:=averaged (fun s=>∑ i,T₂ s i); let v:= veer T x β F' W α (ξ) V₀
 have hh:τ=v+ g+β*t:= curve_y _ _ _ _ _ _ _ _ _ _ hv hV -- tune implicit
 change f+ -β*t+Cay.adjust _ _ _ _ _ _ M=jP+Z at ht; congr 2; unfold M'; change _= jP+(Z+Δ-v); rw [hh]; linarith only [ht]
end
end YM.CF.Reine
