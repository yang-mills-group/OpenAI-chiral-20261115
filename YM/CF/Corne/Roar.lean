import YM.CF.Corne.Boost
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
variable(T:Tube G S)(x u v:ℝ)(P:Tab S)(q:Chi)(d α:ℝ)(l:ℕ)(M: Monk G S)
local notation "a₀"=> M.key
local notation "Q₀"=>(M.park,M.k)
local notation "N₀"=>kist M
local notation "Z₀"=>rough M 0
-- flat TAG addbacks. expose zero from investment. masks.Probe proof. isolate $leftV braid separately for later
variable(β:ℝ)(J:ChartRatio G)(t:ℝ) (j r:ℕ)
local notation "L"=>M.key.dome (j*radiusB x)
lemma capAX (h:FreshT T x u q J t b σ n l Q₀ C m)(p:K.Funds S T)(hv:Ready T x)(hk:0 < m)(hx:1000 ≤ radiusB x)(hr:l+76 ≤ j)(hz:∀ i:Site c,i∉ M.key.dome (j*radiusB x)→Taurus u M ((l+68)*radiusB x) i) : Bright T x u q d α l M β J t j:=by
 constructor; intro i hu; have he:i ∉ M.key.dome (horn x l):=fun z=> hu (farther (Nat.mul_le_mul_right _ hr) z)
 let Q:(Monk G S) := Z₀; let V:= dawn_h T x q d α l β Z₀ rfl hv hx i he; unfold Tarn.Coin; simp only [Pi.sub_apply] 
 rw [show rugG T x q d α l Q₀ i M.V=_ from V,← show (_:ℂ)= MossZ T x q d l J t Q₀ i M.V from due T x q d l Z₀ β J t rfl hv hx i he, tipC T x u q d b l M J t h i (fun z=> hu (farther (Nat.mul_le_mul_right _ (by omega)) z)) p hv hx hk (hz i hu)]; unfold kite qerr kist; dsimp only [rough]; push_cast; abel
open Cloak
end YM.CF.Corne
