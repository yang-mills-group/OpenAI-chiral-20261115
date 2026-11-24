import YM.CF.Corne.Flat
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
abbrev kite(i:Site c):= dua T x q d l β J t i M
abbrev qerr(i:Site c):= Quill T x q d l M i-Quill T x q d l N₀ i
abbrev porry(i:Site c):= Quill T x q d l N₀ i-∑ i'∈Finset.range 3, tit T x N₀ i i'
abbrev Orr:= Coin T x u q J t d α l Q₀
structure Bright:Prop where
 sung (i:Site c)(h:i ∉ M.key.dome (j*radiusB x)) : Coin T x u q J t d α l Q₀ i M.V=((ink T x q d α l β i Z₀-ink T x q d α l β i N₀-kite T x q d l Z₀ β J t i+kite T x q d l N₀ β J t i-qerr T x q d l M i):ℝ)
lemma capB (h:FreshT T x u q J t α σ n l Q₀ C m)(p:K.Funds S T)(hv:Ready T x)(hk:0 < m)(hx:1000 ≤ radiusB x)(hr:l+76 ≤ j)(hz:∀ i:Site c,i∉ M.key.dome (j*radiusB x)→Taurus u M ((l+68)*radiusB x) i) : Bright T x u q d α l M β J t j:=by
 constructor; intro i hu; have he:i ∉ M.key.dome (horn x l):=fun z=> hu (farther (Nat.mul_le_mul_right _ hr) z)
 let Q:(Monk G S) := Z₀; let V:= dawn_h T x q d α l β Z₀ rfl hv hx i he; unfold Tarn.Coin; simp only [Pi.sub_apply] 
 rw [show rugG T x q d α l Q₀ i M.V=_ from V,← show (_:ℂ)= MossZ T x q d l J t Q₀ i M.V from due T x q d l Z₀ β J t rfl hv hx i he, tipC T x u q d α l M J t h i (fun z=> hu (farther (Nat.mul_le_mul_right _ (by omega)) z)) p hv hx hk (hz i hu)]; unfold kite qerr kist; dsimp only [rough]; push_cast; abel
open Cloak
variable(F' W':BudgetPoint)
abbrev veil:=averaged fun s=>let U:=M.sent x T q d l β; (∑ i, leftV T U s a₀ q F' x β i)-(∑ i,rightV T M.V s a₀ W' x α β i)+ ∑ k∈blip S a₀ r, ∑ i∈strum x s k.val j, heatR T U M.V s a₀ q F' W' x α i
lemma sent_h (k:Signed)(X:Along S→ℝ) : ∑ i∈rush x M.key k j, X i=∑ z∈Lᶜ, ∑ v∈Arena.hoop S k z,X v:=by
 unfold Arena.hoop; simp_rw [sum_filter]; rw [sum_comm]; unfold rush; rw [sum_filter]; exact sum_congr rfl fun i _=>by simp
lemma normU : lit_x T x M q d l β F' W' r j α= veil T x q d α l M β j r F' W'+∑ z∈ Lᶜ, ink T x q d α l β z M:=by
 unfold lit_x veil averaged ink; dsimp only; simp_rw [sent_h x M j] -- tune implicit order
 unfold averaged; rw [←mul_sum,sum_comm (t:=univ) (f:=fun z i=>∑ j∈Arena.hoop S i z,fle T x q d α l β i j M),←mul_add,←sum_add_distrib]; apply congrArg _; refine sum_congr rfl fun i _=>?_ ; unfold fle; abel
end YM.CF.Corne
