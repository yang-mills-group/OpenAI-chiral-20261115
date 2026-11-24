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
variable(β:ℝ)(J:ChartRatio G)(t s e s' L:ℝ) (j r:ℕ)
local notation "L₀"=>M.key.dome (j*radiusB x)
abbrev penR(y:ℕ)(i:Site c):= beds T x q d l M y i - tit T x N₀ i y
def arcD := -(1/2:ℝ)* Real.log (baseX T x (kist M).key (kist M).park (kist M).k 1).det
def artU(i:Site c):= porry T x q d l M i
-- zero goal for flat refs ink/kite. analytic
abbrev flat_w(i:Site c):=kite T x q d l N₀ β J t i-ink T x q d α l β i N₀
def zenA(i:Site c):= kite T x q d l M β J t i- kite T x q d l Z₀ β J t i - (ink T x q d α l β i M-ink T x q d α l β i Z₀)+flat_w T x q d α l M β J t i
open Cloak
variable{θ t' w μ:ℝ}
variable(Ω:Tab S→DirP c)(p:ℕ)(F' W':BudgetPoint)
def brawn := (∑ O∈blip S M.key r,oak T x M q d l β F' W' j O.val)+ (-β*(∑ y,issueC T x M q d l j Ω p y) + -β*averaged (fun t=> ∑ i∈rush x M.key t j,shotB (dense T x q d l β t i) M)+ ∑ e: Bond f,opus T x q d l β j e M)
-- expose Coin*M F.G crossing future. EXACT
abbrev junk:= (∑ y∈L₀,(kite T x q d l M β J t y+qerr T x q d l M y)) - jewel T x q d l M β J t j
abbrev archQ:=arcD T x M + (∑' j:ℕ,∑ i:Site c,penR T x q d l M (j+3) i) +∑ i:Site c, artU T x q d l M i
abbrev warmth:= junk T x q d l M β J t j + (brawn T x q d l M β j r Ω p F' W'- veil T x q d α l M β j r F' W')
abbrev bus := (∑ i∈L₀ᶜ,zenA T x q d α l M β J t i)
abbrev gearC:= archQ T x q d l M+ warmth T x q d α l M β J t j r Ω p F' W'+ bus T x q d α l M β J t j
lemma voteD(h:NameX T M x q d l n C θ t' w μ)(hN:NameX T N₀ x q d l n C θ t' w μ)(v:Bright T x u q d α l M β J t j): ((∑ i,kite T x q d l M β J t i)-jewel T x q d l M β J t j)+apexA T x M q d l β F' W' r j α Ω p= gearC T x q d α l M β J t j r Ω p F' W' -∑ i∈L₀ᶜ,(Coin T x u q J t d α l Q₀ i M.V).re:=by
 let Δ:= Real.log |(credW T M.key M.park M.k q d x (M.bush x) l M.V).det|; let J₀:=brawn T x q d l M β j r Ω p F' W'; let Z:= arcD T x M
 have ht:Δ= archQ T x q d l M+∑ i:Site c,qerr T x q d l M i:=by
    have he:= (eerie T x q d l M h hN); dsimp only at he; have hT:=he.tsum_eq; change (∑' j:ℕ,∑ i:Site c,penR T x q d l M (j+3) i)=Δ-Z-∑ i,(artU T x q d l M i+qerr T x q d l M i) at hT; unfold archQ; rw [hT,sum_add_distrib]; unfold Z; ring
 let A:=archQ T x q d l M; let V:= fun i=>qerr T x q d l M i; let Z(i):= kite T x q d l M β J t i; let I(s:Monk G S)(i:Site c):=ink T x q d α l β i s; let v':=veil T x q d α l M β j r F' W'; let Y:= (∑ i∈L₀ᶜ,(Coin T x u q J t d α l Q₀ i M.V).re)
 let Q:=jewel T x q d l M β J t j; rw [show apexA T x M q d l β F' W' r j α Ω p= Δ+J₀-lit_x T x M q d l β F' W' r j α from rfl,normU,ht]; change (∑ i,Z i)-Q+(A+(∑ i,V i)+ J₀- (v'+∑ i∈L₀ᶜ,I M i))= A+((∑ i∈ L₀,(Z i+V i))-Q+(J₀-v'))+bus T x q d α l M β J t j-Y
 rw [←sum_add_sum_compl L₀ Z,←sum_add_sum_compl L₀ V,sum_add_distrib]; let B:= bus T x q d α l M β J t j
 have hk:B-Y= (∑ i∈L₀ᶜ,Z i)+(∑ i∈L₀ᶜ,V i)-(∑ i∈L₀ᶜ,I M i):=by
    unfold B bus Y; rw [←sum_sub_distrib,← sum_add_distrib,←sum_sub_distrib]; apply sum_congr rfl; intro i t; rw [v.sung _ (mem_compl.mp t),Complex.ofReal_re]; unfold zenA Z V flat_w I; ring
 linarith only [hk]
lemma actZ(h:NameX T M x q d l n C θ t' w μ)(hN:NameX T N₀ x q d l n C θ t' w μ)(v:Bright T x u q d α l M β J t j)(hX:0<d)(hp:d≤t): heirI T x M q d l β F' W' r j α Ω p J e s' L= Qen T x q d l M β e s' j * (∏ i∈blip S M.key r,treat T x M q d l β J e s' L r j i)*Real.exp (gearC T x q d α l M β J t j r Ω p F' W' -∑ i∈L₀ᶜ,(Coin T x u q J t d α l Q₀ i M.V).re) := by
 unfold heirI; rw [←voteD T x u q d α l M β J t j r Ω p F' W' h hN v, lore T x q d l M β J t e s' j hX hp, Real.exp_add]; unfold kite; ring
end YM.CF.Corne
