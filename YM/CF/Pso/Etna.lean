import YM.CF.Pso.Crawl
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
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
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
local notation "j'"=> A.loft
local notation "q"=> A.trot
local notation "Q"=> A.LawQ
local notation "L'"=> A.post
local notation "J"=> A.vita
local notation "R"=> A.rota
local notation "v'"=> A.room
local notation "H"=> A.hot
local notation "β"=> A.beta
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "X"=> kist M
variable (f:Sweep (mid N B))(W U': Rent0 G e)(i:Site (Domain N B))
variable {v u:ℝ}(hp1:0<u)(ht':0<v)
local notation "Mt"=> poleY M v u
local notation "Vt"=> tint_z A v
local notation "Ut"=> tint_z A u
local notation "fu"=> M.fuel x T q v' L' u
local notation "fo"=> M.sent x T q v' L' u
include M A
lemma terminal_w : Cay.rough (rot f Mt) 0=Cay.rough (rot f M) 0:=by
 unfold Cay.rough; rw [Tye.pose_t,Tye.pose_t,toss_a,toss_a,(person (poleY M v u) f).1,(person M f).1,(person (poleY M v u) f).2,(person M f).2,thereZ,thereZ]; rfl; --] -- tune
lemma long_z (k:Palot.leaf (Site (Domain N B))): mace (tint_z A v) (poleY M v u) k=mace A M k:=by unfold mace patrol; simp_rw [terminal_w A M]; rfl
variable {ρ:Type}[TopologicalSpace ρ](P_:ρ→ℝ)(c:Continuous P_)(hhP:∀ i,0<P_ i)
local notation "ζt" i:max=> tint_z A (P_ i)
local notation "ℙt" i:max=> poleY M (P_ i) u
include c hp1 hhP
lemma tea_c: Continuous (fun z=> Tye.mare (ζt z) (ℙt z) i):=by
 unfold mare patrol; simp_rw [terminal_w A M]; let u(x):=ζt x; refine Continuous.smul (continuous_const (y:=(Fintype.card (Sweep Z):ℝ)⁻¹)) (?_:Continuous (fun z=>∑ w:Sweep Z,payZ w (marble (ζt z) (Cay.rough (rot w M) 0) ((chart w).symm i)))); refine (continuous_finsetSum _ fun f2 _=> ?_)

 have ht:Continuous (fun z=> marble (ζt z) (Cay.rough (rot f2 M) 0) ((chart f2).symm i)):=by
    let I:= (chart f2).symm i; let m:= Cay.rough (rot f2 M) 0; let k:= issueC T x m q v' L' j' A.muK A.mup I; exact ((Complex.continuous_ofReal).comp (c.neg.mul (continuous_const (y:=k)))).sub (continuous_const (y:=booth A m I)) -- order
 exact (show Continuous (payZ f2) from by unfold Spire.payZ cSignX; split; exact continuous_star; exact continuous_id).comp ht
lemma mig_c: Continuous (fun z=> mig (ζt z) (ℙt z) W U' i):=by
 have ht:Continuous (fun z=>mix (ζt z) (ℙt z) i):=by
    simp_rw [fun z=> stern_a A M i hp1 (hhP z)]; exact ((((c.div_const u).mul continuous_const).add continuous_const).add continuous_const)
 exact (((Complex.continuous_ofReal.comp ht).add (continuous_const (y:=prum A M U' W i))).add (tea_c A M i hp1 P_ c hhP)) -- argument prum order
lemma sore_c (O:Stores S): Continuous (fun z=>soreG (ζt z) (ℙt z) O):=by
 let g(uX:Unit):= averaged (fun s: Signed=>∑ i∈lyn x s O j',Cloak.folkK T x M s q v' L' u A.phaseUp A.phaseLow i)
 let G_(o):= averaged (fun s:Signed=>∑ i∈strum x s o j',heatR T fo M.V s M.key q A.phaseUp A.phaseLow x (α+γ) i)
 have ht(z):gemG (ζt z) (ℙt z) O=gemG Ut M O:=by
    unfold gemG Corne.flare; dsimp only [tint_z]; simp_rw [(spirit_X A M hp1 (hhP z)).1]; rfl
 have hp(z): soreG (ζt z) (ℙt z) O=-(P_ z)*g () - G_ O-gemG Ut M O:=by
    unfold soreG oak; dsimp only [tint_z]; simp_rw [Cloak.folkK,(spirit_X A M hp1 (hhP z)).2]; rw [ht]; rfl
 simp_rw [hp]; exact ((c.neg.mul continuous_const).sub continuous_const).sub continuous_const
lemma tide_c (k:ℕ) (Va:Palot.leaf (Site (Domain N B))) : Continuous (fun z=>shardy (ζt z) (ℙt z) k Va):=by
 unfold shardy averaged; refine ((continuous_const.mul (continuous_finsetSum _ fun s _=> (continuous_finsetSum _ fun i _=>?_).sub (continuous_finsetSum _ fun j _=>?_))).neg)
 · unfold Muster.river sapU extU; dsimp only [tint_z]; simp_rw [fun z=> (spirit_X A M hp1 (hhP z)).2]; dsimp only [poleY,Cay.rough]; exact (c.mul continuous_const).add continuous_const
 unfold flows sapC extV; dsimp only [tint_z,poleY,Cay.rough]; exact ((((c.add continuous_const).mul continuous_const).add continuous_const).add continuous_const)
end YM.CF.Tye
