import YM.CF.Tye.Reign
import YM.CF.Pso.Dual
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
abbrev tint_z (t:ℝ):Muster G S x e T:= {A with beta:=t}
variable {v u:ℝ}(hp1:0<u)(ht':0<v)
local notation "Mt"=> poleY M v u
local notation "Vt"=> tint_z A v
local notation "Ut"=> tint_z A u
local notation "fu"=> M.fuel x T q v' L' u
local notation "fo"=> M.sent x T q v' L' u
include A M T hp1 ht'
lemma spirit_X: (poleY M v u).fuel x T q v' L' v=M.fuel x T q v' L' u∧(poleY M v u).sent x T q v' L' v=M.sent x T q v' L' u :=⟨lift_z T x q _ _ _ _ ht' hp1 M,port_z T x q _ _ _ _ ht' hp1 M⟩
lemma ball_m (s t:ℝ)(O:Stores S): ((Mt).silver x T s O q v' L' v t j')=M.silver x T s O q v' L' u t j' ∧ (Mt).copper x T O q v' L' v J j'=M.copper x T O q v' L' u J j' ∧ (Mt).tin x T s O q v' L' v j'=v/u*M.tin x T s O q v' L' u j':=by
 obtain ⟨a,b⟩:= spirit_X A M hp1 ht'; refine ⟨?_,?_,?_⟩
 · exact congrArg (fun W=>cohoT M.key x t s q M.V W M.k (obv x j' 100 O) (obv x j' 110 O)) b
 · exact congrArg (fun w=>capsule x M.key M.park q v' J (locals M.key O x M.park ((j'+104)*radiusB x)) (tape w)) a
 unfold Monk.tin Esti.σ pist; dsimp only
 unfold Monk.fuel at a; simp_rw [a]; dsimp only [poleY,Cay.rough]; field_simp; rfl
lemma kit_m : kite T x q v' L' Mt v J R i=kite T x q v' L' M u J R i ∧ Corne.ink T x q v' (α+γ) L' v i Mt=Corne.ink T x q v' (α+γ) L' u i M :=by
 obtain ⟨a,b⟩:=spirit_X A M hp1 ht'; unfold Corne.kite Corne.dua Corne.ink; simp_rw [Corne.flare,Corne.fle,a,b]; exact ⟨rfl,rfl⟩
lemma zero_w :Muster.blunt (tint_z A v) (poleY M v u) i=Muster.blunt (tint_z A u) M i:=by
 obtain ⟨a,b⟩:= kit_m A M i hp1 ht'; obtain ⟨p,q'⟩:=kit_m A (Cay.rough M 0) i hp1 ht'; rw [show poleY (Cay.rough M 0) v u=Cay.rough M 0 from (by unfold poleY Cay.rough; simp)] at p q'
 obtain ⟨k,l⟩:= kit_m A (kist M) i hp1 ht'; rw [show poleY (kist M) v u=kist M from (by unfold poleY Cay.rough kist; simp)] at k l
 unfold Muster.blunt; by_cases hp':i∈M.key.dome (A.loft*radiusB x)
 · rw [if_pos hp',if_pos (show i ∈ (Mt).key.dome ((Vt).loft*radiusB x) from hp')]; exact congrArg₂ (·+·) a (show qerr T x A.trot A.room A.post (poleY M v u) i=qerr T x A.trot A.room A.post M i from rfl)
 rw [if_neg hp',if_neg (show i ∉ (Mt).key.dome ((Vt).loft*radiusB x) from hp')]; unfold zenA flat_w; exact congrArg₂ (·+·) (congrArg₂ (·-·) (congrArg₂ (·-·) a p) (congrArg₂ (·-·) b q')) (congrArg₂ (·-·) k l)
lemma stern_a : mix (tint_z A v) (poleY M v u) i= v/u*(Muster.wish (tint_z A u) M i+flockK (tint_z A u) M i)+blunt (tint_z A u) M i +artU T x q v' L' M i:=by
 unfold mix; refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ (zero_w A M i hp1 ht')) (show artU T x q v' L' (poleY M v u) i=artU T x q v' L' M i from rfl)
 unfold flockK Muster.wish; dsimp only [tint_z]; simp_rw [shove_z T x q v' L' v u ht' hp1 M, opus_z T x q v' L' v u ht' hp1 M]; dsimp only [poleY,Cay.rough]; rw [mul_add, mul_sum]; apply congrArg₂
 · field_simp
 exact sum_congr rfl (fun _ _=>by ring)
end YM.CF.Tye
