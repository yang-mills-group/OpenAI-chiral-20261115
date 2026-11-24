import YM.CF.Stake.Sect
import YM.CF.Iva.Iva
import YM.CF.Lor.Cred
import YM.CF.Tye.High
import YM.CF.Cloak.Shoal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L) (O:Acorn.Repair K.j){U:Grasp V.U B d}(W:GivenX V U)
def before_t(K:Teller SU.group)(n:ℕ)(p:3≤ n): Push.Uniform.Before SU.group K.top.width K.top.paths K.j K.bind n:= Classical.choice (Push.Uniform.pre_order _ _ _ _ _ p)
local notation "G5"=>SU.group
abbrev Year(R:Patch)(x:ℝ): Set ℝ:= Set.Icc (y G5 R.L x/2) (2*y G5 R.L x)
structure Pilot where
 cost:ℝ
 penalty:ℝ
 width:ℝ
 bump:ℝ -- moss.size
 large:ℝ
 s:ℝ -- analytic sat
 D:ℝ
 M:ℝ
 peak:ℝ
 gear:ℝ
 c4:ℝ -- moss n+8
 mpay:0<c4
 realC:0<cost
 earn:0<penalty
 small:1≤width
 fare:0<bump
 high:0<large
 crest:0<peak
 seek:0<s
 toll:0<gear
abbrev Pilot.skin(A:Pilot)(R:Patch)(x:ℝ):= A.width*fiery G5 x R.L
abbrev Pilot.hat(A:Pilot)(R:Patch)(x:ℝ):ℝ:= A.large*Scales.p G5 R.L x
abbrev Pilot.tail(A:Pilot)(R:Patch)(x:ℝ):= A.peak*Scales.p G5 R.L x
variable {q:Chi}(D:Pilot){x α β Z:ℝ}
structure FireK (L:ChartRatio SU.group)(q:Chi)(D:Pilot)(R:Patch)(K:Teller SU.group)(l k j:ℕ)(x:ℝ) :Prop where
 horizon: 0< fiery G5 x R.L
 blade:1000 ≤ radiusB x
 moat:shovel R+10≤radiusB x
 cloud:4*D.skin R x<L.radius
 sole: D.skin R x ≤ D.gear
 gain: 4*D.gear < L.radius
 years:0< x
 era:2*D.skin R x< firstRadius G5
 lope: Erin K R L k j l q D.cost D.width D.penalty x D.bump D.large D.s D.D D.M
 worn{N P B:Side}{S:StepData (Domain N B) (Domain P B)}(T:Tube SU.group S):Cert R K S T x→PointCharge T x D.cost D.penalty∧ Ready T x∧ spanO T x∧ Reine.spanC T x∧∀ M: Monk SU.group S,sizedP G5 R K S T M.park→Chir M x→ MossX (k+8) l x M.key M.park T M.V M.k D.c4 (D.skin R x) (fiery G5 x R.L) q ∧∀ β∈ Year R x, ‖M.z‖ ≤ D.tail R x → readyJ M T q l x (D.skin R x) D.s β D.cost
lemma flying(K:Teller G5)(R:Patch)(p:R.Branches K.bind G5)(vu:∀ᶠ w:ℝ in atTop,∃ u:ℝ,0<u ∧ K.cash R.L w u)(Q:LocalRatio L)(k j l:ℕ)(h:4≤ j)(w:3≤ k)(p':l ≤18) (q:Chi):∃ D:Pilot,∀ᶠ x:ℝ in atTop, FireK L q D R K l k j x:=by
 obtain ⟨i,y,a,b,f⟩:= Cloak.anchor K R p k l (by omega) p' q (before_t K _ (by omega)); obtain ⟨T,H⟩:= eventually_atTop.mp vu; let A:= max y T; have hh:0<A:= b.trans_le (le_max_left ..)
 obtain ⟨c,t,Y⟩:= H A (le_max_right ..); obtain ⟨N,v,N'⟩:=melonX K R p k j l w h p' (before_t K _ w) (before_t K _ (by omega)) q L Q A c hh t
 let U:= max i N; have hx:0<U:= a.trans_le (le_max_left ..)
 obtain ⟨J,M,s,D,D',hj,hM,hs,I,hD,Hy⟩:= N' U (le_max_right ..); obtain ⟨g,z,G⟩:=f J s hj hs; let g':= L.radius/8; have hz:= Q.patch; have h₁:0<g':= div_pos hz (by norm_num)
 obtain ⟨m',v',H'⟩:=turnsX (k+8) l U hx K R p (by omega) p' (before_t K _ (by omega)) q
 let P':Pilot:=⟨A,c,U,J,M,s,D,D',g,g',m',v',hh,t,v.trans (le_max_right ..),hj,hM,z,hs,h₁⟩; let x':=min g' (firstRadius G5/4); have ht:Tendsto (fun x=>U*fiery G5 x R.L) atTop (𝓝 0):=by have he:=(tally_g G5 R.L 0 1).const_mul U; rw [mul_zero] at he; apply he.congr; intro i; rw [fi]; ring
 have hu:x'<firstRadius G5:= lt_of_le_of_lt (min_le_right ..) (by linarith [first_pos G5]); have hv:4*g'<L.radius:=by unfold g'; linarith
 refine ⟨P',?_⟩; filter_upwards [Y.late, H', Hy, PatchReads.reserve K R,Reine.capable K R,(year G5 R.L).eventually_gt_atTop 0,G,ht.eventually (ge_mem_nhds (show 0<x' from lt_min h₁ (div_pos (first_pos _) (by norm_num)))),Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel R+1000),eventually_gt_atTop (0:ℝ)] with x Hh hh hx₀ H R' v G k' hy hu'
 have hv':0<fiery G5 x R.L:=by rw [fi]; exact mul_pos (Scales.gauge _ _ v) (Scales.pos ..)
 have hl:U*fiery G5 x R.L ≤g':=k'.trans (min_le_left ..); have hy':U*fiery G5 x R.L ≤ firstRadius G5/4:= k'.trans (min_le_right ..)
 refine ⟨hv',by omega,by omega, (mul_le_mul_of_nonneg_left hl (by norm_num : 0 ≤ (4:ℝ))).trans_lt hv,hl,hv,hu',show 2*(U*_)< _ from by linarith [first_pos G5], hx₀,?_⟩; intro N S B Z' T e; have hx:= e.funds.1
 obtain ⟨π,S'⟩:= R' Z' T e.got hx
 refine ⟨?_,H _ _ e.got e.size hx,π,S',fun M w h=> ⟨?_,?_⟩⟩
 · let hp:=congrArg RG.Patch.L e.got; intro I U V W Y p v; rw [hp]; exact Hh _ _ Z' hp e.size T hx _ _ _ _ _ p v
 · have he:=hh _ T e M.key M.park M.V w h M.k; rw [e.got] at he; exact he
 intro β v y'; obtain ⟨_,_,_,_,_,_,p⟩:= hx₀.heat β v; exact G _ T e U (le_max_left ..) A (le_max_left ..) M h w β v y' (p Z' T e M w h).1
end YM.CF.Stake
