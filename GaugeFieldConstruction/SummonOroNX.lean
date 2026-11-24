import GaugeFieldConstruction.OroConsulNX
-- computes the strong tested propagative prices in GetsThin. NOTHING centered remains here.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2800
set_option linter.unusedSectionVars false
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze Sifter VoucherOp Theatre
variable {P:Spine}{R:P.Register}{x:P.Spectrum0 3}{D N:Doorway}{M:P.Menagerie}
variable {F G:SampleDose}{c b r:ℕ→ℕ}{i:ℕ}{o:Orders}(w:P.Dawn R x (c i) (r i) D N o F G M)(Z W:Lead.Clan){T:∀ Z:Lead.Clan,P.VoucherOp x Z (r i) b}{a:ℝ}
variable (U:P.GetsThin R x c r i a F G b T)
local notation "ξ"=> (flagsFor Z W)
local notation "L"=> fun j:Bool=> T (flagsFor Z W j)
local notation "Y"=> P.electro M
local notation "Φ"=> (smearsFor F G)
local notation "Ψ"=>Theatre.answer x (flagsFor Z W) (fun i=>T (flagsFor Z W i)) id (smearsFor F G) lEdge rEdge
include w U
lemma goldenDawnNX : P.jointPrice x r i F G b Z W T=star (P.electro M Z)*P.electro M W ∧
   Theatre.answer x (flagsFor Z W) (fun i=>T (flagsFor Z W i)) id (smearsFor F G) lEdge rEdge [false]=star (P.electro M Z) ∧ Theatre.answer x (flagsFor Z W) (fun i=>T (flagsFor Z W i)) id (smearsFor F G) lEdge rEdge [true]=P.electro M W:=by
   have hL(m:List Bool)(p:PlayPrice x (flagsFor Z W) (fun j=>T (flagsFor Z W j)) id (smearsFor F G) lEdge rEdge m)(Q:ℂ)(q:∀ ε> (0:ℝ),∀ᶠ s in atTop, ∀ᶠ t:ℕ in atTop,‖measuredPrice x (flagsFor Z W) (fun j=>T (flagsFor Z W j)) id (fun _=>s) (smearsFor F G) m t-Q‖≤ε): Theatre.answer x (flagsFor Z W) (fun i=>T (flagsFor Z W i)) id (smearsFor F G) lEdge rEdge m=Q:=by
     let B:ℕ→Bool→ℕ:=fun s _=>s
     obtain ⟨hp,ht,hw⟩:= p.passage B (fun _ _=> tendsto_id)
     refine tendsto_nhds_unique ht (Metric.tendsto_nhds.mpr ?_)
     intro e v
     filter_upwards [hp,q (e/2) (half_pos v)] with s q s'
     let g:=p.footQualified (B s) q
     rw[dist_eq_norm]; exact (le_of_tendsto ((g.2.2.1.sub_const Q).norm) s').trans_lt (half_lt_self v)
   let A:= U.channel Z W
   have hg(ε:ℝ)(p:0<ε):∀ᶠ s:ℕ in atTop,∀ᶠ t:ℕ in atTop,
     ‖P.singleState 3 t x ((T Z).markField false s t F*(T W).markField true s t G)-star ((P.electro M) Z)*(P.electro M) W‖≤ε ∧
     ‖P.singleState 3 t x ((T Z).markField false s t F)-star ((P.electro M) Z)‖≤ε ∧
     ‖P.singleState 3 t x ((T W).markField true s t G)-(P.electro M) W‖≤ε:=by
      have hv:= bothFlowNX w Z W (U.purchased.2.tendsto_atTop) (T Z) (T W) ε p
      have ha:Tendsto (fun s:ℕ=>(s,s)) atTop atTop:=by rw[←prod_atTop_atTop_eq]; exact tendsto_id.prodMk tendsto_id
      filter_upwards [ha.eventually hv] with s v; filter_upwards [(T Z).alwaysLater s,(T W).alwaysLater s] with t h k; exact v t h k
   -- replace
   constructor
   · refine hL wedding A.pair _ (fun ε v=>(hg ε v).mono (fun s w=>w.mono fun t h=>?_))
     unfold measuredPrice Theatre.word wedding; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; exact h.1
   constructor
   · refine hL [false] A.earlier _ (fun ε v=>(hg ε v).mono (fun s w=>w.mono fun t h=>?_)); unfold measuredPrice Theatre.word; simp only[List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; exact h.2.1
   refine hL [true] A.later _ (fun ε v=>(hg ε v).mono (fun s w=>w.mono fun t h=>?_)); unfold measuredPrice Theatre.word; simp only[List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; exact h.2.2
#print axioms goldenDawnNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
