import YM.CF.Eire.Bare
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x:ℝ)(e_:ℝ)(r l k D:ℕ)
local notation "bay"=> Stilo.bay
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
open Rush Scroll Paige Vault Phase Acorn Spire
namespace Dress
variable {S G D k r l x}
variable (M:Monk SU.group S)(R:GramM (mid P B))
variable {M R X e_}
variable (U:Dress (r:=r) G S e_ D M R k X) -- order inferred?
variable (x:ℝ)(l:ℕ)
local notation "B₀"=> BranchX S X k
local notation "Fh"=> flags (temp x) M.V
local notation "O'"=> capG S Fh (chillB M) R.p.threshold
-- charged SCALAR Heir split.R.Phase law.JM.
-- exact table reassignment at arbitrary multipliers, stays conditional on material nonzero
variable {A:Stores S}{Z:Finset (Kite S r)}
local notation "κ"=> quaint (r:=r) (ι:=ι) (S:=S) (M:=M) (R:=R)
open Dial Broc Proa Pec Girt Scree Hest Kennel Arena Reine Oriented
variable {A':Type*}(J:ChartRatio SU.group)(W₀:WG A')(T:A'→ Male)(I:A'){Fx:Scree.Loom (mid P B)}{F:Scree.Loom (mid N B)}{q:Chi}{y₀ d D':ℝ}{L:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}(P':Grasp Y B e_)(C:GramM (mid N B))(Q:Ids (mid N B)){R₀:Patch}{T':Teller SU.group}
variable {Ht:GramM (mid N B)}
variable {γ L₁ L₀ H v D₁ D₂ H₁ s z z₁ z₂ δ a b c d' w α t:ℝ}{u j':ℕ}
local notation "Tq"=> (mid N B)
local notation "m"=>R.J.M
local notation "μ"=> upMale L o (R.J.M)
local notation "λw"=> F (M.V,Q)
local notation "Δ"=> shotM J v R.beta
local notation "Θ"=>spar j (upMale L o (R.J.M))
local notation "Yp"=> U.blocks A
local notation "Y₁"=> (U.blocks A).val.1
local notation "Ck"=> Teller
-- separate price RHS permutation cases to κ.L
variable (B':U.CrownX x l J P' C γ L₁ L₀ H v D₁ D₂ H₁ s z z₁ z₂ δ a b c d' w α t u j' W₀ T I F Fx q D' T' R₀)
variable (Ω:Arena.Tab S→ Arena.DirP (Domain N B))(δ':ℕ)
variable (Z':ℂ)
open scoped Classical
structure Aphro (Z':ℂ)(Fx:Scree.Loom (mid P B))(F:Scree.Loom (mid N B))(q:Chi)(D':ℝ)(A: Stores S) : Prop where
 heel: D=20*radiusB x
 snap:U.wager.Nodup
 hoop(i):i∈ blip S A r → i∈ U.wager
 crown : Clan G S (T:=U.pipe) U.axes Q U.cloth (trot S M A) F Fx U.chi q l x U.wage D' R.beta (U.blocks A)
 fame : W₀ I (mid P B) (Tulip.profile (U.blocks A).val.1.1)= R.J.P.den (U.blocks A).val.1.1
 cheer:Cheer (U.blocks A).val.1.1 (U.blocks A).val.2 A e_ (20*radiusB x) r
 ports: fulfills G U.odds e_ (j:=j) T W₀ I U.portT U.portG (bring U.yawB (U.blocks A))
 height: IsStarProjection (spar j (R.J.M) (U.blocks A).val.2)
 wealth: IsStarProjection (spar j (R.J.M) (U.blocks A).val.1.1)
 opX: ‖Pec.coatG L o j G m R.J.P.den (U.blocks A).val.1‖ < 1
 runsT: U.brood A≠ 0 → SubmitB S x R (trot S M A) U.pipe U.chi U.wage l
 paintP : (((heirI U.pipe x (trot S M A) U.chi U.wage l R.beta R.p C.p r j' α Ω δ' J H₁ s Δ : ℝ):ℂ)*Complex.exp (-Cour.shipA G P' m R.J.P.den R.J.I C.J.I (U.blocks A).val.1)) • (exp (Hest.boat (Hest.Budget L o R.J.P.den C.J.P.den G m j (U.blocks A).val.1))).val=Z' • (U.brood A).val
include B'
set_option maxHeartbeats 700000 in
lemma aphro_a (K: U.Aphro (α:=α) (H₁:=H₁) (s:=s) (v:=v) (j':=j') x l J W₀ T I P' C Q Ω δ' Z' Fx F q D' A) (g:A.flags= flags (temp x) M.V)(wr:IsStarProjection (Θ λw)) :
 U.boarding x l J P' Q A v H₁ F Fx q D'= (Δ^Fintype.card M.park.Free) • Complex.exp (C.betaL F (M.V,Q)-C.v+R.v) • Z' • acts ((nursery _ wr).eval (∑ i∈ κ A,(U.sweepG x l i).val)) (nest P' C.J.P μ λw):=by
 -- align proofs, cases D before.
 let X:= U.blocks A; let W:=X.val.1.2; have ht:W= λw:=congrArg (fun x=> x.1.2) K.crown; have hh: IsStarProjection (Θ W):=ht.symm ▸ wr; have hp:=K.heel; subst D; have hg:(U.taskA A).toFinset=blip S A r:=Finset.ext fun i=>by rw [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]; exact ⟨And.right,fun v=>⟨K.hoop i v,v⟩⟩
 rw [shore U x l g K.runsT K.cheer K.snap K.hoop]; have hx:= dawnK U x l J W₀ T I P' C Q B' Ω δ' A g K.crown hg K.fame K.cheer K.ports K.height K.wealth hh K.opX
 refine hx.trans ?_; try dsimp only
 let Z:=issue (U.stalk A) (R.board (U.stories x l A)).val (kindle e_ U.dyes U.pens U.cloth K.cheer (U.taskA A)); let D:= (U.brood A).val; let P:= (exp (boat (Hest.Budget L o R.J.P.den C.J.P.den G m j X.val.1))).val
 have hv:= boiler (0:Cipher Tq) D P Z _ hh (nest P' C.J.P μ W) _ _ _ K.paintP
 let P0(V: Pane Tq)(h:IsStarProjection (Θ V)):=Z' • acts ((nursery _ h).eval (Z*D)) (nest P' C.J.P μ V); have hK(K L: Pane Tq)(p:IsStarProjection (Θ K))(h:IsStarProjection (Θ L))(t:K=L):P0 K p=P0 L h:=by subst K; rfl
 exact congrArg (fun v:Phys Tq=> (Δ^Fintype.card M.park.Free) • Complex.exp (C.betaL F (M.V,Q)-C.v+R.v) • v) (hv.trans (hK W λw hh wr ht))
lemma shone (p: Org (BranchX S X k) (U.blazon x l))(H:∀ A:Stores S,A.flags=flags (temp x) M.V → U.Aphro (α:=α) (H₁:=H₁) (s:=s) (v:=v) (j':=j') x l J W₀ T I P' C Q Ω δ' Z' Fx F q D' A)(wr:IsStarProjection (Θ λw)):
 (∑ A:Stores S with A.flags= flags (temp x) M.V,U.boarding x l J P' Q A v H₁ F Fx q D')=
 (Δ^Fintype.card M.park.Free) • Complex.exp (C.betaL F (M.V,Q)-C.v+R.v) • Z' • acts ((nursery _ wr).eval ((hGas (flags (temp x) M.V) (fun i=> mintF (U.blazon x l) (beamH i.val))).val)) (nest P' C.J.P μ λw):=by
 rw [turn_r U x l p,map_sum,act_sum, smul_sum, smul_sum, smul_sum]; -- careful smul_sum rewrites all! RHS
 apply sum_congr rfl; intro i v; exact aphro_a U x l J W₀ T I P' C Q B' Ω δ' Z' (H i (mem_filter.mp v).2) (mem_filter.mp v).2 wr
end Dress
end YM.CF.Eire
#print axioms YM.CF.Eire.Dress.cogent
#print axioms YM.CF.Eire.Dress.shone
