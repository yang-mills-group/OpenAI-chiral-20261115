import YM.CF.Ups.Block
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
variable(X:Month x a i p N0 V W) (H:MeterQ V a p i N0 J q h R0 δ x X)
open Graph
local notation "Mo"=> oYY V N0 J x
local notation "Zo" j:max=>cell Mo B R.L j
variable {ℓ:ℝ}(hp:1≤h)(ht:0 <ℓ)(hx:0 < x)
open Pyx Girt
local notation "hatQ"=> hat R.L x
variable (L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ x l)(R':Cape (oYY V N0 J x) B R.L)(Q:CoilPS V a p i N0 J q h R0 δ X L0 R')
variable {β:ℕ→ℝ}{A:ℕ→Haro.SpaceM}{F:∀ i,InkPS (cell (oYY V N0 J x) B R.L i)}{u:ℕ→ℕ}
local notation "Eρ"=> ν_P V a p i N0 J q h R0 δ L0 R'
variable (dF:ΦS_P V a p i N0 J q h R0 δ L0 R' β A F u)(hpF:K.top.clip.direct ≤1)
section
-- compare coupling shifts along ACTUAL normalized projective limit path (not exact one-loop asymptotic)
abbrev psK(L:Side):ℝ:= (11*50/(24*Real.pi^2) - 60/(12*Real.pi^2))*Real.log L.val
lemma woods(R:Patch) : Vale.net R.L= psK R.L:=by unfold Vale.net psK Vale.billX Vale.billC Gauge.slopeConstant spiceM; rw [Thera.hut_k]; ring
end
include dF
lemma spar_k (j l:ℕ): |β (j+l)-β j-(l:ℝ)*psK R.L|≤ l*K.top.drift+W.z+∑ i∈range l,δ (hat R.L x (j+i)):=by
 apply le_of_tendsto (f:=fun i:ℕ=> |((L0 (u i)).E (j+l)).beta - ((L0 (u i)).E j).beta - (l:ℝ)*psK R.L|) (((dF.lampB (j+l)).sub (dF.lampB j)).sub_const _ |>.abs)
 filter_upwards [dF.hz.tendsto_atTop.eventually (eventually_ge_atTop (j+l))] with i t
 let M:= L0 (u i); let A:=M.scale; let he:=W.arm (M.val.large.trans M.tip) (u i); have hr: Gold.Last.Running he M.main:=by intro d p; rw [A.day.fee d p]; change |M.main _ + he.move _-(M.main _+he.move _)|≤1; simp
 have hβ:= Vale.spark hr (W.pose _ _) j l t; rw [woods R] at hβ -- tune
 let f(i):=(M.E i).beta - M.main i; have ht : ∀ k,k≤l→ |f (j+k)-f j| ≤∑ x'∈range k, δ (hat R.L x (j+x')):=by intro k p; induction k with
    | zero=>simp
    | succ k ih=>
       have h := A.note.shift (j+k) (by omega); have hv: |f (j+k+1)-f (j+k)|≤δ (hat R.L x (j+k)):= h ▸ A.note.price (j+k) (by omega)
       rw [sum_range_succ,Nat.add_succ, ←sub_add_sub_cancel (f (j+k+1)) (f (j+k))]; exact (abs_add_le ..).trans ((add_le_add hv (ih (by omega))).trans (add_comm .. |>.le))
 change |(M.E _).beta - _ - _| ≤ _; rw [show (M.E _).beta - _ - _= (M.main (j+l)-M.main j-(l:ℝ)*psK R.L)+(f (j+l)-f j) from ?_]; exact (abs_add_le ..).trans (add_le_add hβ (ht l le_rfl)); unfold f; ring
lemma vicinity (hV:Chill_v δ) :∀ ε:ℝ,0<ε→∀ᶠ j:ℕ in atTop,∀ l:ℕ, |β (j+l)-β j-(l:ℝ)*psK R.L|≤ l*(K.top.drift+ε)+W.z:=by
 intro ε v; let z:= hat R.L x; have hz:=billx_T V; have hu:0<Vale.billX R.L:= by unfold ν_PS at hz; linarith
 have he:Tendsto z atTop atTop:= tendsto_atTop_add_const_left atTop _ (tendsto_natCast_atTop_atTop.atTop_mul_const hu); obtain ⟨j,hz⟩:= eventually_atTop.mp ((hV.spine_a.comp he).eventually (ge_mem_nhds v))
 filter_upwards [eventually_ge_atTop j] with y p'; intro k; have hG: (∑ i∈range k,δ (hat R.L x (y+i)))≤ k* ε:= (sum_le_sum (g:=fun _=> ε) (fun i _=>hz (y+i) (by omega))).trans_eq (by simp)
 refine (spar_k V a p i N0 J q h R0 δ L0 R' dF y k).trans ?_; nlinarith
end YM.CF.Py
