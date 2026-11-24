import GaugeFieldConstruction.Norwood
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option synthInstance.maxSize 24000
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
local instance localeTwitterT (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance localeTwitterB (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
open Fock.Flux Girt
local notation "Xq" s:max => hat P.R.L P.x s
variable {J:Type*} [DecidableEq J]
open Guide Fock.Flux
lemma onpage_d (q: Finset J)(S:J→ Support (More N))(p:Set.PairwiseDisjoint ↑q S): Set.PairwiseDisjoint ↑q (fun i=> onPage N (S i)):=fun _ x _ y k=> Finset.disjoint_left.mpr (fun i h1 h2=> Finset.disjoint_left.mp (p x y k) (mem_filter.mp h1|>.2) (mem_filter.mp h2|>.2))
lemma court_sep (q:Finset J)(S:J→Support (More N))(p:Set.PairwiseDisjoint ↑q S)(i:Signed): Set.PairwiseDisjoint ↑q (fun j=>(S j).image (affine i⁻¹ 0)):=by
 intro j v k y l; apply disjoint_left.mpr; intro x p' h; obtain ⟨u,e,rfl⟩:= mem_image.mp p'; obtain ⟨a,w,Q⟩:= mem_image.mp h; have hc:a=u:= i⁻¹.act_injective (add_right_cancel Q); exact disjoint_left.mp (p v y l) e (hc ▸ w)
set_option maxHeartbeats 70000 in
lemma hour_now (s i k:ℕ)(u:s≤Y.uv k)(E:List J)(C W:J→ℂ)(F:J→Pane (count Y s i)→ FC (Single (count Y s i))) (S:J→Support (More (count Y s i)))
 {z K v A D u₀ x:ℝ}{m:ℕ}(g:∀ j∈E, Upright (count Y s i) (S j) v m (F j)) (he:Set.PairwiseDisjoint ↑E.toFinset S) (pK:1≤K)(p:D≤ K)(e:E.Nodup)(t:0<x)(v₀:0≤v)(vK:∀ i∈E,‖W i‖≤u₀)(uP:0≤u₀)(uz:0≤z)(zP:∀ i∈E,‖C i‖≤z)(iA:0≤A)
 (pT:Kea.Pad P.K.j (count Y s i))(bw:Crest u₀ v z K m ≤ 1/2) (j:Signed)(T: Oak Y s i)(X:Orbit (count Y s i))
 (χ:∀ b:ℝ,b∈Set.Icc 0 1→ let U:= tradew (count Y s i) (Loose j T.T X.1); let G:= gram Y s i k; let M:=G.J.M; let N:=count Y s i; let Z:=boardC N P.K.j M; PurchB A D b (oneWarp Z (pinShift N P.K.j M) U b)∧ PurchB A D b (star (onePeak Z (pinBack N P.K.j M) U b)))
 (d:ℝ)(iY: ‖acts (offWall Y s i k (Loose j T.T X.1) 1) (Graph.recX P.U (gram Y s i k) (room Y s i) X)‖ ≤ d):
 let f:= ShootF E C W F
 let Q:= tailored T.T (pull j 0 X.1)
 ‖PryF Y s i k f X‖ ≤ ØCost Y s i k * (Real.exp ((∑ l∈E.toFinset,(C l*(MapΘ Y s i k j (F l) Q - W l)).re)+ Tor x A K z v m E.length + 2*(Crest u₀ v z K m)^2*E.length)*d):=by
 intro f Q; let Ω:=ØFlat Y s i k; let H:= gram Y s i k; let P':=boardC (count Y s i) P.K.j H.J.M; let Z:= Graph.recX P.U H (room Y s i) X; let G:= Loose j T.T X.1; let U:= tradew _ G
 let R:= offWall Y s i k G 0; let R':= offSeek Y s i k G 0; let V:= acts R Z; let Y':= translateW P' (pinShift (count Y s i) P.K.j H.J.M) (pinBack (count Y s i) P.K.j H.J.M) U 0 -- tune
 have h₀:= token_V pT (by rw [P.kJ]; decide) H.J.M; have hp:= baseP pT H.J.M
 let U':= f X.1; let A':= fun j:J=> F j X.1; have he' := mantle U C W E A' (fun i=>onPage _ (S i)) hp h₀ Ω (actual_f Y ..) e (onpage_d E.toFinset S he) (fun i v=>zP i v) uz (fun i p=> (g _ p).holds X.1) v₀ (e:=x) t iA pK p χ bw vK uP V -- order verify
 obtain ⟨c,v,h⟩:= cosmos Y pT G
 let J':= Y' U'; let N:= count Y s i; let T':= PryF Y s i k f X; let y:= mateK N
 have ht: T'=inner ℂ (c • Ω) (acts J' V):=by
    rw [show c • Ω=acts (star R') y from (h 0).symm, act_inner]
    have hp: acts R' (acts J' V) = acts U' Z:=by
       have hh: acts J' V= acts R (acts U' Z):= (act_char h₀ hp 0 U U' Z).symm
       rw [hh, ←act_mul,show R'*R=1 from couple_wall h₀ hp U 0,act_one]
    rw [hp]
 let Φ(l:J):= (C l*(MapΘ Y s i k j (F l) Q-W l)).re
 have hz:(∑ l∈E.toFinset,(C l*(quotation Ω (Y' (A' l))- W l)).re)=∑ l∈E.toFinset,Φ l:=sum_congr rfl (fun l w=>by unfold Φ; rw [show MapΘ _ _ _ _ _ _ _= _ from F_shot Y s i k pT j T (g l (List.mem_toFinset.mp w)) X.1])
 rw [show PryF Y s i k f X=_ from ht]; apply (norm_inner_le_norm ..).trans; rw [norm_smul,v,(actual_f Y s i k).2,mul_one, ← hz];
 have hh:acts (knight P' 1) V= acts (offWall Y s i k G 1) Z:=by
    unfold V; rw [←act_mul]; refine congrArg (fun f=> acts f Z) ?_; unfold R offWall; dsimp only; unfold wall; rw [knight_start,one_mul]; simp only [mul_assoc]; rfl
 exact mul_le_mul_of_nonneg_left (he'.trans (mul_le_mul_of_nonneg_left (hh ▸ iY) (Real.exp_pos _).le)) (norm_nonneg _)
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
