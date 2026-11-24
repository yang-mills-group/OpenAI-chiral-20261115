import YM.CF.Feu.Views
import YM.CF.Haro.Cubit
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
section
variable (p q: Single (mid P B))(R:GramM (mid P B))
abbrev gateY {f:Side}(p q:Single f): FC (LeanV (Single f)):= put (true,p)*put (false,q)
abbrev handY {f:Side}(p q:Single f):= parity ((true,p):LeanV (Single f)) {(false,q)}
lemma cue_y : poke (Haro.tray p q) = handY p q • gateY p q:=by
 unfold poke Haro.tray; rw [Poly.tag_any,Poly.tag_once]; rfl; simp
lemma peru(Y:Cipher (mid P B)): Pastry.crumb Y.val (Haro.tray p q) • poke (Haro.tray p q)=Haro.orbitPH Y p q • gateY p q:=by
 rw [cue_y]; unfold Haro.orbitPH; rw [Matrix.of_apply, Prism.port_eq,if_neg, smul_smul]; rw [mul_comm]; simp
abbrev hue_I (X:Support (Domain P B)):= univ.filter fun p:Prism.Rock κ=> Cube.node p.1∈ X
variable (X:Support (Domain P B))(a0 b0:SU.Slot)(P1 P2:Rock (mid P B))
lemma fellow : Haro.tray (P1,a0) (P2,b0) ∈ Feu.Corset.perm_p (Wheat (camp X)) ↔ P1∈ hue_I X ∧ P2∈ hue_I X :=by
 have h(P:Prism.Rock κ)(b a): ((b,(P,a)): Fm)∈camp X ↔P∈ hue_I X:=by rw [camp,hue_I]; simp
 have he:(Haro.tray (P1,a0) (P2,b0)).card=2:=by simp [Haro.tray]
 unfold perm_p Wheat; rw [mem_filter,he,mem_filter,he]; simp only [mem_powerset,even_two,and_true] -- tune
 rw [Haro.tray,insert_subset_iff,singleton_subset_iff,h,h]
-- eliminate same charge using gauge center
lemma pure_G (W:InkD κ)(x:Scree.Hub κ)(T:Pane κ)(B_:BudgetPoint)(hp:PressB B_ x W d e)(Q:Finset (Dwell κ))(h:Q.card=2)(v:crumb (W T).val Q≠0): ∃ i j,Q=Haro.tray i j:=by
 obtain ⟨⟨a,i⟩,⟨b,j⟩,he,h⟩:=card_eq_two.mp h; subst Q
 have hv:a≠b:=by
    rintro rfl; let x:Rock κ:= i.1; let y:Rock κ:=j.1; have ht:=Prism.twice0 hp T x y a
    have hh:Prism.portB (W T).val (a,i) (a,j)=0:= Matrix.ext_iff.mpr ht i.2 j.2
    rw [Prism.port_eq,if_neg he] at hh; exact (mul_ne_zero (by simp [parity]) v) hh
 cases a <;> cases b; contradiction; exact ⟨j,i,by unfold Haro.tray; rw [Finset.pair_comm]⟩; exact ⟨i,j,rfl⟩; contradiction
variable (O: Ride S)(Θ:Ride S→ Weave (Single (mid P B)) (Single (mid N B)))(R':Support (Domain N B))
lemma craneS (W:InkD (mid P B))(T:Pane (mid P B))(x₁:Scree.Hub (mid P B))(B_:BudgetPoint)(hp:PressB B_ x₁ W d e): Feu.Corset.lump (perm_p (Wheat (camp X))) (fun i' => Pastry.crumb (W T).val i') Θ O R'= ∑ i'∈ hue_I X,∑ j∈hue_I X, ∑ a:SU.Slot,∑ b:SU.Slot,ranks ([(true,(i',a)), (false,(j,b))]) (beamH R') (orbitPH (W T) (i',a) (j,b)) Θ O:=by
 let F:=W T; let L(i:Finset Fm):= ranks (rollP i) (beamH R') (crumb F.val i) Θ O; let g(x:Single κ×Single κ):=Haro.tray x.1 x.2
 let S':= (hue_I X)×ˢ (univ :Finset SU.Slot); let C:=S'×ˢ S'; let D:=perm_p (Wheat (camp X))
 have h(i j:Single κ) : (i,j)∈ C ↔ Haro.tray i j∈ D:=by
    have hx:= fellow X i.2 j.2 i.1 j.1; refine Iff.trans mem_product ?_; unfold S'; simp only [mem_product,mem_univ,and_true]; exact hx.symm
 change ∑ i∈D,L i=_; rw [←sum_subset (show C.image g ⊆ D from ?_)]; swap -- tune ordering
 · intro i p v; by_cases he:crumb F.val i=0; · unfold L ranks; simp [he]; exact congrFun (map_zero reconL.symm) O
   obtain ⟨a,b,rfl⟩:=pure_G W x₁ T B_ hp i (mem_filter.mp p).2 he; exact False.elim (v (mem_image.mpr ⟨(a,b),(h ..).mpr p,rfl⟩))
 swap; · intro i p; obtain ⟨c,hx,rfl⟩:=mem_image.mp p; exact (h c.1 c.2).mp hx
 rw [sum_image Haro.tray_in.injOn]; unfold C S'; rw [sum_product,sum_product]; refine sum_congr rfl fun i p=>?_ ; conv_rhs=> rw [sum_comm]
 apply sum_congr rfl; intro a _; rw [sum_product]; refine sum_congr rfl fun j p=>sum_congr rfl fun b _=>?_; apply congrArg (fun f: Track (Ride S) (FC (LeanV (Single (mid N B))))=>reconL.symm f O); funext z; split_ifs; swap; rfl
 let p:Single κ:=(i,a); let q:Single κ:=(j,b)
 have hx: gateY p q=rollC put [(true,p),(false,q)]:=by simp [gateY,rollC]
 exact congrArg (fun a=> issue (Θ z) a 1) ((peru p q F).trans (congrArg (fun v:FC (LeanV (Single (mid P B)))=> orbitPH F p q • v) hx))
end
end YM.CF.Oath
