import YM.CF.Yaw.Seal
import YM.CF.Rue.Ore
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees PetalP
variable {I N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B)){r d k l D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
local notation "m"=> mid P B
local notation "V'"=> Domain P B
local notation "H_"=> Eire.Ride S
local notation "S_"=> Eire.Folk S r ι
local notation "τ"=> Oboe (Single (mid P B))
local notation "χ"=> (LeanV (Single (mid P B)))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable{S G}
variable (L:List (Kite S r))(U:List (Rust (mid P B)))(W:List ι)
local notation "Z'"=> weave_g L U W
open Eire Dress
variable {e A Q:ℝ}(R:GramM (mid P B))(M:E→Monk SU.group S)(T: ∀ i:E, Dress G S e r D (M i) R k X)
variable (eK:ℕ)(Q':Hos S r→ Sweep (mid P B))(G_u: ∀ O:Hos S r, Support (Domain P B) →ℝ)
variable (P': Tints P B e)(Gm:∀ i:Support (Domain P B), Lend P B e i)(U':Ids (mid P B))
variable (HX:TailB→Support (Domain P B)→Toll (Iota G))(HY:Grave→Support (Domain P B)→Toll (Iota G))
local notation "Z₁"=> (Z').toFinset
open Eire.Dress
variable (x:ℝ)(l:ℕ)(A:Eire.Ride S)
lemma spout(i:E)(b:Hos S r)(c:b∈liftK S L.toFinset)(p: (T i).blazon x l (weave_g L U W).toFinset A≠0): (T i).rare (penn S (weave_g L U W).toFinset) b≠0:=by
 unfold Eire.Dress.blazon at p; split at p; swap; contradiction
 next u =>
    let Z:= (T i).stageT x l (weave_g L U W).toFinset; let F:= Scion.vig Z; intro b'; have hp:(T i).brew (weave_g L U W).toFinset=0:=by unfold brew; dsimp only; rw [prod_eq_zero _ b',zero_mul]; rw [left_i]; exact c
    have hv:F=0:=by
      funext y; apply Subtype.ext; change Scion.tempo Z y=(0:Cipher (mid N B)).val; unfold Scion.tempo; split
      · rw [show Z.diet y=_ from rfl, show Z.diet y=0 from ?_,mul_zero]; rfl -- tune
        exact congrArg Subtype.val hp
      rfl
    apply p; change reconL.symm F A=0; rw [hv,map_zero]; rfl
section strict
variable (t':Support (Domain N B))(i:E)(u:t'⊆Stilo.bay A)
include u
lemma flare_w (k:(M i).V∈Rue.litres (temp x) (bay A) t') : flags (temp x) (M i).V∩bay A=t':=by
 obtain ⟨p,t⟩:=k; apply subset_antisymm _ (subset_inter t u); intro i v; by_contra h; exact disjoint_left.mp (Scree.ping_le p) (mem_sdiff.mpr ⟨(mem_inter.mp v).2,h⟩) (mem_inter.mp v).1
lemma stamp_w(z:E)(kw:∀ᶠ i in 𝓝 z,(M i).V∈Rue.litres (temp x) (bay A) t')(v:∀ᶠ u in 𝓝 z,chillB (M u)=chillB (M z))(p:z ∈ tsupport (fun i:E=> (T i).blazon x l (weave_g L U W).toFinset A)): (∀ᶠ i in 𝓝 z, capG S (flags (temp x) (M i).V) (chillB (M i)) R.p.threshold (weave_g L U W).toFinset A) ∧ Palot.fits (BranchX S X k) (weave_g L U W).toFinset A:=by
 obtain ⟨i,⟨h',l'⟩,r'⟩:=mem_closure_iff_nhds.mp p _ (kw.and v); have hx:(T i).blazon x l (weave_g L U W).toFinset A ≠0:= r'; unfold Eire.Dress.blazon at hx; split at hx; swap; contradiction
 next g=> refine ⟨?_ ,fuelFit _ _ hx⟩; obtain ⟨t,x',c⟩:= g; filter_upwards [kw,v] with q hp h; exact ⟨t,(Eq.trans l' h.symm) ▸ x',(Eq.trans (flare_w M x A t' q u hp) (flare_w M x A t' i u h').symm).trans c⟩
end strict
end YM.CF.Yaw
