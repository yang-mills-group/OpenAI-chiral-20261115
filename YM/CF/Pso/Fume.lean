import YM.CF.Pso.Spake
import YM.CF.Ione.Pose
import YM.CF.Ione.Lean
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
local notation "B'"=> P.B
local notation "P'"=> (P.supportExponent+1+1)
variable {γ e q α γ' b₁:ℝ}{K':Cusp n}{L:blazeK n}{Q:Aura n→ℝ} (Wp:Wisp P F E h γ c d) (T:ArmsK P K L h)(R:RegBudget n)(u:∀ V:Orbit n,FleetS P.threshold V.1→exponentL P R V.1+fuelV P K' V=coldE P E V)(η0:1≤h)
variable(hU:Sym_P (numbD R))(hk: Mono_W K')(hp:Sym_a F)(ht: ZealQ K)(pc:Sym_a E)
variable(hQ:Anuk K' Q P h)(KB:∀ i:Seat n,tallB Q P.B (P.supportExponent+1+1) i ≤ α)(KK:∀ i:Seat n,tallB (Vow.hymn L) P.B (P.supportExponent+1+1+1) i ≤ b₁)
local notation "Lr"=> (P.supportExponent+1+1)
abbrev vault_Z(y:Cipher n):ℝ:= (crumb y.val ∅).re
lemma lift_E(Z Y:Cipher n): vault_Z (Z+Y)=vault_Z Z + vault_Z Y:=rfl
lemma lift'_E(Z Y:Cipher n): vault_Z (Z-Y)=vault_Z Z - vault_Z Y:=rfl
lemma tintKz(v:ℝ): vault_Z (thim n v)=v:=by change Complex.re ((v • (1:FC (Dwell n))) ∅ ∅)=_; simp
private lemma pay_k(Y:Cipher n):‖vault_Z Y‖≤ ‖Y‖:=by
 refine (Complex.abs_re_le_norm _).trans ?_; exact (YM.CF.norm_entry _ _ _) -- l2
abbrev curr_r (Vq:Orbit n): Aura n→ℝ:= Mat_R fun i=> vault_Z (FeeD P F i Vq - E i Vq)
abbrev curr_X (Vq:Orbit n):Pax n:= fun i=> zenS P i.val ∅ ((FeeD P F i-E i)-cashV (curr_r P E F Vq) i)
local notation "U1"=> curr_r P E F
local notation "Eτ"=> curr_X P E F
structure FoamZ (V0:Orbit n)(b c d:ℝ):Prop where
 shape: ∃ A C L:Aura n→ℝ, Ready Palot.stern P.B A (P.supportExponent+1+1) b 1 (degreePrice P.B b 1)∧(∀ i,Medal P i.val ∅ (F i) h (A i))∧(∀ i, Medal P i.val ∅ (cashV (curr_r P E F V0) i) h (L i))∧(∀ i,Medal P i.val ∅ (curr_X P E F V0 i) h (C i))∧(∀ o:Seat n,tallB L P.B (P.supportExponent+1+1) o≤c)∧(∀ o:Seat n,tallB C P.B (P.supportExponent+1+1) o≤d)∧(∀ (i:Aura n)(v:Orbit n),visible P i.val ∅ v.1→ FeeD P F i v=cashV (curr_r P E F V0) i v + E i v + curr_X P E F V0 i v)∧Turf (curr_X P E F V0)∧ Sym_a (curr_X P E F V0)
include Wp η0 hp pc
-- Costs 3d→L and C 6d. use Mat_R hereditary
lemma foam (Vq:Orbit n)(g: Vq.1=1): FoamZ (h:=h) P E F Vq γ (c+3*d) (6*d):=by
 obtain ⟨Y,W,LL,C,A,u,S',he,p,hQ,hA,vy,vX,uK,hW⟩:= (achieve_T P E F Wp η0 hp pc).keep
 let ζ(i):= vault_Z (FeeD P F i Vq - E i Vq); let R:= Mat_R ζ; let S:=R-Y; let Z:=Mat_R C
 have hp0(i:Aura n):pingS P.threshold (i.val\∅) Vq.1:=by rw [sdiff_empty,g]; exact ping_f P _
 have hk (i):‖ζ i-Y i‖ ≤ C i:=by
    unfold ζ; rw [uK _ _ (hates (hp0 i)),add_right_comm (cashV Y i Vq),add_sub_cancel_right,lift_E, show vault_Z _=Y i from tintKz ..,add_sub_cancel_left]; exact (pay_k ..).trans ((hA _).capF η0 Vq (hp0 i))
 have hv(i:Aura n):‖S i‖≤ Z i:=by
    unfold S R Z Mat_R; simp only [Pi.smul_apply, Pi.sub_apply,Finset.sum_apply]; nth_rw 1 [←oath_r n (Y i)] -- orientation
    rw [← smul_sub, norm_smul,←sum_sub_distrib]; have hp:0 ≤ plight_C n:=(envy n).le; rw [Real.norm_of_nonneg hp]; refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le ..) (sum_le_sum (fun j _=>?_))) hp
    have he:= hk (moldA j i); rw [u _ _] at he; exact he
 have hg(i:Aura n): ((Eτ) Vq) i= zenS P i.val ∅ (W i+ cashV (-S) i):=by
    funext V; unfold curr_X zenS; split_ifs with h
    · dsimp only [Pi.add_apply,Pi.sub_apply]; rw [uK _ _ h, add_right_comm (cashV Y i V),add_sub_cancel_right]; unfold cashV Lilt.thim S; simp only [Pi.neg_apply,Pi.sub_apply, neg_sub,sub_smul]; abel -- Rp unsym
    rfl
 have hc(X:Aura n)(u:Aura n→ℝ): Medal P X.val ∅ (cashV u X) h (‖u X‖):= ((Medal.oneT).rum _).big (by rw [mul_one]) -- defeq tune
 have hh(i:Aura n): Medal P i.val ∅ (cashV S i) h (Z i):=(hc i _).big (hv i)
 refine ⟨⟨A,C+Z,LL+Z,he,p,?_,?_,fun i=>?_,fun i=>?_,?_,?_,?_⟩⟩
 · intro i; have ht: cashV R i=cashV Y i+cashV S i:=funext (fun j=>by nth_rw 1 [cashV, show R i=Y i+S i from (by unfold S; rw [Pi.sub_apply]; abel),Lilt.thim, add_smul]; rfl); change Medal P _ _ (cashV R i) _ _; rw [ht]; exact (hQ i).plus (hh i)
 · intro i; rw [hg]; apply zen_B; exact (hA i).plus ((hc i _).big ((norm_neg ..).le.trans (hv _)))
 · rw [tall_add]; exact add_le_add (vy i) (labourV C _ _ vX i)
 · rw [tall_add]; exact (add_le_add (vX i) (labourV C _ _ vX i)).trans_eq (by ring)
 · intro i v t; rw [curr_X,zenS,if_pos t]; simp only [Pi.sub_apply]; abel
 · intro i V q; rw [hg]; unfold zenS; split; next p=>change W i _+_= _ ; rw [Pi.add_apply]; exact congrArg (·+_ ) (hW i V q)
   next p=>rfl
 intro s i v; by_cases h0:visible P i.val ∅ v.1; swap; · rw [show (Eτ) Vq i v=_ from (if_neg h0 : zenS _ _ _ _ _=0),map_zero]; exact if_neg (mt (yarnV (P:=P) s v i 0).mpr h0)
 rw [hg,hg,zenS,if_pos ((yarnV (P:=P) s v i 0).mp h0),zenS,if_pos h0,Pi.add_apply,Pi.add_apply,map_add,S']; congr 1
 unfold S cashV R Lilt.thim; rw [Pi.neg_apply,Pi.sub_apply,tally_F,u]; simp_rw [Pi.neg_apply,Pi.sub_apply,map_smul,map_one] -- tune
end YM.CF.Ione
