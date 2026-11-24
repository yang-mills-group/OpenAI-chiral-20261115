import YM.CF.Chaff.Aff
import YM.CF.Pso.Fume
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
variable {γ γ' σ σ':ℝ}
abbrev Pant_k (A:Sweep n→Prop)(F:Pax n):Prop:=∀ s:Sweep n,A s→∀ i v, F (moldA s i) (yellA s v)=suit_Y s (F i v)
abbrev rim_r (Vq:Orbit n) (i:Aura n):ℝ:=vault_Z (FeeD P F i Vq)
abbrev rim_t(Vq:Orbit n):Pax n:=fun i=> zenS P i.val ∅ (FeeD P F i-cashV (rim_r P F Vq) i)
variable (Qs:Sweep n→Prop) (wQ:Wisp P F 0 h γ σ σ')(hp:1≤ h)(hf:Pant_k Qs F)
local notation "θ"=> P.supportExponent+1+1
private lemma pay_k(Y:Cipher n):‖vault_Z Y‖≤ ‖Y‖:=by
 refine (Complex.abs_re_le_norm _).trans ?_; exact (YM.CF.norm_entry _ _ _) -- l2
include wQ hp hf
lemma pay_Wr (V0:Orbit n)(bV:V0.1=1): let U:=rim_t P F V0; let UW:=rim_r P F V0
        ∃ A C L:Aura n→ℝ, Ready Palot.stern P.B A (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1)∧(∀ i,Medal P i.val ∅ (F i) h (A i))∧(∀ i, Medal P i.val ∅ (cashV UW i) h (L i))∧(∀ i,Medal P i.val ∅ (U i) h (C i))∧(∀ o:Seat n,tallB L P.B (P.supportExponent+1+1) o≤σ+σ')∧(∀ o:Seat n,tallB C P.B (P.supportExponent+1+1) o≤σ'+σ')∧(∀ (i:Aura n)(v:Orbit n),visible P i.val ∅ v.1→ FeeD P F i v=cashV UW i v + U i v)∧ Turf U∧Pant_k Qs U ∧∀ s,Qs s→∀ i,UW (moldA s i)=UW i :=by
 intro U UW; obtain ⟨G,R,L,C,A,hw,u,v,p,t,hL,hU,pM,W⟩:=wQ.keep
 have hv:= (add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 have ht:Pant_k Qs (FeeD P F):= fun s p i u'=> spinsE s i (suit_Y s) u' (fun i=>hf s p i u') u hp v hv 0 -- maybe expects all v.
 choose Y hz using hw
 have hM(i)(z:Orbit n)(q:visible P i.val ∅ z.1): FeeD P F i z=cashV Y i z+R i z:= by have h:=pM i z q; change FeeD _ _ i z= G i z+0+R i z at h; rw [add_zero,hz] at h; exact h
 have he0(i:Aura n):pingS P.threshold (i.val \ ∅) V0.1:=by rw [sdiff_empty,bV]; exact ping_f _ _
 have hΨ(s:Sweep n)(p:Qs s)(i:Aura n):UW (moldA s i)=UW i:=by
    unfold UW rim_r; let X:= moldA s i; let V:= yellA s V0
    have h':V.1=V0.1:=by change flashA s V0.1= V0.1; rw [bV,revoke]; funext i; simp [Lattice.pull, Step.read] -- StepRead
    have hq: FeeD P F X V0=FeeD P F X V:=by rw [hM X _ (hates (he0 _)),hM X V (hates (by rw [h']; exact he0 X)), W X V V0.2,h']
    change vault_Z (FeeD P F X V0)=_; rw [hq, show FeeD P F X V= _ from ht s p i V0]
    let K:= FeeD P F i V0; change (Pastry.pane (suit_Y s K)).re=(Pastry.pane K).re; rw [Chaff.matter_Re]; unfold Spire.payZ; cases Spire.wageZ s <;>rfl
 let D:= UW-Y; have hb(i):‖D i‖≤ C i:=by unfold D UW rim_r; rw [Pi.sub_apply,hM i _ (hates (he0 i)),lift_E,show vault_Z _= Y i from tintKz ..,add_sub_cancel_left]; exact (pay_k ..).trans ((t i).capF hp V0 (he0 i))
 have hg(i): U i= zenS P i.val ∅ (R i-cashV D i):=by
    funext q; unfold U rim_t zenS; split; next p=> rw [Pi.sub_apply,hM _ _ p,Pi.sub_apply]; change cashV Y i q+_-cashV UW i q= _; unfold D cashV Lilt.thim; rw [Pi.sub_apply,sub_smul]; abel
    next p=> rfl
 have hu(i): Medal P i.val ∅ (cashV D i) h (C i):= ((Vow.Medal.oneT).rum _).big (mul_one (‖D i‖)|>.trans_le (hb i))
 refine ⟨A,C+C,L+C,u,v,?_,?_,?_,?_,?_,?_,?_,hΨ⟩
 · intro i; have he:cashV UW i=G i+cashV D i:=by rw [hz]; funext z; change UW i • (1:Cipher n)= _+ D i • _; unfold D; rw [Pi.sub_apply, sub_smul]; change _= Y i • _+_; abel
   rw [he]; exact (p i).plus (hu i)
 · intro i; rw [hg]; apply zen_B; rw [sub_eq_add_neg]; exact (t i).plus ((hu i).negT)
 · intro i; rw [tall_add]; exact add_le_add (hL i) (hU i)
 · intro i; rw [tall_add]; exact add_le_add (hU i) (hU i)
 · intro i v z; unfold U rim_t zenS; rw [if_pos z,Pi.sub_apply]; exact (add_sub_cancel _ _).symm
 · intro i v Y; rw [hg]; unfold zenS; split; next p=>exact congrArg (fun x=> x- cashV D i v) (W ..)
   next p=>rfl
 intro s p i u; by_cases vS:visible P i.val ∅ u.1; swap; · rw [show U i u=0 from if_neg vS,map_zero]; exact if_neg (mt (yarnV (P:=P) s u i 0).mpr vS)
 unfold U rim_t zenS; rw [if_pos ((yarnV (P:=P) s u i 0).mp vS),if_pos vS,Pi.sub_apply, Pi.sub_apply, ht s p, map_sub]; unfold cashV Lilt.thim; rw [map_smul,map_one,show rim_r _ _ _ (moldA s i)=rim_r P F V0 i from hΨ s p i] -- tune UW
end YM.CF.Ione
