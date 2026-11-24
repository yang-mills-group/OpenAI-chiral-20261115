import YM.SU5.Fineness.Frank
import YM.SU5.FiniteGaugeData.Pannier.PerRoot

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
/-! # Link normalizer and sharp rooted cable widths. -/
namespace Fineness
open Pannier YM.Fineness
open YM.SectorNext.Vacuum (narrow linkZ narrow_pos mouth first_asymptotic)
variable {G:Gauge}(J':ChartRatio G)(p:LocalRatio J')(ε:ℝ)
set_option linter.unusedVariables false
local notation "r'"=> Fintype.card G.ColorIndex
local notation "d'"=> halfLie G
include p
lemma lens_fare(g:KernelChoices) (s:ε>0) : ∀ᶠ b:ℝ in atTop,∀ {m n:Side}(S:StepData m n), S.kernel=g →
 |Real.log (S.penaltyZ b G)-Real.log (spare J' b)+halfLie G *Real.log g.penalty|≤ ε:=by
 let t:=g.penalty; have u:=g.penalty_pos
 let v:=narrow J' t; have ht:=narrow_pos J' p _ u
 have he:Real.log v=logFlat J' - d'*Real.log g.penalty:=by
    have hp : (Real.pi / (t/2))>0:= div_pos Real.pi_pos (half_pos u)
    rw [show v=J'.scale * (Real.pi / (t/2)) ^ d' from rfl, Real.log_mul p.scale.ne' (Real.rpow_pos_of_pos hp _).ne',Real.log_rpow hp]
    rw [show Real.pi/(t/2)= (2*Real.pi)/g.penalty from by unfold t; ring,Real.log_div (mul_pos (by norm_num) Real.pi_pos).ne' u.ne', shadowLie]; unfold logFlat; ring
 let f (x:ℝ):= x^(Module.finrank ℝ G.Color)*linkZ G (g.penalty*x^2)
 have hf:Tendsto (fun x=>|Real.log (f x)-Real.log v|) atTop (𝓝 0):=by simpa only [v,t,sub_self,abs_zero] using (((first_asymptotic J' p _ u).log ht.ne').sub_const (Real.log v)).abs
 filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_sqrt_atTop.eventually (hf.eventually (ge_mem_nhds s))] with b h k
 intro m n S hS
 let a:=Real.sqrt b
 have h0: 0<a:= Real.sqrt_pos.mpr h
 have heq : S.penaltyZ b G = linkZ G (g.penalty*b) := by
   unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth
   rw [hS]; congr 1; ext x; ring_nf
 rw [← Real.sq_sqrt h.le] at heq
 change |Real.log (a^ (Module.finrank ℝ G.Color)*linkZ G (g.penalty*a^2))-Real.log v|≤ε at k
 rw [show linkZ G (g.penalty*a^2)= S.penaltyZ b G from ?_,Real.log_mul (by positivity : a^ (Module.finrank ℝ G.Color)≠0) (S.penaltyZ_pos ..).ne', Real.log_pow,show Real.log a=_ from Real.log_sqrt h.le, he] at k
 · rw [spare_formula _ p.scale h,← shadowLie]; apply le_trans (le_of_eq _) k; unfold halfLie; ring_nf
 exact heq.symm.trans (by rw [Real.sq_sqrt h.le])
omit p
open scoped ENNReal
lemma arc_guard (G:Gauge): Tendsto (Appel.point G) atTop (𝓝 1):=by
 let M:= rice G; let B (x:ℝ):=closedBall (0:G.Color) x;
 have ht : Tendsto (fun x:ℝ=> M (B x)) atTop (𝓝 (M (⋃ x,B x))):=tendsto_measure_iUnion_atTop (fun _ _ h=>closedBall_subset_closedBall h)
 have hp: (⋃ x,B x)=Set.univ:= Set.eq_univ_of_forall fun x=>Set.mem_iUnion.mpr ⟨dist x 0,mem_closedBall.mpr le_rfl⟩
 rw [hp,show M Set.univ=1 from measure_univ] at ht; exact (show (1:ℝ≥0∞).toReal=(1:ℝ) from by simp) ▸ (ENNReal.tendsto_toReal (by simp)).comp ht
lemma lens_flurries(J':ChartRatio SU.group)(p':LocalRatio J')(i:ℝ)(s:i>0):∀ᶠ y:ℝ in atTop, ∀ b> (0:ℝ), |Real.log (shotM J' y b)-Real.log (spare J' b)| ≤ i:=by
 have hp:= ((arc_guard SU.group).log (one_ne_zero)).abs; have ht: abs (Real.log 1)< i:= by simpa using s
 filter_upwards [eventually_gt_atTop (0:ℝ),hp.eventually (ge_mem_nhds ht)] with y h ht b q
 unfold shotM; rw [Real.log_mul (spare_pos J' p' q).ne' (Appel.point_p h|>.ne'),add_sub_cancel_left]; exact ht
variable (Kv:Teller SU.group)(b α:ℝ)
local notation "G5"=> SU.group
local notation "u'"=> halfLie G5
local notation "d5"=> Fintype.card SU.group.ColorIndex
local notation "ℓM" N:max=> (Fintype.card (Site N):ℝ)
abbrev gaugedBase (L:ChartRatio SU.group) (β:ℝ) (n:Side)(H:Bed):ℝ:= 3*(ℓM n-1)*Real.log (spare L β) - halfLie SU.group * Real.log (leasePart (H.metric.acts n))
variable (S:StepData m n)(M: Forge.Monk SU.group S)(H Q:Bed){x:ℝ}(Gx: Tube SU.group S){δ η uₚ:ℝ}
lemma gold_floor (G:Gauge)(n:Side)(p:Clip)(H:Bed)(a b:ℝ)(h:Floor H p n a b)(z:0<a): (H.metric.acts n).PosDef:= qpos z h.symmetric.1 ⟨fun y=>(h.uniform.1 y).1⟩
local notation "Tt"=> FreeResolvent.Affine.headGap G5 R K.bind K.top.clip
local notation "M'" i:max H:max=> H.metric.acts i
local notation "Gf"=> H.metric.acts n
open Exterior Next.Fluctuations.Sector
local notation "Γ'"=> Corne.arcD Gx x M
lemma strands (A':YM.Fineness.Tab (Body 1 n) (Body 1 m))(v0:0< ε)
 
 (p:Floor H K.top.clip n η δ)(q:Attached H Gx.up)(e:Bid.Sworn H n G5)(ηP:0<η)(u:Newt.Cert R K S Gx x)
 (P':Floor Q K.top.clip m η uₚ)(y:Inputs S A' (H.metric.acts n) (Q.metric.acts m))(z:LocalRatio L)
 (a b:ℝ)(t0:0<b)(t1:0<a) (s0:|Real.log (S.penaltyZ b G5)-Real.log (spare L b)+u'*Real.log S.kernel.penalty|≤ ε) (s1:|Real.log (shotM L a b)-Real.log (spare L b)| ≤ ε) (s2:|Γ'+ (1/2:ℝ)*Real.log (FreeResolvent.treeMatrix G5 S M.park H.metric).det| ≤ ε*ℓM n) :
 |Real.log (prefactor S G5 b * (shotM L a b)^Fintype.card M.park.Free)+Γ'-(gaugedBase L b n H-gaugedBase L b m Q-8*(u')*Real.log S.patch.L.val)|≤10*ε*ℓM n:=by
 have ht:= (shotP L z t1 t0);  have hp:= p; have hx:= lattice_pos (gold_floor G5 n K.top.clip H η δ p ηP); have hz:=lattice_pos (gold_floor G5 m _ Q _ _ P' ηP)
 have hK:=S.kernel.penalty_pos; have he:= rpos S; let C:= Real.log (FreeResolvent.treeMatrix G5 S M.park H.metric).det; let A:= inBoard S M.park (H.metric.acts n)
 let N:= ℓM m; let F:= ℓM n; let D:= Real.log (spare L b); let v:= u'; let LF:=Real.log (leasePart Gf); let LC:=Real.log (leasePart (Q.metric.acts m)); let l:=Real.log S.patch.L.val; let K':=Real.log S.kernel.penalty
 have hQ:C=2*u'*(LF-LC+8*l+4*N*K'):=by
    unfold C; rw [tree_det,Real.log_pow]; cases isEmpty_or_nonempty SU.group.ColorIndex with
    | inl hP=> rw [shadowLie,Fintype.card_eq_zero,Nat.cast_zero]; ring
    | inr hP=>
       let hB:= scalar_gap S M.park G5 H.metric (g_prec S M Gx H u p q e); let hv:= qpos (FreeResolvent.Affine.headGap_pos G5 R K.bind K.top.clip) (board_symm S M.park _ p.symmetric.1) hB
       have he':= congrArg Real.log (hinges S M.park A' _ _ y p.symmetric.1 P'.symmetric.1 hv.isUnit ); have hu : (S.patch.L.val:ℝ)^8>0:= pow_pos he _
       rw [Real.log_mul (mul_pos hu hx).ne' (pow_ne_zero _ hK.ne'), Real.log_mul hu.ne' hx.ne', Real.log_mul hv.det_pos.ne' hz.ne',Real.log_pow, Real.log_pow,bond_count] at he'; push_cast at he';
       rw [shadowLie]; change (d5:ℝ)* Real.log A.det=2*((d5:ℝ)/2)*_; rw [show Real.log A.det=LF-LC+8*l+4*N*K' from ?_]; ring; -- tune
       unfold A LF LC l N K'; linarith only [he']
 unfold prefactor; rw [Real.log_mul (pow_pos (inv_pos.mpr (S.penaltyZ_pos ..)) _).ne' (pow_pos ht _).ne', Real.log_pow, Real.log_pow,Real.log_inv,thinWireCount,show Fintype.card (Edge (Site m))= Fintype.card (Site m)*4 from (Fintype.card_prod ..).trans (by rfl)]; push_cast
 have hn:0≤N:=by unfold N; positivity
 have he:N ≤ F:= Jade.Earn.builtLe S
 have hz:0≤3*F+N:=by linarith only [hn,he]
 rw [abs_le] at s0 s1 s2; change _ ≤ _ +(1/2:ℝ)* C ∧ _+(1/2:ℝ)*C ≤ _ at s2
 let Z:= Real.log (S.penaltyZ b G5); let W':=Real.log (shotM L a b)
 change |N*4*(-Z)+(3*F+N)*W'+ Γ' -((3*(F-1)*D-v*LF)-(3*(N-1)*D-v* LC)-8*v*l)| ≤ 10*ε*F; rw [abs_le]; change - ε≤ Z-D+v*K' ∧ Z-D+v*K' ≤ ε at s0; change -ε ≤ W'-D ∧ W'-D ≤ε at s1; change C=2*v*(LF-LC+8*l+4*N*K') at hQ; rw [hQ] at s2; change -(ε*F)≤ _ ∧ _ ≤ ε*F at s2
 constructor <;> nlinarith only [mul_le_mul_of_nonneg_left s0.1 hn,mul_le_mul_of_nonneg_left s0.2 hn,mul_le_mul_of_nonneg_left s1.1 hz,mul_le_mul_of_nonneg_left s1.2 hz,s2.1,s2.2,mul_le_mul_of_nonneg_right he v0.le,mul_nonneg hn v0.le] -- shadow v
where
 shotP (L:ChartRatio SU.group)(z:LocalRatio L){u b:ℝ}(hv:0<u)(hx:0<b): 0<shotM L u b:= mul_pos (spare_pos L z hx) (point_p hv)
end Fineness
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Fineness.strands
