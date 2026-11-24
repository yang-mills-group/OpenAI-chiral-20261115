import YM.CF.Sour.Calm
import YM.CF.Rill.Oboe
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes Tenant

variable {N:Side}
set_option synthInstance.maxSize 20000
open Sour Vow
local notation "SS"=> More N
open Pressure
-- uniform pays kernels.Heats. threshold eta.After.L. ε arbitr.
structure HopeT (d b a:ℝ)(n:ℕ):Prop where
 warm:actB d n b
 ease:0 < b
 peta:0<a
 until':∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](F:E→L[ℝ]SU.group.Color)(U:SU.group.El),‖F‖ ≤ a→Tender (fun x=> SU.group.lieExp (F x)*U) 0 b n
lemma cozy (n:ℕ)(p:0 < d):∃ a b: ℝ,HopeT d b a n:=by
 obtain ⟨b,u,hv⟩:=opus_b n p; obtain ⟨C,k,H⟩:=funding n; obtain ⟨e,v,K,hK,J⟩:= buy _ n (duoK n (·*·) (fun F M g h=>by unfold Scope; simp_rw [Function.comp_def,Gauge.mat_mul]; exact g.mul h)) -- tune private
 have ht:0<C:= lt_of_lt_of_le zero_lt_one k; have he:0<K:= lt_of_lt_of_le zero_lt_one hK; let a:=min 1 (min (e/C) (b/K/C)); have hg:0<a:=lt_min zero_lt_one (lt_min (by positivity) (by positivity)); have hp:a ≤ 1:=min_le_left ..; refine ⟨a,b,hv,u,hg,fun E _ _ F U l=>?_⟩
 have hx:= H F 0 a (allows_linear l (by rw [map_zero,norm_zero]; exact hg.le)) hp; have hh:C*a ≤ e:=by rw [mul_comm]; exact (le_div_iff₀ ht).mp ((min_le_right ..).trans (min_le_left ..))
 have hl:= J.duty hh hx ((Shake.holds (SU.group.mat U)).bag hx.price); exact hl.bag (by rw [mul_comm K]; refine (le_div_iff₀ he).mp (show C*a ≤ b/K from ?_); rw [mul_comm]; exact (le_div_iff₀ ht).mp ((min_le_right ..).trans (min_le_right ..))) -- orientation maybe
variable {U:Scree.Loom N}{e a:ℝ}{P:BudgetPoint}{n r:ℕ}{S X D Z:Support (More N)}(hp:0<e)(h:Roof N b e r U)(vb:P.threshold ≤ b)
variable {m:ℝ}(G':HopeT e m a P.order)(x:Orbit N)(Y:Vow.Aura N)(pY:halo (r+10) S ⊆ Y.val) -- tune
variable (pz:P.threshold ≤ a)(hD:halo (cipherK r) D ⊆ Y.val)(hs:cipherK r≤5*P.B)(ht:3≤P.B)
include hD pY hs ht pz h G' vb
lemma earnR (p:x.1∈σX P Y D)(t:D⊆Z)(z:Bond SS)(wZ:Skye.ends z⊆S): Tender (fun v:tangD N=> U ((pressQ P Z x.1 v,x.2):Orbit N) z) 0 m P.order:=by
 have hy:= portA h vb hD p S pY t hs ht (show z.1∈S from wZ (by simp)); let Yq:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Bond SS=>SU.group.Color) z; let B(v:tangD N):=pressQ P Z (U x) v; let W:tangD N→L[ℝ]SU.group.Color:= P.threshold • Yq
 suffices p:Tender (fun v=> B v z) 0 m P.order by exact p.same (hy.symm.mono fun i t=> congrArg SU.group.mat t)
 by_cases g:z∈unrest Z P.B; swap
 · refine Shake.same ((Shake.holds (SU.group.mat ((U x) z))).bag G'.ease.le) (Eventually.of_forall ?_); intro y; change _=SU.group.mat (B y z); unfold B pressQ gyrate Function.comp increment; rw [steadyB,if_neg g]; simp
 have hz:‖Yq‖ ≤ 1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i'=> (norm_le_pi_norm i' z).trans_eq (one_mul _).symm
 apply Shake.same (G'.until' _ W ((U x) z) ?_)
 · exact Eventually.of_forall fun y=> by change _=SU.group.mat (B y z); unfold B pressQ gyrate Function.comp increment; rw [steadyB,if_pos g]; rfl
 unfold W; rw [norm_smul,Real.norm_of_nonneg P.threshold_pos.le]; exact (mul_le_of_le_one_right P.threshold_pos.le hz).trans pz
end YM.CF.Rill
