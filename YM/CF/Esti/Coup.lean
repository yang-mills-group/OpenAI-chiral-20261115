import YM.CF.Esti.Gain
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {F:Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{β c' D L v':ℝ}
abbrev still(n:ℕ)(q D C:ℝ):= Jet.composeCost n D (2/q^2*(2^n*C*C))
abbrev plat(n:ℕ)(u a J C M:ℝ):= zest n*still n (2*a) M C* Jet.composeCost n J C
abbrev plume(n:ℕ)(u a J C M:ℝ):= Jet.composeCost n (Real.exp (Jet.composeCost n J C)) (plat n u a J C M)
abbrev grip(n:ℕ)(u a J C M:ℝ) (x:ℕ):= zest n*((zest n * plume n u a J C M)^x)*((zest n* still n a M C)^x)
variable {R:ChartRatio G}
structure Red (R:ChartRatio G)(n:ℕ)(t m:ℝ):Prop where
 cost(x:SU.group.Color): ‖x‖≤ t → Allows n (Real.log ∘ R.J) x m
lemma rene(R:ChartRatio G)(h:LocalRatio R)(n:ℕ):∃ t C:ℝ,0<t∧ 1≤ C ∧ Red R n t C:=by
 let t:=R.radius/2; have ht:= half_pos h.patch
 obtain ⟨K,hK,H⟩:= Push.Uniform.exists_allows (f:=Real.log ∘ R.J) (isCompact_closedBall (0:SU.group.Color) t) (fun x (hx:x∈ closedBall 0 t)=> by have hp:x∈ Metric.ball (0:SU.group.Color) R.radius:=mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt (half_lt_self h.patch)); exact (h.germ x hp).log (h.pos _ hp).ne') n
 exact ⟨t,max 1 K,ht,le_max_left ..,⟨fun x k=>let P':=H x (mem_closedBall_zero_iff.mpr k); ⟨P'.1.of_le le_top,fun i l=>(P'.2 _ l).trans (le_max_right ..)⟩⟩⟩ -- elaborator f
lemma ore_q (n:ℕ){F:E→SU.group.Color}(p:Allows n F x' C)(q:Chi)(a:ℝ)(ht: C ≤ t)(h:Red R n t L)(hd:Dane G n q D): Mesh n (fun i=>Next.SectorChange.extended q R a (F i)) x' (plume n t a L C D):=by
 let P:=Jet.composeCost n L C; let N(y:E):= Real.log (R.J (F y)); have hp:Allows n N x' P:=(h.cost _ (p.value.trans ht)).comp p
 have he: Next.SectorChange.logGuard q R a (F x') ≤ P:=by
    unfold logGuard; have ht:= Next.SectorChange.broad_range q (F x') (2*a); refine (mul_le_mul_of_nonneg_left (le_trans (le_abs_self (N x')) hp.value) ht.1).trans ?_; exact mul_le_of_le_one_left hp.nonneg ht.2
 let X(y:E):=Next.SectorChange.logGuard q R a (F y); exact ⟨light_c X (allot (posts _ F p q _ hd).1 hp) _ he, sigP _ (extended_pos ..)⟩
lemma capsule_p(n:ℕ)(S:Finset (Active A x F))(U:E→LogArray G (Active A x F))(p:∀ i∈S, Allows n (fun x=>U x i) x' C)(q:Chi)(a:ℝ)(ht:C≤ t)(h:Red R n t L)(hd:Dane G n q D): Mesh n (fun i=> capsule x A F q a R S (U i)) x' (grip n t a L C D S.card):=by
 have hx:=fuel S (fun i x=>Next.SectorChange.broad q a (U x i)) (fun i p'=> let P:=posts _ _ (p i p') q _ hd; ⟨P.1,P.2⟩)
 have hs:= fuel S (fun i x=>Next.SectorChange.extended q R a (U x i)) (fun i p'=>let P:= ore_q (F:=fun x=>U x i) n (p i p') _ _ ht h hd; ⟨P.1,P.2⟩)
 exact mesh _ _ _ ⟨hs.1,hs.2⟩ ⟨hx.1,hx.2⟩
end YM.CF.Esti
