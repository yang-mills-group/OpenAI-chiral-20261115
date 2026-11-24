import YM.CF.Esti.Flow
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
abbrev Inure (A:Stores S)(x:ℝ)(q:Chi)(k:S.Choices)(a:ℝ)(i:Bond c)(U:Config G f):= if onS A x i then SU.group.mat (S.prediction U k i) else abortP S q k i a U
abbrev litF(A:Stores S)(x:ℝ)(k:S.Choices)(U:Config G f)(i:Site c):= if onF A x i then AnalyticBridge.Annulus1AD.frame k U i else (Fintype.card S.patch.FrameTag:ℝ)⁻¹
abbrev litB(A:Stores S)(x:ℝ)(k:S.Choices)(U:Config G f)(i:Bond c):= if onS A x i then AnalyticBridge.Annulus1AD.bond k U i else (Fintype.card S.patch.Points:ℝ)⁻¹
abbrev tidal(A:Stores S)(x w a:ℝ)(q:Chi)(U:Config G f)(V:Config G c)(k:S.Choices)(i:Bond c):ℝ:= testing q (w*fiery G x S.patch.L) (fareG G (SU.group.mat (V i)*star (Inure A x q k a i U))) (if i∈A.aisles then false else true)
def cohoT(A:Stores S)(x w a:ℝ)(q:Chi)(V:Config G c)(U:Config G f)(k:S.Choices)(N F: Support c):ℝ:= total A x q U F * (∏ p∈nearNoise N, tidal A x w a q U V k p) * ((∏ i∈N,litF A x k U i)*(∏ i∈nearNoise N,litB A x k U i))
structure Volo (S:StepData c f)(n:ℕ)(a b C M:ℝ): Prop where
 wind(u:S.Choices)(i:Bond c): Vim G n S u i a b C M
variable {F:Tree.Forest S.ratio}{I:Support c}{Y:Pane c} -- actually n specialized?
abbrev FuelG(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(x:E)(n:ℕ)(a:ℝ):=∀ i:Bond f,grantB n (fun v=>U v i) x a
section wind
variable (A:Stores S)(q:Chi)(k:S.Choices){E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E](U:E→ Config G f)(z:E)(hV:FuelG E U z n C) -- implicit FuelG expects E
variable (B:Stores S)(N :Support c)(h: B.dome v ⊆ N)(l:r+shovel S.patch ≤ v)(p:shovel S.patch+10 ≤ radiusB x)(ht:0<fiery SU.group x S.patch.L)(hy:fiery SU.group x S.patch.L ≤ a/2)(hk:Volo S n a b C m)(he:total A x q (U z) N ≠ 0)
include A q k h l p ht hy hV hk he
lemma capita(i:Bond c)(g:i∈nearNoise (B.dome r)): Inure A x q k a i (U z)=SU.group.mat (S.prediction (U z) k i) ∧ litB A x k (U z) i=bond k (U z) i:=by
 unfold Inure litB; split_ifs with L; · exact ⟨rfl,rfl⟩
 have hp:ResV S  (a:=a/2) i (U z):=by rw [charged]; exact fun j p'=>( (charged ..).mp (yes_z p l g _ N h ht L he) _ p').trans hy
 have ha:0<a:=by linarith only [ht,hy]
 refine ⟨abort_e S q k i ha _ hp,?_⟩ -- tune
 have h' :ResV S  (a:=a) i (U z):=by rw [charged]; exact fun j u=>((charged ..).mp hp j u).trans (half_le_self ha.le)
 exact Eq.symm (if_pos (show S.patch.usesBest S.kernel _ from (hk.wind k i E U z h' hV).1))
lemma capital (i:Site c)(g:i∈B.dome r):litF A x k (U z) i= AnalyticBridge.Annulus1AD.frame k (U z) i:=by
 unfold litF; split_ifs with b'; rfl
 let j:Bond c:=(i,0); have h':i∈pinPos j:=mem_insert_self ..; have hx:j∈nearNoise (B.dome r):= mem_filter.mpr ⟨mem_univ _,fun p=> Finset.disjoint_left.mp p h' g⟩; have hf :=yes_f p l hx (U z) N h ht b' h' he
 have hh:ResV S (a:=a) j (U z):=by
    rw [charged]; have hv: fiery SU.group x S.patch.L ≤ a:=by linarith only [hy,ht]
    exact fun i u=>((charged ..).mp hf i u).trans hv
 exact Eq.symm (if_pos (show S.patch.usesMin S.kernel _ from (hk.wind k j E U z hh hV).2.1 i h'))
lemma tide_re (i:Bond c)(g:i∈nearNoise (B.dome r))(V:Config G c)(w:ℝ): tidal A x w a q (U z) V k i=tokenB A q x w (U z) V k i:=by
 have hp:=capita A q k U z hV B N h l p ht hy hk he _ g; unfold tidal; rw [hp.1,← SU.group.mat_inv,← SU.group.mat_mul,fare_h]; split; next x=> exact (chooseB ..).symm.trans (if_pos x).symm
 next h=>exact (chooseF ..).symm.trans (if_neg h).symm
end wind
section bind
variable (A:Stores S)(q:Chi)(k:S.Choices){E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E](U:E→ Config G f)(z:E)(hV:FuelG _ U z n C)(B: Stores S)(N:Support c)(h: B.dome v ⊆ N)(l:r+shovel S.patch ≤ v)(p:shovel S.patch+10 ≤ radiusB x)(ht:0<fiery SU.group x S.patch.L)(hy:fiery SU.group x S.patch.L ≤ a/2)(hk:Volo S n a b C m)
include hV h l p ht hy hk
lemma works_b (w:ℝ)(V:Config G c)(hf:A.flags=RG.flags (temp x) V): cohoT A x w a q V (U z) k (B.dome r) N= receipts q A x w (B.dome r) (nearFace S N) (nearNoise (B.dome r)) (U z) V k :=by
 unfold receipts profilesHere cohoT prayersHere; have hh: ∏ i∈B.dome r, flag x A V i=1:= Finset.prod_eq_one fun i _=> if_pos (by rw [hf]); rw [hh,mul_one]; change _=total A x q (U z) N *_ *_
 by_cases j:total A x q (U z) N=0; rw [j,zero_mul,zero_mul,zero_mul,zero_mul]
 exact congrArg₂ (·*·) (congrArg (total A x q (U z) N*·) (prod_congr rfl fun i g=> tide_re _ q k U z hV B N h l p ht hy hk j i g V w)) (congrArg₂ (·*·) (prod_congr rfl (fun x t=>capital _ q k U z hV B N h l p ht hy hk j x t)) (prod_congr rfl (fun x t=>(capita _ q k U z hV B N h l p ht hy hk j x t).2)))
end bind
end YM.CF.Esti
