import YM.CF.Esti.Lode
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
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Pressure.Stores Bloch Exterior
lemma shares_q(s:Signed): (turnStore s O).shares = O.shares:=by simp [turnStore, Pressure.Stores.shares]
def epoch (L:Side):=Fintype.card Axis+Fintype.card PlaqAxes+Fintype.card Axis*L.val^4+Fintype.card PlaqAxes*L.val^4+Fintype.card Gain+1
abbrev fulg(O:Stores S)(j:ℕ)(x:ℝ):= plotBill O (j+125) (radiusB x)
-- charge all stencils counted
abbrev latticeFieldEstimates(O:Stores S)(j:ℕ)(x:ℝ):=4*(fulg O j x * epoch S.patch.L)
lemma refer(j i:ℕ)(v:j ≤ i): plotBill O j (radiusB x)≤ plotBill O i (radiusB x):=by unfold plotBill; gcongr
lemma vault{s:Signed}(j:ℕ): cardsQ (whim x j O s) ≤ latticeFieldEstimates O j x:=by
 let N:=turnStore s O; let b:=radiusB x; let L:=epoch S.patch.L; let X:=whim x j O s; let c:=fulg O j x
 have hp:N.shares= O.shares:=shares_q s
 have ht:(N.dome (j*b)).card ≤ c:=by
    refine (dome_count N j b).trans ((refer j _ (Nat.le_add_right j 125)).trans_eq ?_) -- tune implicit
    unfold c fulg plotBill; rw [hp]
 have hf : X.face.card ≤ c*L:=by
    refine (fine_count (X.face) _ (fun i p=>show S.ratio.parent i.1 ∈ N.dome (j*b) from (mem_filter.mp p).2)).trans ?_; unfold L epoch; rw [mul_comm c]; gcongr; omega
 have hM {α:Type}[Fintype α](P:Finset (Site _×α))(h:Fintype.card α≤ L)(u:∀ i∈P,i.1∈N.dome (j*b)): P.card ≤ c*L:= (coarse_count P _ u).trans (by gcongr)
 have hu:=hM X.noise (by unfold L epoch; omega) (fun i p=> (mem_filter.mp p).2); have hg:=hM X.coarse (by unfold L epoch; omega) (fun i p=> (mem_filter.mp p).2); have hh:=hM X.rows (by unfold L epoch; omega) (fun i p=> (mem_filter.mp p).2); change X.face.card+X.noise.card+X.coarse.card+X.rows.card≤4*(c*L); omega
lemma tune (j:ℕ)(hp:1≤radiusB x):
 (obv x j 100 O).card ≤ latticeFieldEstimates O j x ∧(nearNoise (obv x j 100 O)).card ≤ latticeFieldEstimates O j x ∧(nearFace S (obv x j 110 O)).card ≤ latticeFieldEstimates O j x∧(locals A O x F ((j+104)*radiusB x)).card ≤ latticeFieldEstimates O j x:=by
 let p:=radiusB x; let L:= epoch S.patch.L; let v:= latticeFieldEstimates O j x
 have ht {i k:ℕ} (hk:k ≤ j+125)(h:i ≤ epoch S.patch.L) : i*plotBill O k (radiusB x) ≤ v:=le_trans ((mul_comm i _).le.trans (Nat.mul_le_mul (refer k _ hk) h))  (le_mul_of_one_le_left (by positivity) (by norm_num))
 have he:= counts_torus O (j+100) p hp; refine ⟨(dome_count O (j+100) p).trans ((one_mul _).symm.le.trans (ht (by omega) (by unfold epoch; omega))), he.1.trans ((mul_comm ..).le.trans (ht (by omega) (by unfold epoch; omega))), (counts_torus O (j+110) p hp).2.2.trans (ht (by omega) (by unfold epoch; omega)), ?_ ⟩
 apply le_trans (b:=(everyLink S O ((j+104)*radiusB x)).card) _ ((counts_torus O (j+104) p hp).2.1.trans (ht (by omega) (by unfold epoch; omega)))
 refine card_le_card_of_injOn (fun i => i.val.val) ?_ (fun _ _ _ _ h => Subtype.ext (Subtype.ext h))
 intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
end YM.CF.Esti
