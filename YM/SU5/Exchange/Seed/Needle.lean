import YM.CF.Rive.Ora
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import YM.SU5.Exchange.Seed.Zero
import YM.CF.Pso.Pick
import YM.CF.Ione.Pose
import YM.CF.Ione.Lean
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Mew Ione
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
open Vow Larch Rue Push.AbsoluteSums Trees Ursell
-- two readings; sum-bound tail with varying witnesses at fixed price
variable{C:Type}[Fintype C][LinearOrder C] (Vb:Mew.Key C→ Pax n) (P:BudgetPoint)
variable (hp1:1≤h)(g:∀ x:Aura n,∀ y,River (fun z:Key C=> Vb z x y)){B:ℕ}{δ S a q:ℝ} (X:Mew.Key C→ Aura n→ℝ)(u:0 ≤ a)(s:∀ i∈hill C,Ready Palot.stern B (X i) a S δ q) (o:∀ i∈hill C,∀ x, Medal P x.val ∅ (Vb i x) h (X i x)) (qh:0 ≤ q)(qt:q<1)
open Bake Gas
open scoped YM.CF.Mew
-- derivative of opacity assembly on just one tag. Visibility matters.
variable (Q:Aura n→ℝ) (t:Ready Palot.stern B Q a S δ q) (O:∀ z∈hill C, ∀ x:Aura n, Medal P x.val ∅ (Vb z x) h (Q x)) (V0: Vb 0=0)
include u g hp1 O V0 t
lemma hour (X:Aura n)(V:Orbit n)(Y:visible P X.val ∅ V.1)(i:C):
 tipI (fun z=>FeeD P (Vb z) X V) [i]= tipI (fun z=> Vb z X V) [i]:=by
 let F(z:Mew.Key C)(m:ℕ):= funge X (Vb z) 0 m V
 have hr(z:Mew.Key C):FeeD P (Vb z) X V=∑' m,F z m:=if_pos Y
 let E(m:ℕ):= ∑ j:Tuple (Aura n) m,sepV Q X 0 ⟨m,j⟩
 have kv (v:Clusters (Aura n)): 0≤ sepV Q X 0 v:= (ponder X v hp1 (O 0 roots) 0).wage (zero_le_one.trans hp1)
 have ht(m:ℕ):0 ≤ E m:=sum_nonneg (fun _ _=>kv _)
 have hh : Summable E:=by simpa only [tsum_fintype] using ((glomM (m:=0) X t u).sigma)
 have hE:Integrable E Measure.count:=by rw [integrable_count_iff]; simpa only [Real.norm_eq_abs,abs_of_nonneg (ht _)] using hh -- simp only ht wildcard unbound
 have hS(z : Mew.Key C)(w:z∈hill C)(m:ℕ) : ‖F z m‖≤ E m:=by
    obtain ⟨W,p',f⟩:=Y; unfold F funge; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; refine sum_le_sum (fun j v=>?_)
    let R:=ponder X ⟨m,j⟩ hp1 (O z w) 0; rw [R.same V (W,V.2) f (fun _ _=>rfl)]; exact R.capF hp1 _ p'
 have hU(z : Mew.Key C)(w:z∈hill C): Integrable (F z) Measure.count:= integrable_count_iff.mpr (hh.of_nonneg_of_le (fun _=> norm_nonneg _) (hS z w))
 have hR(j):River fun z=>F z j:=by
    unfold F funge; simp_rw [Finset.sum_apply]; refine tick_sum _ _ (fun k _=>?_); let p:Clusters (Aura n):=⟨j,k⟩
    change River (fun z=>sta (Vb z) X 0 p V); unfold sta; split; swap; exact zeroR _
    unfold guava; simp_rw [Pi.smul_apply,Finset.prod_apply]; exact bScale _ (cost_R _ _ (fun a _=>g _ _)) (coefficient gRule p.2/(p.1+1).factorial)
 have e:Set.EqOn (fun z=>FeeD P (Vb z) X V) (fun z=>∫ i,F z i∂Measure.count) (hill C):=by intro z w; change FeeD P (Vb z) X V=∫ i,F z i∂Measure.count; rw [hr,integral_countable (hU z w)]; simp [measureReal_def]
 obtain ⟨j0,w⟩:=wind_eq Measure.count F hR hE (fun z w=>(hU z w).aestronglyMeasurable) hS (0:Key C) roots i
 rw [show tipI (fun z=> FeeD P (Vb z) X V) [i]=tipI (fun z=>∫ n,F z n∂Measure.count) [i] from lace_C _ e roots]
 change cutI (fun z=>∫ n,F z n∂Measure.count) i 0= _; rw [w,integral_countable j0]; simp only [measureReal_def,Measure.count_singleton,ENNReal.toReal_one,one_smul]
 have hε(m:ℕ)(hu:m≠0): cutI (fun z=> F z m) i 0=0:=by
    change tipI (fun z=> F z m) [i]=0; let Kz(j:Tuple (Aura n) m)(z:Mew.Key C):= sta (Vb z) X 0 ⟨m,j⟩ V
    have ht(j:Tuple (Aura n) m): River (Kz j) ∧ tipI (Kz j) [i]=0:=by
       by_cases hx:X=tideU ⟨m,j⟩; swap
       · simp_rw [Kz,sta,if_neg (show ¬ (X=tideU ⟨m,j⟩ ∧ 0 ≤ m) from fun v=>hx v.1)] -- tune
         exact ⟨zeroR _,tip_0 _⟩
       simp_rw [Kz,sta,if_pos (show (X=tideU ⟨m,j⟩ ∧ 0 ≤ (⟨m,j⟩ : Clusters (Aura n)).1) from ⟨hx, Nat.zero_le m⟩)]; let U':ℝ:= coefficient gRule j/(m+1).factorial
       let G (a:SongQ m)(z:Mew.Key C):= Vb z (j a) V; let J(z):=∏ k: SongQ m,G k z; let R := cost_R univ G (fun j _=>g _ _) -- tune
       unfold guava; simp_rw [Pi.smul_apply, Finset.prod_apply]; change River (fun z=>U' • J z) ∧ _
       have hG: River J:= R
       rw [show (fun z:Mew.Key C=> U' • J z)=fun z=> (U':ℂ) • J z from funext fun x=> (Complex.coe_smul ..).symm]; refine ⟨hG.scale _, ?_⟩
       change tipI (fun z=>U' • J z) [i]=0; simp_rw [←Complex.coe_smul]; rw [tip_C hG]; suffices hf:tipI J [i]=0 from by rw [hf,smul_zero]
       let l:=none (α:=Fin m); let S:= (univ:Finset (SongQ m)).erase l; have hz₀(z:Mew.Key C):J z= G l z*∏ k∈S,G k z:=(mul_prod_erase _ (fun i=> G i z) (mem_univ l)).symm -- orientation
       rw [funext hz₀]; let K(z:Mew.Key C):=∏ i∈ S,G i z; have e :m>0:=Nat.pos_of_ne_zero hu
       change tipI (G l*K) _=_; rw [tip_mul (show River (G l) from g (j l) V) (show River K from cost_R _ _ (fun k _=>g (j k) _))]; change _* K (dune i 0)+G l (dune i 0)*_=0
       rw [show dune i (0:Mew.Key C)=0 from centre i,show G l 0=0 from (by unfold G; rw [V0]; rfl), show K 0=0 from prod_eq_zero (show some (⟨0,e⟩ : Fin m) ∈ S from mem_erase.mpr ⟨by simp [l],mem_univ _⟩) (by unfold G; rw [V0]; rfl),mul_zero,zero_mul,zero_add]
    unfold F funge; simp_rw [Finset.sum_apply]; change tipI (fun z=>∑ j,Kz j z) [i]= _; exact ((tip_bank univ Kz (fun j _=>(ht j).1)).2 _).trans (sum_eq_zero fun j _=>(ht j).2)
 rw [tsum_eq_single 0 hε]; unfold F; simp_rw [sheerH X]; rfl
end YM.CF.Rive
