import YM.CF.Tye.Muse
import YM.CF.Vale.Tour
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief rates
variable (q:Chi)(j l n:ℕ)
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{e x:ℝ}{T:Tube G₅ S}
open Tye
lemma flockB (P:Patch)(K:Teller G₅)(p:P.Branches K.bind G₅)(A D:ℝ)(g:0 ≤ A)(h:0<D)(hv:3 ≤ l)(hl:l ≤18)(hx:l+78 ≤ j)(hn:2 ≤ n)(W:∀ i:ℕ,3 ≤ i → i ≤ n+8 →  Push.Uniform.Before G₅ K.top.width K.top.paths K.j K.bind i):∃ C M:ℝ,0<C∧0<M ∧∃ N T1:ℝ→ℝ, sizeK P.L 1 N ∧ sizeK P.L 3 T1∧∀ᶠ x:ℝ in atTop,∀ {N' R B:Side}{G:Ratio (mid N' B) (mid R B)}{e:ℝ}(S:StepData (Domain N' B) (Domain R B))(T:Tube G₅ S), Cert P K S T x → (coverB l j+coverB l j+101)*radiusB x ≤ (Domain N' B).val →∀ U:Muster G S x e T,U.beta∈Set.Icc (y G₅ P.L x/2) (2*y G₅ P.L x)→ U.loft=j →U.post=l→U.trot=q→ U.room=D*fiery G₅ x P.L→∀ Z: Monk SU.group S,sizedP G₅ P K S T Z.park → Z.key.flags=RG.flags (temp x) Z.V →∀ L:ℝ,‖Z.z‖≤L → L ≤ A*Scales.p G₅ P.L x → ∀ o:Site (Domain N' B),let Tp(j:ℕ):ℝ:= (about P.L 0)*billC C M n j P L x; let X:=fun i=> Z.atop i x; let Bn:=fun i=> wish U (X i) o; let Gn:=fun i=> wish U (violet (X i)) o
 Allows n Bn 0 (Tp 3) ∧ Allows n Gn 0 (Tp 3) ∧ Allows n (Bn+Gn) 0 (Tp 4+Tp 4) ∧ Allows n (fun i=> flockK U (X i) o) 0 (N x)∧(o∉ Z.key.dome (coastA j l *radiusB x+1) → Allows n (fun i=>flockK U (X i) o) 0 (T1 x)):=by
 obtain ⟨a,b,c,F,F',M,ha,hb,h,h',ht,hm,H⟩:= Cay.post P K n l j (W _ (by omega) (by omega)) (W _ (by omega) (by omega)) (W _ (by omega) (by omega)) p hn hl hx A D g h q; let v:=Fintype.card Axis*P.L.val^4*Rel.plot 1; let B(x):= A*Scales.p G₅ P.L x
 let N(x):= rates.bill n l P D F M (Cay.burn a x P) (2/Scales.g G₅ P.L x) (2*y G₅ P.L x) (B x) x; let N'(x):=rates.bull (n+4) l F' (2*Scales.g G₅ P.L x) (2*y G₅ P.L x) (Cay.burn b x P) (B x)
 refine ⟨c,M,ht,hm,fun x=> v*N x,fun x=>v*N' x,(bill_s ..).scale _,(bill_h _ _ _ _ _ _ hv).scale _,?_⟩ -- tune
 filter_upwards [H, (year G₅ P.L).eventually_gt_atTop 0, (burn_k P a).spine.eventually (ge_mem_nhds zero_lt_one)] with x hB he η C R Y G e S T H' heX U hz hk hw g tt A' hC hK L hL u o t X Bn Gn
 have hL':=le_trans (norm_nonneg _) hL; have hs:= hB _ hz S T H' _ _ hL' hL u heX hC hK; have hE(i:ℝ)(p:0 < i):0≤Cay.burn i x P:=by unfold Cay.burn Neige.lamp; have ht:=temp_nonneg x; rw [Scales.fi]; have hp:=Scales.pos G₅ P.L x; have hv:=Scales.gauge G₅ P.L he; positivity
 have hp:= check_b n l F M a D A P L hL' u hz he (hE _ ha) (temp_nonneg _) h.le hm.le; have hY:=check_h (n+4) l F' b A P L hL' u hz he (hE _ hb) h'.le; let U':=univ.filter (fun i:Bond (Domain R Y)=>separation o (S.ratio.parent i.1)≤1); have hy: (#(U'):ℝ) ≤ v:=Nat.cast_le.mpr ((iconic o 1).trans_eq (by unfold v ratioB; rw [H'.got]; rfl))
 have heN(V:ℝ)(e:0≤V)(h:∀ i∈ U',Allows n (fun y=> opus T x U.trot U.room U.post U.beta U.loft i (X y)) 0 V):Allows n (fun y=>flockK U (X y) o) 0 (v* V):=by
    refine ((summed U' (fun i y=> ansC (S:=S) o i * _) (fun i p=>((h i p).smul (ansC (S:=S) o i)).mono (mul_le_of_le_one_left e (plant_v (w:=fun _:Fin (0+2)=>i))))).mono (mul_le_mul_of_nonneg_right hy e)).germ ?_; filter_upwards with y; apply sum_subset (subset_univ _) ; intro i p z; unfold ansC; rw [if_neg (fun h=>z (mem_filter.mpr ⟨p,innZ _ _ h⟩)),zero_mul]
 have hh(i:Bond (Domain R Y)) := (hs.cost i).mono hp.2; have hW: Allows n (fun y=> flockK U (X y) o) 0 (v*N x):=by
    refine heN _ (hp.1.trans hp.2) (fun i _=>?_); rw [hw,hk,tt,g]; exact hh i
 have hf(p:o∉A'.key.dome (coastA j l*radiusB x+1)):Allows n (fun y=> flockK U (X y) o) 0 (v*N' x):=by
    refine heN _ (hY.1.trans hY.2) (fun i t=>?_); rw [hw,hk,tt,g]; have ht : S.ratio.parent i.1∉ A'.key.dome (coastA j l*radiusB x):= fun h=> p (Atala.dome_u h ((congrArg (fun k'=> _+ k') (separation_comm _ _)).trans_le (Nat.add_le_add_left ((mem_filter.mp t).2) _))); exact (hs.star i ht).mono hY.2

 rw [←hw,←hk] at hs; rw [← tt,←g] at hs
 have ht':= stemK n P U A' o hs hL' hz he hm.le (hE _ ha) η ht.le; dsimp only at ht'; rw [H'.got] at ht'; exact ⟨ht'.1,ht'.2.1,ht'.2.2,hW,hf⟩
end YM.CF.Lor
