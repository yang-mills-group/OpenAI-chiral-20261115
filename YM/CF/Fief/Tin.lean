import YM.CF.Fief.Bol
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
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
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{f:Side}{K:E→ Config SU.group f}{X:Support f}{A:Finset (Cell f)} {x:E}{q:Chi}{t σ:ℝ}{n d:ℕ}
lemma lateB {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{f:E→ F}{x:E}(p:ContDiffAt ℝ (↑n) f x):∃ C:ℝ, 0<C∧∀ᶠ i in 𝓝 x, Allows n f i C:=by
 let C:=∑ i: Fin (n+1),‖iteratedFDeriv ℝ (i:ℕ) f x‖; have he(j:ℕ)(p:j≤n): ‖iteratedFDeriv ℝ j f x‖ ≤ C:=single_le_sum (f:=fun i:Fin (n+1)=>‖iteratedFDeriv ℝ (i:ℕ) f x‖) (fun i _=>norm_nonneg _) (mem_univ (⟨j,Nat.lt_succ_of_le p⟩: Fin (n+1))); have hc : 0 ≤ C:=(norm_nonneg _).trans (he 0 (Nat.zero_le _)); refine ⟨C+1,by positivity,?_⟩
 have hp(j:Fin (n+1)):∀ᶠ v in 𝓝 x,‖iteratedFDeriv ℝ (j:ℕ) f v‖ ≤ C+1:= (p.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.lt_succ_iff.mp j.isLt))).norm.eventually (ge_mem_nhds ((he _ (Nat.lt_succ_iff.mp j.isLt)).trans_lt (lt_add_one _)))
 filter_upwards [eventually_all.mpr hp,p.eventually (by simp)] with i v k; exact ⟨k,fun j h=>v ⟨_,Nat.lt_succ_of_le h⟩⟩
lemma grant_cost(p:∀ i:Bond f,ContDiffAt ℝ (↑n) (fun i'=> SU.group.mat (K i' i)) x):∃ D:ℝ,0 ≤ D∧∀ᶠ v in 𝓝 x, ∀ i:Bond f,grantB n (fun y=>K y i) v D:=by
 choose C h H using fun i=>lateB (p i); let D:=∑ i,C i; have he(i):C i ≤ D:=single_le_sum (fun i _=> (h i).le) (mem_univ i)
 refine ⟨D,sum_nonneg (fun i _=>(h i).le),?_⟩; filter_upwards [eventually_all.mpr H] with i hp y using (hp y).mono (he y)
lemma horizonB (h: HeldT K A x):∀ᶠ i in 𝓝 x,HeldT K A i:=by
 filter_upwards [eventually_eventually_nhds.mpr h,h] with i g p; filter_upwards [g] with z v u t; rw [v u t,p u t]
lemma turnM(A:Finset (Cell f))(p:HeldT K A x)(W: RG.Atom G₅ d)(i:Site f) {v:ℝ}(σ:ℝ)(h:Allows n (fun y=> W.unmasked (K y) i) x (v*W.budget σ)) : Allows n (peer_k W A t i ∘ K) x (v*W.budget σ):=by
 let Y(y):Prop:= polP t (K y) (W.footprint i) A; have hp:∀ᶠ i in 𝓝 x,Y i ↔ Y x:= p.mono fun j v=> forall_congr' fun z=>imp_congr_right fun s=>by rw [Pressure.toll,v z (mem_inter.mp s).1]; rfl
 by_cases g:Y x
 · refine h.germ (hp.mono fun y v=>(?_ :peer_k W A t i (K y)=_).symm); exact if_pos (v.mpr g)
 apply (allows_const x (v:=(0:ℝ)) (C:=v*W.budget σ) (by rw [norm_zero]; exact h.nonneg)).germ; exact hp.mono fun y v=>Eq.symm (if_neg (mt v.mp g) : peer_k W A t i (K y)=_)
lemma loopK (p:∀ i:Bond f,ContDiffAt ℝ (↑n) (fun i'=> SU.group.mat (K i' i)) x)(v:HeldT K A x)(ht:0<t)(hy:t ≤ 1)(h:0<σ)(d:ℕ)(q:Chi):∃ C:ℝ,0≤C ∧∀ᶠ i in 𝓝 x,∀(W:RG.Atom G₅ d)(y:Site f), Allows n (lush_k q W A t y ∘ K) i (C*W.budget σ) ∧ Allows n (peer_k W A t y ∘ K) i (C*W.budget σ) ∧ ∀ V:Clip, Allows n (Cloak.sleeve W A V y t∘ K) i (C*W.budget σ):=by
 have hg(y:Cell f):ContDiffAt ℝ (↑n) (fun i'=>SU.group.mat (faceValue (K i') y)) x:=by -- tune lemma
    exact SelectedOrderedKernels.Sector.travel_smooth _ _ p
 obtain ⟨D,hD,H⟩:=grant_cost p
 choose W hW HW using fun i=>lateB (hg i)
 let D':=∑ y,W y; let P:= max (D/t+D'/t) (max 1 SU.group.colorScale); have hz:(1:ℝ)≤ P:=(le_max_left ..).trans (le_max_right ..); have ht':SU.group.colorScale ≤ P:=(le_max_right ..).trans (le_max_right ..)
 have hu(i): W i ≤D':=single_le_sum (fun j _=> (hW j).le) (mem_univ i)
 have hh: 0≤ D':= sum_nonneg (fun i _=>(hW _).le); have he:D/t+D'/t≤ P:= le_max_left ..
 obtain ⟨C,hC,hx⟩:= crown_h P σ hz n d h ht' q; obtain ⟨C',hv,hw⟩:= plain n d D σ h hD
 let M:=max C C'; have hp : 0≤ M:=hC.trans (le_max_left ..); refine ⟨M,hp,?_⟩
 filter_upwards [H,eventually_all.mpr HW,horizonB v] with i p' k x' X y
 have hW': 0 ≤ X.budget σ:=by unfold RG.Atom.budget RG.Atom.magnitude; positivity
 have hv:= hw K i p' X y; have hh:= (hx K i t A ht hy (fun j=> (Shake.pick (p' j)).bag ((div_le_iff₀ ht).mp ((le_add_of_nonneg_right (by positivity :0 ≤ D'/t)).trans he))) (fun j=> (Shake.pick (k j)).bag ( (hu j).trans ((div_le_iff₀ ht).mp ((le_add_of_nonneg_left (div_nonneg hD ht.le)).trans he)))) x' X y)
 have hp:= (hv.mono (mul_le_mul_of_nonneg_right (le_max_right C _) hW')); refine ⟨hh.1.mono (mul_le_mul_of_nonneg_right ?_ hW'),turnM _ x' _ _ _ hp, fun v=>(hh.2.2 v).mono (mul_le_mul_of_nonneg_right (le_max_left ..) hW')⟩
 exact le_trans (mul_le_of_le_one_right hC (pow_le_one₀ ht.le hy)) (le_max_left ..)
end YM.CF.Fief
