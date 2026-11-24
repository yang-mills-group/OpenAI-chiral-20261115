import YM.CF.Vow.Jig
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
variable {F:ℕ→ Copy n}{u:ℕ→ℝ}
variable (p:∀ i,Medal P X D (F i) h (u i))(g: Summable u)(k':1≤ h)
abbrev lasting(P:BudgetPoint)(X D:Support (More n))(F:ℕ→ Copy n):Copy n:=zenS P X D (fun i=>∑' j,F j i)
include p g k'
lemma lend(A:Orbit n)(v:visible P X D A.1): Summable (fun i=> F i A):=by
 obtain ⟨i,t,r⟩:=v
 refine Summable.of_norm_bounded g fun j=>?_
 rw [(p j).same A (i,A.2) r (fun _ _=> rfl)]; exact (p j).capF k' _ t
lemma tsign : ThemeR X (lasting P X D F):=by
 let U:= lasting P X D F
 refine ⟨fun i j t v=>?_,fun i=>?_, ?_,fun i x=>?_⟩
 · unfold lasting zenS; rw [visibly t]; congr 1; exact tsum_congr fun n=> (p n).same i j t v
 · unfold lasting zenS; split
   next v=> let M:=stretch (camp X); exact (stretch_ok _).mp (tsum_mem (show IsClosed (M:Set (Cipher n)) from Submodule.closed_of_finiteDimensional M.toSubmodule) (fun j=>(stretch_ok ..).mpr ((p j).lit i)))
   exact Flour.trivial
 · let J(y:Orbit n):Prop:=visible P X D y.1; let K(i:ℕ)(x:Orbit n):=zenS P X D (fun y=>∑ j∈range i,F j y) x
   have he(i):Measurable (K i):=Measurable.ite (show MeasurableSet {y|J y} from measurable_fst ((Rue.year_s _ ping_o).measurableSet)) (Finset.measurable_fun_sum _ fun i _=>(p i).keeps) measurable_const -- tune
   apply measurable_of_tendsto_metrizable he; refine tendsto_pi_nhds.mpr fun i=>?_; simp only [K,lasting,zenS]; split_ifs with x; exact (lend p g k' i x).hasSum.tendsto_sum_nat; exact tendsto_const_nhds
 · let c:= tradew n x; let Y:= Scree.paintR false false c; unfold lasting zenS; rw [show visible P X D ((Lattice.gauge x i.1,threadG x i.2):Orbit n).1 ↔ visible P X D i.1 from visiL ..]; split_ifs with t
   · simp_rw [show ∀ j, F j (Lattice.gauge x i.1,threadG x i.2)= Y (F j i) from fun j=>(p j).gaugeX i x]; exact (Y.toLinearMap.toContinuousLinearMap.hasSum ((lend p g k' i t).hasSum)).tsum_eq
   exact (map_zero _).symm
lemma vaut : Medal P X D (lasting P X D F) h (∑' i,u i):=by
 choose C v x y using fun i=>(p i).pays
 have ht':0 ≤ h:=zero_le_one.trans k'
 have hv : Summable C:=by
    rw [Pi.summable]; intro i
    refine g.of_nonneg_of_le (fun j=> v _ _) fun j=> ?_
    apply le_trans (le_trans (Rue.sheen (v j) i) _) (y j)
    exact sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (one_le_pow₀ k') (v j i)
 refine ⟨tsign p g k',∑' i,C i,fun i=>by rw [tsum_apply hv]; exact tsum_nonneg (fun j=>v _ _),fun i t Z m=> ?_,?_ ⟩
 · let K:= lasting P X D F
   let Y(x):= pressQ P Z i.1 x
   refine ⟨Eventually.of_forall (fun x=>(fineShape _).allP),fun a=>?_ ⟩
   let L₀:Cipher n→ₗ[ℝ]ℂ:={toFun:=fun i=> crumb i.val a, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
   let L:= L₀.toContinuousLinearMap; let A(j:ℕ)(U:Pane n):= L (F j (U,i.2)); have hy:= Pi.summable.mp hv a
   obtain ⟨V,e,q⟩:= reach_p (Y:=Z) t; have hx(j:ℕ)(u:Pane n)(v:pingS P.threshold (X\D) u):Pence P.order (fun i':DN=> A j (pressQ P Z u i')) 0 (C j a):=(x j (u,i.2) v m).haveP _
   have hr:∀ᶠ k in 𝓝 (0:DN),∀ j:ℕ,Allows P.order (A j ∘ Y) k (V*C j a):=q.mono fun k z j=> z (A j) (C j a) fun _=>hx j _
   rw [tsum_apply hv]; apply Pence.germ (Rue.punch hr (hy.mul_left _) hy (fun j=>hx j i.1 t)); filter_upwards [tick (Y:=Z) t] with j p'; change (∑' m,A m (Y j))= L (K (Y j,i.2)); unfold K lasting zenS; rw [if_pos (show visible P X D _ from hates p')]; exact (L.hasSum ((lend p g k' (Y j,i.2) (hates p')).hasSum)).tsum_eq
 let L: (Ink n)→ₗ[ℝ] ℝ := ⟨⟨joinV (stake h),fun _ _=>joinVadd ..⟩,fun i j=>by simp [joinV,smul_eq_mul,mul_left_comm, Finset.mul_sum]⟩
 exact hasSum_le y (L.toContinuousLinearMap.hasSum hv.hasSum) g.hasSum
end YM.CF.Vow
