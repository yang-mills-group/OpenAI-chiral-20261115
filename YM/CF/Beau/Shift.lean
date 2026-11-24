import YM.CF.Taxi.World
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
abbrev Hatch(P:BudgetPoint)(X:Support (More n))(v:Pane n): Prop:=pingS P.threshold X v
variable {F:ℕ→ Pane n → ℂ}{o: Skye.Seat n}{u:ℕ→ℝ}
local notation "Θ"=> P.threshold
local notation "N"=> P.order
local notation "S"=>Hatch P X
lemma ploy(V:Pane n)(i:DN): pressQ P ∅ V i=increment V (Θ • i):=by
 let L:= Θ • i; unfold pressQ gyrate; rw [Function.comp_apply]; apply congrArg; ext1 a; rw [steadyB, if_pos]; simp [unrest,Lattice.halo]
variable(p:∀ i:ℕ,∀ x:Pane n,Hatch P X x→ Signs P o (F i∘increment x) (u i))(g:Summable u)
include p
lemma yacht (w:Hatch P X U) : ∃ C:ℝ,0≤ C∧∀ᶠ x in 𝓝 (0:DN), ∀ i:ℕ, Jet.Allows N (F i∘increment U) x (C*u i):=by
 let L: DN→L[ℝ]DN:=Θ⁻¹ • ContinuousLinearMap.id ℝ DN
 have hp:S U:= w; obtain ⟨W,z,h⟩:= Vow.reach_p (Y:=∅) (D:=∅) (P:=P) (U:=U) (X:=X) (by rw [sdiff_empty]; exact w)
 let C:=‖L‖+1; refine ⟨composeCost N (W*((N+1:ℝ)* composeCost N 1 1)) C, (by unfold C composeCost; positivity),?_⟩
 have k:Tendsto L (𝓝 0) (𝓝 0):= by simpa only [map_zero] using L.continuous.tendsto 0
 have hx:∀ᶠ x in 𝓝 (0:DN), ‖L x‖ < 1:=k.eventually ((continuous_id.norm).isOpen_preimage (Set.Iio (1:ℝ)) isOpen_Iio |>.mem_nhds (show (0:DN)∈ _ from (by change ‖(0:DN)‖ < 1; norm_num)))
 let M:= pressQ P ∅ U
 filter_upwards [k.eventually h,hx] with a v l i
 have he:= v (F i) ((N+1:ℝ)*composeCost N (u i) 1) fun x t=>Rue.bare_p _ _ (debt_m (Y:=∅) (p i x (show Hatch P X x from by simpa only [sdiff_empty] using t)))
 let A:= (he.comp (f:=L) (allows_linear (by change ‖L‖≤ C; unfold C; linarith) (l.le.trans (le_add_of_nonneg_left (norm_nonneg _))))) -- tune
 have hh:M ∘ L=increment U:= funext fun a=> by rw [Function.comp_apply]; unfold M; rw [ploy]; exact congrArg _ (smul_inv_smul₀ P.threshold_pos.ne' a)
 refine (show Jet.Allows N (F i∘ (M∘ L)) a _ from A).germ (?_) |>.mono ?_ -- tune
 · rw [hh]
 unfold composeCost; exact le_of_eq (by ring)
-- differentiation with all. cost.u rooted
include g
abbrev ray(V:ℕ→ Pane n→ℂ)(i: Pane n):ℂ:=∑' j,V j i
lemma surf (w:Hatch P X U) : Chart N (ray F) U ∧ ∀ j:ℕ,j≤N→HasSum (fun i=> iteratedFDeriv ℝ j (F i∘ increment U) 0) (iteratedFDeriv ℝ j (ray F∘ increment U) 0) :=by
 obtain ⟨C,z,h⟩:=yacht p w
 let f(i):=F i ∘ increment U; let Y(i):= C*u i; let μ:= (Measure.count:Measure ℕ); obtain ⟨V,hV,r,t⟩:= _root_.mem_nhds_iff.mp h; have hp:Summable Y:=g.mul_left C; have he:Integrable Y μ:= integrable_count_iff.mpr hp.abs; have ht(i:DN)(v:i∈ V)(j:ℕ):Jet.Allows N (f j) i (Y j):=hV v j
 have hy(y:DN)(p:y∈V):Integrable (fun i=> f i y) μ:=integrable_count_iff.mpr (Summable.of_norm_bounded hp fun i=> by rw [norm_norm]; exact (ht y p i).value)
 have hm:= under (l:=r) (fun j y p=>(ht y p j).smooth) (fun y _=>StronglyMeasurable.of_discrete) he (fun j y p=>ht y p j)
 have hw: (fun i=>∫ j,f j i∂μ)=ᶠ[𝓝 0] ray F∘increment U:=by filter_upwards [r.mem_nhds t] with i p; rw [integral_countable (hy _ p)]; simp [μ]; rfl
 refine ⟨(hm.germ r t).congr_of_eventuallyEq hw.symm,fun j s=>?_⟩
 let A:=average μ f
 have hB:= hm.integrate t s; let Q(i:ℕ):= iteratedFDeriv ℝ j (f i) 0
 rw [←(hw.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]; change HasSum Q (iteratedFDeriv ℝ j A 0); rw [(show iteratedFDeriv ℝ j A 0= _ from (hm.less s).differentiate r t), integral_countable hB]; simp [μ]; exact ((integrable_count_iff.mp hB).of_norm).hasSum -- tune
lemma wayF(w:Hatch P X U): Signs P o (ray F ∘ increment U) (∑' i,u i) :=by
 obtain ⟨t,he⟩:=surf p g w
 refine ⟨tsum_nonneg (fun i=>(p i U w).grade),t,fun i v x l=>?_ ⟩
 let L:=ContinuousMultilinearMap.apply ℝ _ ℂ x; have h:=L.hasSum (he i v)
 -- norm bound by hasSum. use norm_tsum_of_norm hg. simpler
 let q(j:ℕ):=L (iteratedFDeriv ℝ i (F j∘ increment U) 0); have hp(j): ‖q j‖ ≤ u j:=(p j U w).token i v x l; have hv: Summable (fun i=> ‖q i‖):=g.of_nonneg_of_le (fun i=> norm_nonneg _) hp
 change ‖L _‖ ≤_; rw [show L _= (∑' i,q i) from h.tsum_eq.symm]; exact (norm_tsum_le_tsum_norm hv).trans (Summable.tsum_le_tsum hp hv g)
end YM.CF.Beau
