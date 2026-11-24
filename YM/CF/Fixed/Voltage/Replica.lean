import YM.CF.Fixed.Voltage.Surgery
/-!
Surgery requires CONTINUOUS refund to carry all parent sparse costs along slight tilt. Section over femionic activity witness; no openness in large volume implied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Fixed.Voltage
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
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Collection
open Trees Salt Beau Push.BetaTransport Reef
variable{n:Side} {x Δ e d k v w:ℝ}{L:ℕ}
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(hp:Geo.Width P q σ)(ht:1 ≤ w)(r: Rare R)
open Haro
variable {S:Finset (Scree.Hub n)}{F:InkD n}
lemma orbit_smul (c:ℝ)(F:Cipher n):orbitPH (c • F)= c • orbitPH F:=by
    ext x y; change Prism.portB _ _ _= c • Prism.portB F.val _ _; simp only [Prism.port_eq]; split; exact (smul_zero _|>.symm); change (_:ℂ)*(c • _)= _; rw [Algebra.mul_smul_comm]; rfl -- tune crumb & error direction
abbrev frame_P (S:Finset (Scree.Hub n)): RegBudget n→ₗ[ℝ] Op (Single n):= {
 toFun:=fun F=> StackL F S, map_add':=fun f g=> mark_T S f g,
 map_smul':=fun c f=> by unfold StackL; simp_rw [RingHom.id_apply, smul_sum,Pi.smul_apply,orbit_smul] }
variable {I:Type}[TopologicalSpace I]
lemma wake_p(F:I→ RegBudget n)(S:Finset (Scree.Hub n))(h:LampF F): Continuous (fun i=> StackL (F i) S) := by unfold StackL; refine continuous_finsetSum _ fun i _=>seatC.comp (h i 1)
lemma lamp_smul(Z:I→ℝ)(F:I→ RegBudget n)(p:Continuous Z)(h:LampF F): LampF (fun i=> Z i • F i):=by intro o x; simp_rw [Pi.smul_apply]; exact p.smul (h o x)
lemma lamp_add(F G:I→ RegBudget n)(h:LampF F)(g:LampF G): LampF (fun i=> F i+G i):=by intro x o; simp_rw [Pi.add_apply]; exact (h x o).add (g x o)
lemma lamp_sub(F G:I→ RegBudget n)(h:LampF F)(g:LampF G): LampF (F-G):=by intro x o; simp_rw [Pi.sub_apply]; exact (h x o).sub (g x o)
lemma lamp_rank(F:I→ RegBudget n)(U:Pane n)(p:LampF F):Continuous (fun v=> exponentL P (F v) U):=by
 unfold exponentL; apply continuous_finsetSum; intro i _; unfold numbE; by_cases h:pingS P.threshold i.val.2 U <;> simp_rw [Set.indicator_apply]; · simp_rw [Set.mem_setOf, if_pos h]; exact p i U
 simp_rw [Set.mem_setOf,if_neg h]; exact continuous_const
lemma lamp_fuel(F:I→ ForceBudget n)(p:∀ i:Scree.Force n,∀ U,Continuous fun x=>F x i U)(U:Orbit n):Continuous fun c=> fueled P (F c) U:=by
 unfold fueled; apply continuous_finsetSum; intro i _; split; swap; exact continuous_const
 apply continuous_finsetProd; intro j _; unfold Scree.clamp; split; exact p j U; exact continuous_const
-- universal range
private noncomputable def bin_P(P:BudgetPoint)(L:ℕ)(n:Side)(t:1 ≤ w): Submodule ℝ (RegBudget n) where
 carrier:= {x|∃ b:ℝ,Lord P x b w L}
 zero_mem':= ⟨0,Lord.empty⟩
 add_mem':=by rintro x y ⟨u,v⟩ ⟨s,t'⟩; exact ⟨_,v.merge (zero_le_one.trans t) t'⟩
 smul_mem':=by rintro a x ⟨b,u⟩; exact ⟨_,u.scale (zero_le_one.trans t) a⟩
local notation "T"=> bin_P P L n ht
local notation "O"=> Op (Single n)
include ht
private lemma section_L(S:Finset (Scree.Hub n)): let H:=(LinearMap.range ((frame_P S).comp (bin_P P L n ht).subtype)); ∃ (F:H→ RegBudget n) (c: H→ℝ), c 0=0∧ Continuous c∧ LampF F∧∀ z:H, Lord P (F z) (c z) w L∧ StackL (F z) S=z.1 :=by
 intro H; let h:=(frame_P S).comp (T).subtype; have hf(S : Submodule ℝ O) : FiniteDimensional ℝ S:=inferInstance; have hu(S : Submodule ℝ O): Module.Free ℝ S:=inferInstance; letI := hu H; letI := hf H; let U:= Module.finBasis ℝ H; let J:=Fin (Module.finrank ℝ H); choose f hf using fun i:J=>(U i).property; choose Z hz using fun i:J=> (show ∃ z:ℝ,Lord P (f i).val z w L from (f i).property)
 let Q(t:H)(i:J):ℝ:= U.coord i t; let c(t:H):=∑ i:J, |Q t i| * Z i; have hc(i):Continuous fun t:H=>Q t i:= (U.coord i).continuous_of_finiteDimensional;
 refine ⟨(fun t=>∑ i:J,Q t i • (f i).val),c,by simp [c,Q],continuous_finsetSum _ (fun i _=> (hc i).abs.mul continuous_const),?_,fun z=>⟨Lord.pileL (P:=P) (zero_le_one.trans ht) _ (fun j:J=>Q z j • (f j).val) _ (fun i _=> (hz i).scale (zero_le_one.trans ht) _),?_⟩⟩
 · intro o s; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact continuous_finsetSum _ fun i _=> (hc i).smul continuous_const
 change frame_P S (_)=_; rw [map_sum]; simp_rw [map_smul,show ∀ i,frame_P S (f i).val=(U i).val from hf]; have hx:=congrArg Subtype.val (U.sum_repr z); rw [Submodule.coe_sum] at hx; exact hx -- adjust coe_sum
lemma spark_R(S:Finset (Scree.Hub n))(F:I→ RegBudget n)(p:LampF F)(g:∀ t:I,∃ b,Lord P (F t) b w L): ∃ (X:I→ RegBudget n)(c:I→ℝ),Continuous c ∧ LampF X∧∀ t:I, Lord P (X t) (c t) w L∧StackL (X t) S= StackL (F t) S ∧ (StackL (F t) S=0 → c t=0) :=by
 let H:=(LinearMap.range ((frame_P S).comp (T).subtype)); let V(t:I):H:=⟨StackL (F t) S, by exact ⟨ ⟨F t, g t⟩,rfl⟩⟩; obtain ⟨F,G,hZ,yp,hψ,hS⟩:= section_L (L:=L) P ht S; let X:=F∘ V; refine ⟨X,G∘V,yp.comp (Continuous.subtype_mk (wake_p _ S p) _), fun o x=>(hψ o x).comp (Continuous.subtype_mk (wake_p _ S p) _),fun t=>⟨(hS _).1,(hS _).2,fun h=> (by rw [comp_apply,show V t= 0 from Subtype.ext h,hZ])⟩⟩
end YM.CF.Fixed.Voltage
