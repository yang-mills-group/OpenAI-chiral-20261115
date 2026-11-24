import YM.CF.BPress.Sugar.Tool
import YM.CF.BPress.Mount.Mounting
/-! Measurable stage. definitional partition, no branchwise continuity claims. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Sugar
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N:Side}{B:BandWidth}{A:Bands (More N) B}(R:Hangar (More N))
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage
section utility
variable {I X Y:Type}[MeasurableSpace X][Countable I][MeasurableSpace I][MeasurableSingletonClass I][MeasurableSpace Y] (f:X→I)(p:Measurable f)
include p
lemma askC (u:I→X→Prop)(h:∀ i, MeasurableSet {x| u i x}):MeasurableSet {x|u (f x) x}:=by
 rw [show {x|u (f x) x}= ⋃ i:I, (f ⁻¹' {i})∩ {x|u i x} from ?_]; exact MeasurableSet.iUnion fun i=>(p (measurableSet_singleton i)).inter (h i); ext x; simp -- tune
lemma askM (g:I→X→Y)(h:∀ i,Measurable (g i)): Measurable fun x=> g (f x) x:= by intro s h'; exact askC f p (fun i x=> g i x∈s) (fun i=> h i h')
end utility
section Finite
variable {I X:Type}[MeasurableSpace X][Fintype I][MeasurableSpace I][MeasurableSingletonClass I](f:X→Finset I)
lemma askF(p:∀ i,MeasurableSet {x|i∈ f x}):Measurable f:= by
 intro s _; rw [show f ⁻¹' s = ⋃ i:s, f ⁻¹' {i.val} from ?_]; swap; · ext x; simp
 apply MeasurableSet.iUnion; intro i; change MeasurableSet {x| f x=i.val}; rw [show {x| f x=i.val}= ⋂ a:I, if a∈i.val then {x| a∈ f x} else {x|a∈f x}ᶜ from ?_]; exact MeasurableSet.iInter fun a=>by split; exact p _; exact (p _).compl
 ext x; simp only [Set.mem_setOf,Set.mem_iInter,Finset.ext_iff]; apply forall_congr'; intro a; split <;> simp_all
end Finite
namespace Crew
variable (H:Crew A)
local notation "η" => mState N A
lemma Sbudget : Measurable (fun i:η=>i.1.1):=by fun_prop
abbrev skyio (i:η):= centerSky A H.F i.1.1 i.2.1 H.y
lemma skyio_m : Measurable H.skyio:=by
 unfold skyio; apply askM (fun i:η=>i.1.1) Sbudget (fun a:Seal A.Hcols=>fun x:η=> centerSky A H.F a x.2.1 H.y); intro i; exact ((heart A).symm.measurable.comp (body_meas ..)).comp (measurable_fst.comp measurable_snd) -- tune
lemma layoutP : Measurable (layout (A:=A)):= (measurable_of_countable (fun v:Old A=> flash A v.2)).comp measurable_fst
lemma port_m : Measurable (H.port):=by
 let k(i:η):= i.2.2.1; have ht: Measurable k:= measurable_fst.comp (measurable_snd.comp measurable_snd); exact askM (layout (A:=A)) layoutP (fun i p=> H.Z.roll A i (H.skyio p) (k p)) (fun i=> (Net.roll_joint A H.Z i).comp (f:=fun q:η=> (H.skyio q,k q)) (H.skyio_m.prodMk ht))
lemma harbor_m : Measurable H.harborT:= H.port_m.prodMk (by fun_prop)
lemma prec_meas : MeasurableSet {x|Precinct A H.y x}:=by
 unfold Precinct Wealth.ToneNoise Barrel; simp only [Set.setOf_and,Set.setOf_forall]; apply MeasurableSet.inter; · exact MeasurableSet.iInter fun i=> measurableSet_le (group.continuous_chord.measurable.comp (f:=fun i':η=>i'.2.2.1 i) (by fun_prop)) measurable_const
 exact MeasurableSet.iInter fun i=> measurableSet_le (show Measurable (fun i':η=>‖i'.2.1.1 i‖) from (by fun_prop)) measurable_const
lemma Role_meas : MeasurableSet {x|H.Role x}:=by
 unfold Role House.Role holdsT; rw [Set.setOf_and]; apply H.prec_meas.inter; rw [Set.setOf_and]; apply MeasurableSet.inter
 · exact askC (fun i:η=>i.1.1) Sbudget (fun S i=> aware A H.κ H.y H.F S i.2.1) (fun i=>((measurable_fst.comp measurable_snd) (show MeasurableSet {x| aware A H.κ H.y H.F i x} from (by simp_rw [aware, eq_comm]; exact body_meas A H.y H.F i (pick_meas ..))))) -- tune
 exact askC (fun i:η=> flash A i.1.2) layoutP (fun i x=> i∈ A.permit H.T H.y (A.atmospheric (H.skyio x))) (fun i=> H.skyio_m ((Bands.atmospheric_meas A) (A.permit_meas H.T H.y i)))
-- beware Open spin namespace.Polish. Finsets measurable.Space chosen. Actual producer standard.
instance std : StandardBorelSpace (castP H):=by
 letI:DiscreteMeasurableSpace (Spire.Sweep N):= ⟨fun _=>trivial⟩; letI: StandardBorelSpace (Skye.Ids N):=inferInstance; letI: StandardBorelSpace η:=inferInstance; exact MeasurableSet.standardBorel (s:= {x|H.Role x}) H.Role_meas
variable (X:Stage N)
lemma stares_m : Measurable (H.unsea R):= by
 unfold unsea bawl BadCols; apply (measurable_of_countable (fun i:Finset A.Hcols=>i.image (own A R))).comp (f:=fun i:η=> BadCols A i.1.1 i.2.1.1 H.y); apply askF; intro i; simp only [BadCols,mem_filter,mem_univ,true_and, Port.rawBad, Set.setOf_or]; exact ((Sbudget (A:=A)) ((Set.to_countable _).measurableSet (s:={j:Finset A.Hcols | i∈j}))).union (measurableSet_le measurable_const (show Measurable fun x:mState N A=> ‖x.2.1.1 i‖ from by fun_prop)) -- tune
lemma flag_m : Measurable H.flag:=by
 apply askF; intro i; exact H.port_m (show MeasurableSet {x: Micro (More N)| i∈ flags (Pressure.temp H.y) x} from (RG.flags_open ..).measurableSet)
lemma areaC_m : Measurable (areaC R H X):=(measurable_of_countable (fun S:Seal (SiteX A R)=> specialB X.W A R S)).comp (H.stares_m R)
end Crew
end YM.CF.BPress.Sugar
