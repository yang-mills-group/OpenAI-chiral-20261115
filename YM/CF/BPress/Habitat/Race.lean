import YM.CF.BPress.Sea.Voice
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
/- Journey dynamic pose. All paths carry stored continuation (time outside [0,2], clamped beyond [-1,3]); prices require variation comparison only on statutory interval. Derivative store allowed, not requiring all X have made turbine. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial Scroll Thera Meadow Topology
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
abbrev Track := ↥(Set.Icc (-1:ℝ) 3)
abbrev Rail0:= ↥(Set.Icc (0:ℝ) 2)
abbrev Upled (I:Type)[Fintype I][DecidableEq I]:= ContinuousMap Track (Op I)
scoped instance : Nonempty Track:= Set.nonempty_Icc_subtype (by norm_num)
scoped instance : Nonempty Rail0:= Set.nonempty_Icc_subtype (by norm_num)
variable {I:Type}[Fintype I][DecidableEq I]
scoped instance pledgeM (I:Type)[Fintype I][DecidableEq I]: MeasurableSpace (Upled I):= borel _ -- meas builder
scoped instance pledgeB (I:Type)[Fintype I][DecidableEq I]: BorelSpace (Upled I):= ⟨rfl⟩
lemma salute {D:Type*}[MeasurableSpace D](f:D→ Upled I)(h:∀ x:Track, Measurable (fun i=>(f i) x)): Measurable f:=by
 let b:=TopologicalSpace.denseSeq Track; let G(u: Upled I)(i:ℕ):=u (b i); haveI : SecondCountableTopology (Op I):=inferInstance; haveI : BorelSpace (Op I):=inferInstance; haveI : BorelSpace (ℕ → Op I):= Pi.borelSpace; haveI : MeasurableSpace.CountablyGenerated (ℕ→Op I):= BorelSpace.countablyGenerated; haveI : MeasurableSpace.SeparatesPoints (ℕ→Op I):=inferInstance; refine MeasurableEmbedding.measurable_comp_iff (g:=G) ?_ |>.mp (measurable_pi_lambda (fun i:D=>(G (f i))) (fun i=> h (b i))); apply Measurable.measurableEmbedding; swap; · intro p q g; exact ContinuousMap.coe_injective ((TopologicalSpace.denseRange_denseSeq Track).equalizer p.continuous q.continuous g)
 exact measurable_pi_lambda G fun i=> (show Continuous (fun u: Upled I=>u (b i)) by fun_prop).measurable
namespace Upled
def tap(t:ℝ): Track:= Set.projIcc (-1) 3 (by norm_num) t
lemma taps(t:Track): tap t.val=t:= by apply Subtype.ext; simp only [tap,Set.coe_projIcc,min_eq_right t.property.2,max_eq_right t.property.1]
lemma tap_v {t:ℝ}(v:t∈ Set.Icc (-1:ℝ) 3): (tap t).val=t:=congrArg Subtype.val (taps (⟨_,v⟩:Track))
abbrev decode (f:Upled I)(t:ℝ): Op I:= f (tap t)
def priceZone(f: Upled I) : ContinuousMap Rail0 (Op I):= ⟨fun x=> f.decode x.val, f.continuous.comp (continuous_projIcc.comp continuous_subtype_val)⟩ -- `Upled` abbrev field notation works?
lemma decode_c : Continuous (fun x:Upled I ×ℝ=> decode x.1 x.2):= continuous_eval.comp (f:=fun x:Upled I ×ℝ=> (x.1, tap x.2)) (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))
def δFee(f g:Upled I):=dist (priceZone f) (priceZone g)
lemma supPrice (f g:Upled I)(a:ℝ): δFee f g ≤ a ↔ ∀ v∈Set.Icc (0:ℝ) 2,‖f.decode v-g.decode v‖≤a:= by rw [δFee, ContinuousMap.dist_le_iff_of_nonempty]; constructor; intro t v h; rw [← dist_eq_norm]; exact t (⟨v,h⟩: Rail0); intro t v; rw [dist_eq_norm]; exact t v.val v.property
private def adapt {Y:Type}[TopologicalSpace Y](F:Y × Op I→ Op I)(h:Continuous F)(x:Y)(f:Upled I): Upled I:= ⟨fun t=> F (x, f t), h.comp (continuous_const.prodMk f.continuous)⟩
private lemma adapt_c{Y:Type}[TopologicalSpace Y](F:Y × Op I→ Op I)(h:Continuous F): Continuous fun x:Y×Upled I=> adapt F h x.1 x.2:=ContinuousMap.continuous_of_continuous_uncurry _ (h.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))
def dial(x:E)(f:Upled SU.Slot): Upled SU.Slot:=adapt (fun t:E × Op SU.Slot=> swivelC t.1 t.2) swivel_cont x f
lemma dial_c : Continuous (fun x:E× Upled SU.Slot=> dial x.1 x.2):= adapt_c _ _
lemma dial_seq(x y:E)(f:Upled Slot): dial x (dial y f)=dial (x*y) f:= by apply ContinuousMap.ext; exact fun h=>(Paint.turn_add x y (f h)).symm
lemma dial_one(f:Upled Slot): dial 1 f=f:=by apply ContinuousMap.ext; intro i; exact Paint.turn_one (f i)
lemma dialCost(x:E)(f g:Upled Slot): δFee (dial x f) (dial x g)= δFee f g:=by
 suffices h:∀ c:ℝ, δFee (dial x f) (dial x g)≤ c↔ δFee f g≤ c from le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)
 intro c; rw [supPrice, supPrice]; exact forall_congr' fun i=> forall_congr' fun _=> by change (‖swivelC x _-swivelC x _‖≤c)↔_; rw [Paint.iso]
end Upled
end YM.CF.BPress.Habitat
