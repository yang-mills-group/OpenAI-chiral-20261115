import YM.SU5.Relativistic.Packet
import YM.SU5.Selected.CompassGlass
/-!
# Strong multiplications by envelopes. Proof entirely on the input gate, without modifying Outdoor.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
section gate
variable {H:Hilbert}{M:Mesh}{j:Axis}(P:Sunbelt j (marks M) H)(E:OS.Semigroup H j)
variable (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z))
local notation "A"=> P.track.aviator P.list
local notation "L"=> P.track.Realm P.list
local notation "P₀"=> (P.track.aviator P.list).orthogonalProjectionOnto
local notation "X"=> glass P (daylight M) E e
local notation "U" u:max=> P.track.raw P.list (fun i=> (u i.val : Stamp M))
local notation "π"=> P.track.stackS P.list
variable (B:H.Op)

lemma norm_comp_cost (f g:H.Op) : ‖f*g‖≤‖f‖*‖g‖:= ContinuousLinearMap.opNorm_comp_le ..

variable (S T:Slab M)
def ahead (i:Axis) (W W₀:Slab M)(u:Axis→ℝ) : ℝ≥0:= ((W.lower:ℝ)+u i-(W₀.lower:ℝ)).toNNReal
def off (i:Axis)(W W₀:Slab M)(u:Axis→ℝ): ℝ≥0:= ((W₀.upper:ℝ)-((W.upper:ℝ)+u i)).toNNReal
def nativeE (u:Axis→ Stamp M):H.Op := (E.E (heatGap T.lower (S.lower+u j))) * ((U u)*B*(U (-u))) * E.E (heatGap (S.upper+u j) T.upper)
def compressed : (P.track.Realm P.list).Op:= P₀|>.comp (B.comp (P.track.aviator P.list).subtypeL)
local notation "G"=> compressed P B
local notation "V" u:max=> ((X).U (diameter (a:=j) u))
def envelope (u:Axis→ℝ): (P.track.Realm P.list).Op := (X).E (ahead j S T u) * ((V u)*compressed P B*(V (-u))) * (X).E (off j S T u)
local notation "E₀"=> nativeE P E B S T
local notation "E₁"=> envelope P E e B S T
local notation "F"=> Axis→ℝ
-- intermediate ordering: bring U(u) outermost. On input Fort, U(-u) & E legitimate. Keeping remainder continuous into indoor.
def deliberate (v:P.track.Realm P.list) (u:Axis→ℝ): H:= E.E (ahead j S T u) (B (show H from (((V (-u)) ((X).E (off j S T u) v) : A).val)))
local notation "D"=> deliberate P E e B S T
lemma continuous_ahead : Continuous (ahead j S T):=by unfold ahead; fun_prop
lemma continuous_off : Continuous (off j S T):=by unfold off; fun_prop
lemma positiveCont {W: Type*}[TopologicalSpace W] (Y:W→H)(C:W→ℝ≥0)(p:Continuous Y)(q:Continuous C): Continuous (fun i=>E.E (C i) (Y i)):=by
  refine continuous_iff_continuousAt.mpr fun i=> Metric.tendsto_nhds.mpr fun ε e'=>?_
  have hp: Continuous (fun t=> E.E (C t) (Y i)):= (E.continuousE (Y i)).comp q
  filter_upwards [Metric.tendsto_nhds.mp (hp.tendsto i) (ε/2) (half_pos e'),Metric.tendsto_nhds.mp (p.tendsto i) (ε/2) (half_pos e')] with t hw hy
  apply lt_of_le_of_lt (dist_triangle _ (E.E (C t) (Y i)) _); refine (add_lt_add_of_lt_of_lt ?_ hw).trans_eq (add_halves _)
  rw [dist_eq_norm, ←map_sub]; exact ((E.E (C t)).le_opNorm _).trans_lt (lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (E.shrinks _)) (by simpa [dist_eq_norm] using hy))
lemma diameterCont : Continuous (diameter (a:=j)):= (OS.Semigroup.SEP j).continuous.comp (by fun_prop)
lemma deliberate_cont (v:L): Continuous (D v):=by
  let y(u:Axis→ℝ):L:= (X).E (off j S T u) v
  have h: Continuous y:= ((X).continuousE v).comp (continuous_off S T)
  apply positiveCont; swap; · exact continuous_ahead S T
  exact B.continuous.comp ((A).subtypeL.continuous.comp ((X).cont_cross y (fun u:Axis→ℝ=> diameter (-u)) h ((diameterCont (j:=j)).comp continuous_neg)))
lemma envelope_price (v:L) (u:Axis→ℝ) : (E₁ u) v = (V u) (P₀ (D v u)) := by
  let f:=off j S T u; let h:=ahead j S T u
  let w:L:= (V (-u)) ((X).E f v); let x:H:= B w.val
  have he : (X).E h (P₀ x)= P₀ (E.E h x) := by
     apply Subtype.ext
     change (E.E h) ((P₀ x).val:H)= (P₀ _).val
     have hu(z:H): (P₀ z).val= P.track.stackS P.list z:= by rw [stack_projection]; rfl
     simp_rw [hu]; rw [←ContinuousLinearMap.comp_apply,P.track.ground _ (E.E h) (fun i _ v=> e i v h)]; rfl
  change (X).E h ((V u) (P₀ x))=(V u) (P₀ (E.E h x)); rw [← ContinuousLinearMap.comp_apply,(X).independent,ContinuousLinearMap.comp_apply,he]
lemma envelope_cont (v:L): Continuous (fun u:Axis→ℝ=> (E₁ u) v):=by
 simp_rw [envelope_price]; exact (X).cont_cross _ _ ((P₀).continuous.comp (deliberate_cont P E e B S T v)) diameterCont
-- exact meshes. define explicit neg to avoid parentheses.
local notation "v↑" u:max=> (fun i:Axis => ((u i:Stamp M):ℝ)) -- syntax unicode bad? tune
lemma native_price (v:P.track.Realm P.list)(u:Axis→Stamp M) : E₀ u v.val = (U u) (D v (fun i:Axis=> (u i:ℝ))):= by
  let x:L:= (X).E (off j S T (v↑ u)) v
  have he : (U (-u)) (x.val:H)= (((X).U (diameter (-(v↑ u))) x:A).val:H):= (glass_move P (daylight M) E e x (-u)).symm -- defeq (-u) lifts
  let w := B ((U (-u)) x.val); let d:=heatGap T.lower (S.lower+u j)
  change E.E d ((U u) w) = (U u) (E.E d (B _)) -- tune
  rw [← ContinuousLinearMap.comp_apply, ← (P.track.hard P.list _ (fun i _ v=> e i v d) _),ContinuousLinearMap.comp_apply]; unfold w; rw [he]
lemma enmeshed (v:L) (u:Axis→Stamp M) : (((E₁ (fun i:Axis=> (u i:ℝ))) v:A).val:H)= (U u) (π (D v (fun i=> (u i:ℝ)))):=by
  rw [envelope_price,glass_move, stack_projection]; rfl
lemma envelope_zero (v:L):
    (E₁ 0) v= P₀ ((E₀ 0) v.val) := by
  have he: (U (0:Axis→Stamp M))=1:= P.track.raw_zero _
  apply Subtype.ext; rw [native_price P E e B S T v]; erw [show (0:Axis→ℝ)=(fun i:Axis => ((0:Axis→Stamp M) i:ℝ)) from rfl,enmeshed]
  rw [he]; rw [stack_projection]; rfl -- inspect

lemma unorm (u:Axis→Stamp M) : ‖U u‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> (raw_norm M _ _ _ _).le.trans_eq (one_mul _).symm
lemma native_cost (u:Axis→Stamp M) : ‖nativeE P E B S T u‖ ≤ ‖B‖:=by
 unfold nativeE
 apply (norm_comp_cost ..).trans; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (E.shrinks _)); apply (norm_comp_cost ..).trans
 apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (E.shrinks _)); apply le_trans (norm_comp_cost ..)
 apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (unorm P (-u))); exact (norm_comp_cost ..).trans (mul_le_of_le_one_left (norm_nonneg _) (unorm P u))
end gate
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.envelope_price
