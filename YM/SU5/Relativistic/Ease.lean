import YM.SU5.Relativistic.Envelopes
import YM.SU5.Relativistic.NeedlePacket
/-! # Axial modulus on neighborhoods all-axis tiled. Ct where limits at d,u displacement. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
variable {H:Hilbert} {W:Type*}{F:Filter W}
-- infer Op enum from other data.
lemma stuff_mul {u v s t:W→ H.Op} {f:Filter W} (r:∃a:ℝ,∀ᶠ w in f, ‖v w‖ ≤ a)(p:∃b:ℝ,∀ᶠ w in f, ‖s w‖≤b) (h:Tendsto (fun w=> u w - v w) f (𝓝 0))(q:Tendsto (fun w=> s w - t w) f (𝓝 0)) :
    Tendsto (fun w=> u w*s w - v w*t w) f (𝓝 0):=by
 obtain ⟨b,w⟩:=p; obtain ⟨a,z⟩:=r
 apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _)
 swap
 · exact (show Tendsto (fun w=> ‖u w-v w‖*b + a*‖s w-t w‖) f (𝓝 0) from by simpa only [norm_zero,zero_mul,mul_zero,add_zero] using (h.norm.mul_const b).add (q.norm.const_mul a))
 filter_upwards [w,z] with i k v'
 rw [show u i * s i - v i * t i = (u i-v i)*s i+ v i*(s i-t i) by rw [_root_.sub_mul,mul_sub]; abel]
 exact (norm_add_le ..).trans (add_le_add ((norm_comp_cost ..).trans (mul_le_mul_of_nonneg_left k (norm_nonneg _))) ((norm_comp_cost ..).trans (mul_le_mul_of_nonneg_right v' (norm_nonneg _))))
section motion
variable {M:Mesh}{j:Axis}(P:Sunbelt j (marks M) H)(E: OS.Semigroup H j)
local notation "R" => Axis→ Stamp M
local notation "U" u:max=> P.track.raw P.list (fun i=> (u i.val : Stamp M))
variable (S T:Slab M) (B:H.Op) (u:Axis→ℝ)
variable (x y:W→ Axis→ Stamp M)
local notation "χ"=> nativeE P E B S T
lemma contributes (a:safely j S T u) (k:Tendsto (fun t i=>((x t i:Stamp M):ℝ)) F (𝓝 u))(p:Tendsto (fun t i=> ((y t i:Stamp M):ℝ)) F (𝓝 u))(h:∀ᶠ t in F,∀i:Axis,i≠ j→x t i = y t i):
    Tendsto (fun t=> χ (x t)-χ (y t)) F (𝓝 0):=by
  let G(u: Axis→Stamp M):= (U u)*B*(U (-u))
  have hp(u: Axis→Stamp M):‖G u‖ ≤ ‖B‖:=by unfold G; apply (norm_comp_cost ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (unorm P _)).trans; exact (norm_comp_cost ..).trans (mul_le_of_le_one_left (norm_nonneg _) (unorm P _))
  have ha:Tendsto (fun t=> G (x t)-G (y t)) F (𝓝 0):=by
     apply Tendsto.congr' ?_ tendsto_const_nhds
     filter_upwards [h] with t v
     have he: (U (x t))= U (y t):= misscost _ _ _ _ _ fun i _=>v _ i.property
     have hu: (U (-(x t)))= U (-(y t)):= misscost _ _ _ _ _ fun i _=> congrArg (fun x:Stamp M=> -x) (v i.val i.property)
     unfold G; rw [he,hu,sub_self]
  let A:=ahead j S T u; let V:= off j S T u
  have hA:0<A:= Real.toNNReal_pos.mpr (by have h:= a.1; linarith)
  have hV:0<V:= Real.toNNReal_pos.mpr (by have h:= a.2; linarith)
  let c:(Axis→Stamp M)→H.Op:= fun i=> E.E (heatGap T.lower (S.lower+i j))
  let d:(Axis→Stamp M)→H.Op:= fun i=> E.E (heatGap (S.upper+i j) T.upper)
  have he(z:W→Axis→ Stamp M)(p:Tendsto (fun t i=> ((z t i:Stamp M):ℝ)) F (𝓝 u)): Tendsto (fun i=> c (z i)) F (𝓝 (E.E A)) ∧ Tendsto (fun i=>d (z i)) F (𝓝 (E.E V)):= ⟨(norm_cont_area E hA|>.tendsto).comp ((continuous_ahead (j:=j) S T).continuousAt.tendsto.comp p), (norm_cont_area E hV|>.tendsto).comp ((continuous_off (j:=j) S T).continuousAt.tendsto.comp p)⟩
  obtain ⟨hc,hv⟩:= he x k; obtain ⟨hv',hl⟩:= he y p
  have hw(i): ‖c i*G i‖≤‖B‖:=(norm_comp_cost ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (E.shrinks _)).trans (hp i))
  change Tendsto (fun w => c (x w)*G _ * d (x w) - c (y w)*G _* d (y w)) F _
  apply stuff_mul (u:=fun i=>c (x i)*G (x i)) (v:=fun i=>c (y i)*G (y i)) (s:=fun i=> d (x i)) (t:=fun i=> d (y i)) ⟨_,Eventually.of_forall fun _=> hw _⟩ ⟨_,Eventually.of_forall fun _=> E.shrinks _⟩
  · apply stuff_mul (u:=fun i=> c (x i)) (v:=fun i=> c (y i)) (s:=fun i=> G (x i)) (t:=fun i=> G (y i)) ⟨1,Eventually.of_forall fun _=> E.shrinks _⟩ ⟨_,Eventually.of_forall fun _=> hp _⟩ ?_ ha
    simpa [sub_self] using hc.sub hv'
  simpa [sub_self] using hv.sub hl
end motion
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.contributes
