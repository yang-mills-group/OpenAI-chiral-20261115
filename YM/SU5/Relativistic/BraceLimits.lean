import YM.SU5.Relativistic.EnvelopSmear
import YM.SU5.Relativistic.CarChain

/-! # Strong limits of groups with projected inputs
-/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
lemma moves_still {H:Hilbert} (G:ℕ→ H.Op) (p: ∃ B:ℝ,∀ i,‖G i‖ ≤ B)(f:ℕ→H){x y:H}(h:Tendsto f atTop (𝓝 x))(t:Tendsto (fun n=>G n x) atTop (𝓝 y)): Tendsto (fun i=>G i (f i)) atTop (𝓝 y):=by
 apply tendsto_of_tendsto_of_dist t
 obtain ⟨B,w⟩:= p
 have g:Tendsto (fun i=> B*dist (f i) x) atTop (𝓝 0):= by simpa only [mul_zero] using (tendsto_iff_dist_tendsto_zero.mp h).const_mul B
 apply squeeze_zero' (Eventually.of_forall fun _=> dist_nonneg) ?_ g
 apply Eventually.of_forall; intro n
 rw [dist_comm, dist_eq_norm,dist_comm,dist_eq_norm] -- tune
 rw [←map_sub]; exact ((G n).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (w n) (norm_nonneg _)).trans_eq (by rw [norm_sub_rev]))
section gate
variable {H:Hilbert}{M:Mesh}{j:Axis}(P:Sunbelt j (marks M) H)(E:OS.Semigroup H j)
variable (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z))
local notation "L"=> P.track.Realm P.list
local notation "X₀"=> P.track.aviator P.list
local notation "π"=> P.track.stackS P.list
local notation "G₀"=> glass P (daylight M) E e

lemma brace_limits {I:Type*}(b:Stamp M)(l:List I)(v:I→ Slab M)(F:ℕ→ I→H.Op)(G:I→ (P.track.Realm P.list).Op)(x:L)(h:∀ a∈ l,∀ y:L,Tendsto (fun i=>F i a y.val) atTop (𝓝 ((G a y:X₀).val:H))) (p:∀a∈l, ∃ B:ℝ,∀i,‖F i a‖≤ B):
    Tendsto (fun i=>bracing E.E v (F i) b l x.val) atTop (𝓝 (((bracing (G₀).E v G b l x): X₀).val : H)):=by
 induction l generalizing b with
 | nil=> simp only [bracing]; exact tendsto_const_nhds
 | cons j l ih=>
    simp only [bracing]; simp only [ContinuousLinearMap.mul_apply]
    let f:=v j; let g:=heatGap b f.lower; change Tendsto _ _ (𝓝 (E.E g (((G j) _ : X₀).val:H)))
    refine (E.E g).continuous.continuousAt.tendsto.comp ?_
    exact moves_still (fun i=>F i j) (p j List.mem_cons_self) _ (ih f.upper (fun i t=>h i (List.Mem.tail _ t)) (fun i t=>p i (List.Mem.tail _ t))) (h j List.mem_cons_self _)
lemma charged_limits {I:Type*}(b: Stamp M)(l:List I)(S T:I→ Slab M)(F:I→ Packet M)(B:I→ H.Op)(x:P.track.Realm P.list):
    Tendsto (fun i:ℕ=> bracing E.E T (fun z=> collecting P E (B z) (S z) (T z) (F z) (i-(F z).size)) b l x.val) atTop (𝓝 (((bracing (glass P (daylight M) E e).E T (fun z=> envelop P E e (B z) (S z) (T z) (F z)) b l x):P.track.aviator P.list).val:H)):=by
 apply brace_limits P E e b l T (fun i a=> collecting P E (B a) (S a) (T a) (F a) (i-(F a).size))
 · intro a _ x'; have hf:= (envelop_price P E e (B a) (S a) (T a) (F a) x').comp (tendsto_sub_atTop_nat (F a).size); exact hf
 intro a ha; obtain ⟨C,r,t⟩:= (F a).span_score; exact ⟨C*‖B a‖,fun n=> collecting_worth P E (B a) (S a) (T a) (F a) t _⟩
end gate
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.charged_limits
