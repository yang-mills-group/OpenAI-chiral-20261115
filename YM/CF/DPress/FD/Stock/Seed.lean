import YM.CF.DPress.FD.Law.Fort
import YM.CF.DPress.FD.Warp.Raw
import YM.CF.Skye.Pine
import Mathlib.Probability.Kernel.Representation
/-!
 Transform minimum uniform priority in every component, using the real/SU/Sweep tags of the
 regulator, no extra draws allocated to Loom. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Filter Lattice Cash Deck Skye MeasureTheory ProbabilityTheory unitInterval SU Cube
open scoped Topology BigOperators ENNReal NNReal Classical unitInterval Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}
namespace Seed
abbrev ℐ:= Set.Icc (0:ℝ) 1
abbrev Stage(n:Side):= Seat n→ I
abbrev heightLaw(n:Side): Measure (Stage n):= Measure.pi (fun _:Seat n=>volume)
def step(k:ℕ)(x:I):I:=σ ((σ x)^k) -- pow exists?
lemma step_v(k:ℕ)(x:I): (step k x).val = 1-(1-x.val)^k:=by unfold step; simp
@[fun_prop] lemma stepC(k:ℕ): Continuous (step k):=by apply Continuous.subtype_mk; fun_prop -- actual val notation tactic conv
lemma step_p(k:ℕ)(h:0<k): StrictMono (step k):= by
 intro x y p; have hb: (y.val:ℝ) ≤ 1:=y.property.2; change (step k x).val < (step k y).val; rw [step_v,step_v]; apply sub_lt_sub_left (pow_lt_pow_left₀ (sub_lt_sub_left (show x.val< y.val from p) 1) (sub_nonneg.mpr hb) (Nat.ne_of_gt h)) -- signature
lemma step_sur (k:ℕ)(h:0 < k): Surjective (step k):=by
 intro y; have hx := (intermediate_value_univ 0 1 (stepC k)); have ht: step k 0=0:=Subtype.ext (by change ((step k 0:I):ℝ) = 0; rw [step_v]; simp); have hv:step k 1=1:=Subtype.ext (by change ((step k 1:I):ℝ) = 1; rw [step_v]; simp [Nat.ne_of_gt h]); exact hx (a:=y) (show y ∈ Icc (step k 0) (step k 1) from (by rw [ht,hv]; exact ⟨y.property.1,y.property.2⟩)) -- binder
lemma spice (k:ℕ)(x:I): volume (Ici (step k x)) = (volume (Ici x))^k:=by simp only [unitInterval.volume_Ici]; rw [step_v,sub_sub_cancel,ENNReal.ofReal_pow]; exact sub_nonneg.mpr x.property.2
variable (S:Support (More n))(z: Stage n)
abbrev pri(z: Stage n) := fun y:Seat n=> (z y).val
def pick : I:= z (greet S (pri z))
lemma pick_m : Measurable (pick S) := mealM (F:=fun z:Stage n=>greet S (pri z)) (fun i=> ((mastM S).comp (measurable_pi_lambda _ (fun i=> measurable_subtype_coe.comp (measurable_pi_apply i)))) (measurableSet_singleton _)) (G:=fun i (z:Stage n)=> z i) (fun i=> measurable_pi_apply _)
lemma peek (h:S.Nonempty):∃ i∈ S,z i= pick S z∧ ∀ j∈ S,pick S z ≤ z j:= ⟨_,(mastP _ h (pri z)).1,rfl,(mastP S h (pri z)).2⟩ -- tune cast
lemma principal (h:S.Nonempty): MeasurePreserving (step S.card ∘ pick S) (heightLaw n) volume:=by
 let k:=S.card; let f:=step S.card; let g:=pick S; have hx:0<S.card:=Finset.card_pos.mpr h; have ht: Measurable (f ∘ g):= (stepC _).measurable.comp (pick_m _)
 refine ⟨ht,Measure.ext_of_Ici _ _ ?_⟩; intro y; obtain ⟨a,rfl⟩:=step_sur k hx y; rw [Measure.map_apply ht measurableSet_Ici, spice]; let P:= pi (S:Set (Seat n)) (fun i=>Ici a); have he: (f ∘ g) ⁻¹' Ici (f a)=P:=by
    ext x; change f a ≤ f (g x) ↔ ∀ i∈ S, _ -- tune
    obtain ⟨i,v,t,p⟩:=peek S x h; rw [(step_p k hx).le_iff_le]; exact ⟨fun r i t=> le_trans r (p i t),fun r=> (show a≤g x from (le_trans (show a ≤ x i from r i v) t.le))⟩
 rw [he,heightLaw,Measure.pi_pi_finset]; simp [k] -- tune implicit change P
variable {J:Type*}[MeasurableSpace J][Fintype J][MeasurableSingletonClass J]
-- all sets (including empty, not used). Seed is callable on min Real 
lemma uniform(T: Cash J):∃ F:ℕ→ℝ→J,(∀ k,Measurable (F k))∧∀ S:Support (More n),S.Nonempty→ MeasurePreserving (fun z:Stage n=>F S.card (pick S z)) (heightLaw n) T.PM:=by
 letI: Nonempty J:= ok T; letI: DiscreteMeasurableSpace J:= ⟨ fun s=>s.to_countable.measurableSet⟩; obtain ⟨g,h,v⟩:= T.PM.exists_measurable_map_eq; let Q(k:ℕ)(x:ℝ):J:= if p:x∈ I then g (step k ⟨x,p⟩) else g 1
 refine ⟨Q,fun k=> ?_,?_⟩; · exact Measurable.dite (h.comp (stepC _).measurable) (g:=fun _:↑((I:Set ℝ)ᶜ)=>g 1) measurable_const measurableSet_Icc -- tune binder
 intro S p; rw [show (fun z:Stage n=>Q S.card (pick S z))=(g∘ step S.card) ∘ pick S from ?_]; exact (show MeasurePreserving g volume T.PM from ⟨h,v⟩).comp (principal S p); funext y; unfold Q; rw [dif_pos (pick S y).property]; rfl
end Seed
end YM.CF.DPress.FD
