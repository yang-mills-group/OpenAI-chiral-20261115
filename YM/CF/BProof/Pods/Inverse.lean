import YM.CF.BProof.Pods.Motion

/-! formulations of θ extended to Marked projections in Sphere. Borel. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Pods.Brick
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open House Cube Lat Wilson Skye Charge Gauss Garden Pricing
open scoped Topology BigOperators Classical ENNReal Hearth
variable {m N:Side}(Y:Yard (More N))(g:Ratio m (More N))(y:ℝ)
local notation "B"=> Block Y m
open Manual
def nick(x:Sphere Y) : Disney Y:= ((gets Y x.1.mood,(cart Y).symm x.1.sev), (x.1.gap,curry x.1.gauss,x.1.dust,x.2))
@[fun_prop] lemma nick_m : Measurable (nick Y):=by
 apply Measurable.prodMk; · exact ((show Measurable (gets Y) from measurable_of_countable ..).comp ((Pawn.mood_m Y).comp measurable_fst)).prodMk ((measurable_of_countable _).comp ((Pawn.sev_m Y).comp measurable_fst))
 apply Measurable.prodMk ((Pawn.gap_m _).comp measurable_fst); apply Measurable.prodMk; swap; · apply Measurable.prodMk ((Pawn.dust_m _).comp measurable_fst) measurable_snd
 apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j; exact (measurable_pi_apply (i,j)).comp ((Pawn.gauss_m Y).comp measurable_fst)
lemma box_nick (x:Sphere Y)(p: Manual.Marked Y x.1.mood): box Y (nick Y x)=x:=by
 unfold nick Manual.box Payment.wrap; simp only [lots, Manual.code, (cart Y).apply_symm_apply, ruling Y x.1.mood p]; rfl
lemma nick_box(x:Disney Y) : nick Y (box Y x)=x:=by
 unfold nick Manual.box Payment.wrap; simp only [gets_m (Y:=Y),lots,Manual.code,(cart Y).symm_apply_apply]; rfl

def invert (x:Sphere Y):= (fieldTotal Y g).symm (nick Y x)
lemma money(x: Static Y g): invert Y g (flats Y g x)= x:=by unfold invert flats; rw [nick_box,MeasurableEquiv.symm_apply_apply]
lemma field_eq (x:Sphere Y)(p:Manual.Marked Y x.1.mood): flats Y g (invert Y g x)=x:=by rw [invert,flats,MeasurableEquiv.apply_symm_apply,box_nick Y x p]
def adapt (f:Static Y g→ℂ)(x:Sphere Y):= if Manual.Marked Y x.1.mood then f (invert Y g x) else 0
lemma adapt_m(F:Static Y g→ℂ)(f:Envelope F): Envelope (adapt Y g F):= by
 have hp:Envelope (F ∘ invert Y g):= Law.pull f ((fieldTotal Y g).symm.measurable.comp (nick_m ..)); refine ⟨hp.meas.ite ?_ measurable_const,max 0 hp.cost.choose,fun x=>?_⟩
 · change MeasurableSet ((fun x:Sphere Y=> x.1.mood) ⁻¹' {i|Manual.Marked Y i}); exact (Pawn.mood_m Y).comp measurable_fst (Set.Countable.measurableSet (Set.to_countable _)) -- tune
 unfold adapt; split; exact (hp.cost.choose_spec x).trans (le_max_right ..); rw [norm_zero]; exact le_max_left ..
lemma beneath(F:Static Y g→ℂ)(x:Static Y g) : adapt Y g F (flats Y g x)= F x:=by rw [adapt,if_pos (Act.marked Y g x),money]
end YM.CF.BProof.Pods.Brick
