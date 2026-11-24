import Merino.Shuttle
import Merino.Fenestral
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

open RG Skye Scree


variable {o:Seat n}{a b c e B W:ℝ}{p:BudgetPoint}{K:Loom n}{X:Oil n}

/-- Near identity in the untempered torus all inspections pass, in
particular this one. -/
lemma passes (A:StemA n):
    ∀ᶠ x in 𝓝 0, petals A x ∈ pass p o:=by
  have h:petals A 0 ∈ pass p o:=by
    rw [petal_idle]
    intro i _
    simp [faceValue,travel,square,Gauge.chord_one,p.threshold_pos]
  exact (cont_petal _).continuousAt.eventually (ping_o.mem_nhds h)



/-- Actual on the FIRST PANE. Scalar opening coefficient without external
normalization; includes all masks. -/
def display (A:StemA n)(p:BudgetPoint)(K:Loom n)(o:Seat n)(X:Oil n): ℝ→ℂ:=
  traceCost K p o X ∘ petals A

lemma displays (r:Skylit p e K)(h:Trunk o X (p.B/10) a b e)(ha:0≤a)(A:StemA n):
    display A p K o X =ᶠ[𝓝 0] glaze A X:=by
  filter_upwards [passes (p:=p) (o:=o) A,petals_open r.pos A] with t g f
  exact congrArg Matrix.trace (mask_extension r ha h g f fun _ _ _=>rfl)


/-- Actual physical scalar fee. `full` unmasked full block response, `fee`
corresponding masked short-lookup through the Loom. Estimates current
fee against full through true derivatives at zero, inclusive lower
for fee (using no degree-three bound). -/
structure Regalia (full fee:ℝ→ℂ)(δ error:ℝ):Prop where
 source : Bud full
 test : Bud fee
 faithful(k): ‖bud fee k - bud full k‖ ≤ error
 weight: δ < (bud fee 2).re

lemma Regalia.scale {full fee:ℝ→ℂ}{δ g q:ℝ}
    (h:Regalia full fee δ g)(hl:0<q):
    Regalia ((q:ℂ) • full) ((q:ℂ) • fee) (q*δ) (q*g):=by
  have e:=h.source.bloom.scale q; have t:=h.test.bloom.scale q
  refine ⟨e.1,t.1,fun k=>?_,?_⟩
  · rw [show bud ((q:ℂ) • fee)=_ from t.bud_eq, show bud ((q:ℂ) • full)=_ from e.bud_eq]
    rw [Pi.smul_apply,Pi.smul_apply,←smul_sub,norm_smul,Complex.norm_of_nonneg hl.le]
    exact mul_le_mul_of_nonneg_left (h.faithful k) hl.le
  rw [show bud ((q:ℂ) • fee)=_ from t.bud_eq,Pi.smul_apply, smul_eq_mul,Complex.re_ofReal_mul]
  exact mul_lt_mul_of_pos_left h.weight hl

lemma glaze_price (r:Skylit p e K)(h:Trunk o X (p.B/10) a b e)
    {A:StemA n}{F Y:Oil n}
    (w:Oily a e B W)(t:Temper o A B)(tail:Soak o Y a c e)
    (split:∀ V:Openc (More n) e,F V.val=X V.val+Y V.val)
    {δ:ℝ}(hw:δ+W*c < (bud (glaze A F) 2).re):
    Regalia (glaze A F) (display A p K o X) δ (W*c):=by
  have hg:glaze A F =ᶠ[𝓝 0] fun x=>glaze A X x + glaze A Y x:=by
    filter_upwards [petals_open r.pos A] with x v
    unfold glaze; rw [split ⟨_,v⟩,Matrix.trace_add]
  obtain ⟨hy,hd⟩:=soak_glaze tail w t
  obtain ⟨hx,_⟩:=soak_glaze h.pay w t
  have pf:=(hx.bloom.add hy.bloom).congr hg
  have px:=hx.bloom.congr (displays r h w.hb.le A)
  have ne(k): ‖bud (display A p K o X) k - bud (glaze A F) k‖ ≤ W*c := by
    rw [px.bud_eq,pf.bud_eq,Pi.add_apply,←sub_sub,sub_self,zero_sub,norm_neg]; exact hd k
  refine ⟨pf.1,px.1,ne,?_⟩
  rw [pf.bud_eq,Pi.add_apply,Complex.add_re] at hw
  rw [px.bud_eq]
  have := (Complex.re_le_norm _).trans (hd 2)
  exact lt_of_add_lt_add_right (hw.trans_le (add_le_add_right this _))

