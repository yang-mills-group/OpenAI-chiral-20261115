import YM.SU5.Six.DoseTour
import ZecaSpray
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 180000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Aria DoseTravel Boundary Function Filter Metric Set MeasureTheory WithLp 
open scoped ContDiff Topology BigOperators NNReal ENNReal InnerProductSpace
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Zeca Probe

def skate(x:Vantage)(i:ℕ) := slider x (chosen x i)

abbrev backV : E4 ≃L[ℝ] Vantage:=EuclideanSpace.equiv Axis ℝ
abbrev homeV : Vantage ≃L[ℝ] E4:=backV.symm
private lemma cash (F:SampleDose): HasCompactSupport (fun p:E4=> (F.val (backV p):ℂ)) :=
  (F.budget.comp_homeomorph backV.toHomeomorph).mono
    (fun _ h e=>h (Complex.ofReal_eq_zero.mpr e))
def att (F:SampleDose) :Test4:=
 (cash F).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (F.smooth.comp backV.contDiff))
lemma att_b (F:SampleDose): bar (att F)= att F:=by
 ext1; rw [bar_at]; exact Complex.conj_ofReal _
lemma att_s (F:SampleDose):
 tsupport ⇑(att F) ⊆ backV ⁻¹' tsupport F.val := by
 refine (closure_mono (s:= Function.support ⇑(att F)) (t:= Function.support (F.val ∘ backV)) ?_).trans (tsupport_comp_subset_preimage _ backV.continuous)
 intro x p
 exact fun h=>p (Complex.ofReal_eq_zero.mpr h)

lemma skate_ahead (x y:Vantage)(i:ℕ):
 att (skate (x+y) i)= ahead (homeV y) (att (skate x i)):=by
 let f:=chosen x i
 let g:=chosen (x+y) i
 have e(p:Vantage): g p=f (p-y):=by
    unfold ContDiffBump.toFun
    simp only [Function.comp_apply, sub_sub,add_comm y x]
    rfl

 ext1 p
 change ↑(g.normed volume (backV p))=(↑(f.normed volume (backV (p-homeV y))):ℂ)
 rw [map_sub,backV.apply_symm_apply]
 simp_rw [ContDiffBump.normed_def,e, integral_sub_right_eq_self]
#check Complex.ofReal_eq_zero

variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
  (Ω:Bench S)(e:∀p,M S p Ω.val=Ω.val)(h:saucer S Ω.val=Ω.val)
  (D: Hierarchy.Seld.Zeca.Moment H)
  (x:Vantage)

include e in
lemma skate_move(y:Vantage)(i:ℕ):
 Zeca.awake S Ω D (att (skate (x+y) i))=
 M S (homeV y) (Zeca.awake S Ω D (att (skate x i))):= by
 rw [skate_ahead,awake_move _ _ _ e]
open OS.Semigroup
lemma att_val(F:SampleDose)(x:Vantage):att F (homeV x)= (F.val x:ℂ):=rfl
lemma skate_int (F:SampleDose)(q:E4→H):
 beam H F (q ∘ homeV)=(∫ x:E4,att F x • q x):=by
 let φ:=homeV.toHomeomorph.toMeasurableEquiv
 have t:MeasurePreserving φ volume volume:=(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis).symm
 rw [←t.integral_comp' (fun x:E4=>att F x • q x)]
 unfold beam; refine integral_congr_ae (Eventually.of_forall fun x=>?_)
 change (F.val x:ℂ) • q (homeV x)=(att F (homeV x)) • q (homeV x)
 rw [att_val]

include e h

lemma skate_go (u:ℝ≥0) (p:0<u):
 Tendsto (fun i=>S.E u (Zeca.awake S Ω D (att (skate x i)))) atTop
    (𝓝 (M S (homeV x) (parabola S D.n (duration u) (D.op Ω.val)))):= by
 let y:= (parabola S D.n (duration u) (D.op Ω.val))
 let f:=fun w=>M S (homeV w) y
 have b:Continuous (fun w:Vantage=>(M S (homeV w)) y):= by
    have e':= (step_c S).comp ((continuous_const (y:=y)).prodMk homeV.continuous)
    exact e'
 have s:Tendsto (fun i=>beam H (skate x i) f) atTop (𝓝 (f x)):=sprinkle x H f b
 change Tendsto (fun i=> S.E u (Zeca.awake S Ω D (att (skate x i)))) atTop (𝓝 (f x))
 apply s.congr
 intro i
 let g:=att (skate x i)
 show beam H (skate x i) f=S.E u (D.field S g Ω).val
 rw [cinnabar S Ω D h e g u p (cash (skate x i))]
 exact skate_int (skate x i) (fun p=>M S p y)
