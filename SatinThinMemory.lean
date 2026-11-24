import SatinThinResolvent
import YM.UVNext.FREE_STRESS_CERTIFICATE.Tangent
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision
open Regis Circuit Regis.Head.Brecht
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open YM.Stationary (Gaia)
open YM.UVNext.FreeStress (curve one_view) -- rotate conflicts
open QuadClock
abbrev witnessZ (i:PlaqAxes):ℝ:= starWeight i / 2
def capture (i j:PlaqAxes):ℤ:= UVNext.FreeStress.rotate (curve 3) i.val.1 i.val.2 j.val.1 j.val.2
lemma rad_self (i j:PlaqAxes): capture i j^2= if i=j then 16 else 0:=by revert i j; decide
lemma yAlive : 0 < Fintype.card SU.group.ColorIndex:=by
 haveI: Nontrivial SU.group.Color:= Thera.yet_one.nontrivial_color; have hf:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
 change 0 < Fintype.card (Fin SU.group.lieDim); rwa [Fintype.card_fin]
abbrev canonWeight :ℝ:= 32*(Fintype.card SU.group.ColorIndex:ℝ)*Maxwell.normal^2
lemma focusEst : spectrumℓ witnessZ SU.group (YM.basis 3)=(↑canonWeight:ℂ):=by
 let t:= Fintype.card SU.group.ColorIndex; let a:= Maxwell.normal
 have hf(x:PlaqAxes): Maxwell.bareCurl x.val.1 x.val.2 x.val.1 x.val.2 (YM.basis 3)=a*(capture x x:ℝ):= one_view ..
 have hg(x y:PlaqAxes): spectrumColor x y SU.group (YM.basis 3)=(if x=y then (canonWeight:ℂ) else 0):=by
    unfold spectrumColor duoPower specter; rw [one_view]; change (2:ℂ)*t*(↑(a*(capture x y:ℝ)):ℂ)^2=_; push_cast; rw [mul_pow]; split; next h=> rw [←Int.cast_pow,rad_self,if_pos h]; unfold t a; push_cast; ring
    next h=> rw [← Int.cast_pow,rad_self,if_neg h]; push_cast; ring
 let f(x):= (witnessZ x:ℂ); unfold spectrumℓ wholeV; simp_rw [hg]; have hp(x:PlaqAxes): (∑ j,f x*f j*(if x=j then (canonWeight:ℂ) else 0))= f x^2*canonWeight:=by simp [sq,mul_ite]
 change ∑ x:PlaqAxes, (∑ j,f x*f j*(if x=j then (canonWeight:ℂ) else 0)) = (canonWeight:ℂ); simp_rw [hp]; rw [←sum_mul]; let S:Finset PlaqAxes:={rimA,rimB,rimC,rimD}
 rw [← sum_subset (subset_univ S)]; swap; · intro i h u; rcases rimCases i with p|p|p|p|p|p <;> subst i; rotate_left; exacts [(u (by simp [S])).elim,(u (by simp [S])).elim,(u (by simp [S])).elim,(u (by simp [S])).elim,by norm_num [f,witnessZ,show starWeight highHigh=0 from rfl],by norm_num [f,witnessZ,show starWeight lowLow=0 from rfl]] -- tune
 unfold S; rw [sum_insert (by decide : rimA∉ ({rimB,rimC,rimD}:Finset _) ), sum_insert (by decide : rimB ∉ ({rimC,rimD}:Finset _) ),sum_insert (by decide : rimC∉ ({rimD}:Finset PlaqAxes)),sum_singleton]; norm_num [f,witnessZ,show starWeight rimA=1 from rfl,show starWeight rimB=-1 from rfl,show starWeight rimC=-1 from rfl,show starWeight rimD=1 from rfl] -- tune brace inferred
lemma focus_positive : 0 < canonWeight :=by unfold canonWeight; have ht:=Maxwell.normal_pos; have h:=yAlive; positivity
end YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.focusEst
