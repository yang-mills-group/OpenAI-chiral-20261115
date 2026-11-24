import YM.SU5.Reconstruction.Vermont.Playlist
import YM.SU5.Reconstruction.Crease.Ghost
/-!
# Turn every instant in a script to one Wick rotation. Horizontal units pay analytic temp.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail BridgeClub ContinuousLinearMap Picket
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(M:Set H.Op)
def shifted (t:ℝ≥0)(z:ℂ) : H.Op:= phase S ((t:ℝ)*z)
local notation "Π"=> ℝ≥0
inductive WickScript : (ℂ→ H.Op) → ℝ≥0 → ℝ≥0→ Prop
| weather (d:ℝ≥0) : WickScript (shifted S d) d 1
| now (A:H.Op) (t:ℝ≥0)(p:A∈ M)(e:‖A‖≤(t:ℝ)): WickScript (fun _=> A) 0 t
| link {A B:ℂ→H.Op}{d e c u} : WickScript A d c→ WickScript B e u→ WickScript (fun z=>A z*B z) (d+e) (c*u)
| plus {A B:ℂ→H.Op}{d c u} : WickScript A d c→ WickScript B d u→WickScript (fun z=>A z+B z) d (c+u)
| scale {A:ℂ→H.Op} {d c}: WickScript A d c→ (t:ℂ)→ WickScript (fun z=> t • A z) d (‖t‖₊*c)
| charge {A:ℂ→H.Op} {d c u} : WickScript A d c→ c ≤ u→ WickScript A d u

lemma shifted_one (d:Π): shifted S d 1=S.E d:=by rw [shifted,mul_one,width_real,Real.toNNReal_coe]
@[simp] lemma shifted_side (x:ℝ)(d:Π):shifted S d (sideways x)=S.edge ((d:ℝ)*x):= by
 unfold shifted; rw [← width_imaginary, show (d:ℝ)*sideways x=sideways ((d:ℝ)*x) from (by unfold sideways; push_cast; ring)]
lemma shifted_pay (z:ℂ)(d:Π): ‖shifted S d z‖≤1:= phase_price ..
lemma shifted_cont (d:Π)(x:ℂ→H)(e:Continuous x): Continuous (fun z=> shifted S d z (x z)):= phase_cont S _ _ e (by fun_prop)
lemma heat_real (t d:Π): shifted S d (t:ℝ)=S.E (d*t):= by unfold shifted; rw [← Complex.ofReal_mul, width_real, ← NNReal.coe_mul, Real.toNNReal_coe]
lemma shifted_hol (d:Π): AnalyticOnNhd ℂ (shifted S d) inside:=by
 by_cases t:d=0; swap
 · have h:0<(d:ℝ):= (show 0<d from pos_iff_ne_zero.mpr t); intro z p; exact (phase_ana S ((d:ℝ)*z) (show 0<(((d:ℝ):ℂ)*z).re from (by simp [h,(show 0<z.re from p)]))).comp (f:=fun z:ℂ=> (d:ℝ)*z) (analyticAt_const.mul analyticAt_id) -- order
 subst d; unfold shifted; simp only [NNReal.coe_zero, Complex.ofReal_zero, zero_mul]; exact analyticOnNhd_const
lemma edge_adds (r d:ℝ) : S.edge (r+d)=S.edge r*S.edge d:= (S.send ..).symm
lemma tickParcel (t:ℝ)(A:H.Op): (parcelUp S (t • basis a)) A= S.edge t*A*S.edge (-t):=by rw [parcelUp, ←neg_smul,trans_time,trans_time]
variable {S M}
namespace WickScript
variable {A:ℂ→H.Op}{d c:Π} (x:WickScript S M A d c)
include x
lemma understands : Script S M (A 1) d c:= by
 induction x with
 | weather d=> rw [shifted_one]; exact Script.weather _
 | now _ _ h p=> exact Script.now _ _ h p
 | link _ _ ih h=> exact Script.link ih h
 | plus _ _ ih h=> exact Script.plus ih h
 | scale _ t ih=> exact Script.scale ih t
 | charge _ t ih=> exact Script.charge ih t
lemma payee (z:ℂ): ‖A z‖≤ (c:ℝ):= by
 induction x with
 | weather d=> exact shifted_pay ..
 | now _ _ h p=> exact p
 | link _ _ ih h=> exact (norm_mul_le ..).trans (mul_le_mul ih h (norm_nonneg _) ((norm_nonneg _).trans ih))
 | plus _ _ ih h=> exact (norm_add_le ..).trans (add_le_add ih h)
 | scale _ t ih=> rw [norm_smul]; exact mul_le_mul_of_nonneg_left ih (norm_nonneg _)
 | charge _ t ih=> exact ih.trans t
lemma with_cont (f:ℂ→ H)(p:Continuous f): Continuous (fun z=> A z (f z)):=by
 induction x generalizing f with
 | weather d=> exact shifted_cont S d _ p
 | now A _ _ _=> exact A.continuous.comp p
 | link _ _ ih h=> exact ih _ (h f p)
 | plus _ _ ih h=> exact (ih f p).add (h f p)
 | scale _ t ih=> exact (ih f p).const_smul t
 | charge _ _ ih=> exact ih _ p
lemma hol_paid : AnalyticOnNhd ℂ A inside:=by
 induction x with
 | weather d=> exact shifted_hol _ d
 | now _ _ _ _=> exact analyticOnNhd_const
 | link _ _ ih h=> exact ih.mul h
 | plus _ _ ih h=> exact ih.add h
 | scale _ t ih=> exact analyticOnNhd_const.smul ih
 | charge _ t ih=> exact ih
end WickScript
lemma Script.wake {A:H.Op}{d c:ℝ≥0} (x:Script S M A d c) : ∃ f:ℂ→H.Op, WickScript S M f d c ∧ f 1=A:=by
 induction x with
 | weather d=> exact ⟨_,WickScript.weather d,shifted_one ..⟩
 | now _ _ h p=> exact ⟨_,WickScript.now _ _ h p,rfl⟩
 | link _ _ ih h=> obtain ⟨A,e,rfl⟩:=ih; obtain ⟨B,g,rfl⟩:=h; exact ⟨_,WickScript.link e g,rfl⟩
 | plus _ _ ih h=> obtain ⟨A,e,rfl⟩:=ih; obtain ⟨B,g,rfl⟩:=h; exact ⟨_,WickScript.plus e g,rfl⟩
 | scale _ t ih=> obtain ⟨A,e,rfl⟩:=ih; exact ⟨_,WickScript.scale e t,rfl⟩
 | charge _ t ih=> obtain ⟨A,e,rfl⟩:=ih; exact ⟨_,WickScript.charge e t,rfl⟩

end YM.Lens
