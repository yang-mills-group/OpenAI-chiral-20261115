import YM.SU5.Reconstruction.Cross.Coherency
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
-- non-contact contour connections to positive real time t; Euclidean coordinate adds sideways (=-I·t).
open _root_.YM.SelectionAnalysis Vacancy.Average
variable {ι:Type*}[Fintype ι] (f : ι→ Marks (tent Y H) false) (g : ∀ i, Gate Y H s j (f i))
local notation "Β" f:max h:max => entrance Y H V s Q Qt j false C f h
local notation "Γ" => saunters Y H V Q Qt j false C c
local notation "G" => peninsula Y H V Q Qt j false C c
local notation "L" => fort Y H V Q Qt j false C c
local notation "γ" => vocation Y H V Q Qt j false C c
local notation "Λ₀" => timeMesh Λ
local notation "U" x:max => (G).U (diameter x)
local notation "O" => paidOp Y H V Q Qt s j C c
local notation "W" x:max => narrowOrt Y H V Q Qt j false C c x
variable (t:List ι) (x:ι→Axis→ℝ)
section one
variable {F:Marks (tent Y H) false} (g' : Gate Y H s j F)
local notation "X" v:max=> Gate.left g' v
local notation "Z" v:max=> Gate.right g' v
local notation "B₀" => W (Β g'.entry g'.pos)
-- fix reference placement v and time drift in each direction. Needn't require v itself interior. contour shifts j only.
def contourOp (v:Axis→ℝ) (z : ℂ) : (fort Y H V Q Qt j false C c).Op :=
  ((G).F (((g'.left v:ℝ):ℂ)+z)) * (U v) * (W (Β g'.entry g'.pos)) * (U (-v)) * ((G).F (((g'.right v:ℝ):ℂ)-z))
-- insert_edge is physical cigar, not local net
local notation "ξ" => contourOp Y H V Q Qt s j C c g'
noncomputable abbrev stepDrift (j:Axis)(v:Axis→ℝ)(z:ℝ):Axis→ℝ := update v j (v j+z)
lemma stepped (v:Axis→ℝ) (z:ℝ) : X (stepDrift j v z) = X v + z ∧ Z (stepDrift j v z)= Z v-z:=by
 have he : X (stepDrift j v z)=X v+z := by unfold Gate.left stepDrift; rw [update_self]; abel
 constructor; exact he
 unfold Gate.right; rw [he]; abel
lemma dia_step (v:Axis→ℝ) (z:ℝ) : diameter (a:=j) (stepDrift j v z)=diameter (a:=j) v := by
 let w:=(stepDrift j v z); apply Subtype.ext; ext i; by_cases h:i=j; · subst i; exact ((diameter (a:=j) _).property : ((diameter (a:=j) (stepDrift j v z)).val:E4) j = 0) |>.trans ((diameter (a:=j) v).property).symm
 rw [diameter_at _ _ h,diameter_at _ _ h]; exact Function.update_of_ne h ..
private lemma diam_neg (v:Axis→ℝ): -diameter (a:=j) v=diameter (a:=j) (-v):= ((map_neg (SEP j) _)).symm
/-- Continue each real ordering-time coordinate of the spatially spread kernel into Minkowski time. No implied ordering-axis independence of the contour! -/
def minkOp (v:Axis→ℝ)(t:ℝ) : (fort Y H V Q Qt j false C c).Op := (G).edge t * O g' v * (G).edge (-t)
local notation "π" => minkOp Y H V Q Qt s j C c g'
def visual (v:Axis→ℝ)(z:ℂ):Prop:= 0 < g'.left v+z.re ∧ 0 < g'.right v-z.re
lemma within_step (v:Axis→ℝ) (z:ℂ): visual Y H s j g' v z ↔ g'.within_ (stepDrift j v z.re):= by unfold visual Gate.within_; rw [(stepped Y H s j g' ..).1,(stepped Y H s j g' ..).2] -- inspect order section vars
local notation "Λp" v:max z:max => visual Y H s j g' v z
lemma contour_analytic (v:Axis→ℝ) : AnalyticOnNhd ℂ (contourOp Y H V Q Qt s j C c g' v) {z:ℂ | visual Y H s j g' v z} := by
 intro x h; obtain ⟨p,q⟩:=h; unfold contourOp -- b cut synt
 have ht : (((g'.left v:ℝ):ℂ)+x)∈ inside:=by change 0< ( (_:ℂ)+_).re; simpa using! p -- syntax underscore raw
 have hz : (((g'.right v:ℝ):ℂ)-x)∈inside:=by change 0< (_:ℂ).re; -- cannot change to `_` goal? maybe
                                                               simpa using! q
 refine ((((AnalyticAt.comp (g:= (G).F) ((G).localHeat _ ht) (analyticAt_const.add analyticAt_id)).mul analyticAt_const).mul analyticAt_const).mul analyticAt_const).mul (((G).localHeat _ hz).comp (analyticAt_const.sub analyticAt_id))

private lemma fee_contour {z:ℝ} (h:0<z)(u:ℝ) : (G).F ((z:ℂ)+sideways u)=(G).edge u*(G).E z.toNNReal ∧ (G).F ((z:ℂ)+sideways u)=(G).E z.toNNReal * (G).edge u:=by
 let i:= z.toNNReal; have hi:0< i:= Real.toNNReal_pos.mpr h
 have ht:= dur.mpr hi; rw [show (z:ℂ) = duration i from (by unfold i; simp [duration,h.le]),←(G).roots_heat hi]; exact ⟨((G).along ht u).symm, ((G).either ht u).symm⟩

lemma continued_contour (v:Axis→ℝ) (z:ℂ) (p : visual Y H s j g' v z) : ξ v z = π (stepDrift j v z.re) (-z.im):=by
 let v':=stepDrift j v z.re; have ht:= (within_step Y H s j g' v z).mp p; let t:=-z.im
 have he : z=↑z.re+sideways t:=by unfold sideways t; rw [Complex.ofReal_neg,neg_neg, Complex.re_add_im]
 unfold minkOp; unfold contourOp paidOp
 rw [show (↑(g'.left v):ℂ)+z = (X (stepDrift j v z.re):ℝ)+ sideways t from ?_, show (↑(g'.right v):ℂ)-z=(Z (stepDrift j v z.re):ℝ)+sideways (-t) from ?_]; swap; next =>
    rw [(stepped Y H s j g' v z.re).2,Complex.ofReal_sub]; nth_rw 1 [he]; unfold t; simp only [sideways,Complex.ofReal_neg,neg_neg]; ring
 swap; next => rw [(stepped Y H s j g' v z.re).1,Complex.ofReal_add]; nth_rw 1 [he]; ring
 rw [(fee_contour Y H V Q Qt j C c ht.1 t).1,(fee_contour Y H V Q Qt j C c ht.2 (-t)).2] -- tune
 rw [show (G).U _= _ from (show (G).U (diameter v')=(G).U (diameter v) from congrArg _ (dia_step j ..)), ←diam_neg j (stepDrift j v z.re),dia_step j,diam_neg j v]; simp only [mul_assoc]; rfl
lemma mink_zero (v:Axis→ℝ):π v 0=O g' v :=by unfold minkOp; rw [(G).birth,neg_zero,(G).birth]; change 1*(O g' v)*1=_; rw [one_mul,mul_one]
lemma mink_contour (v:Axis→ℝ)(r:ℝ)(h : g'.within_ v): ξ v (sideways r)= π v r := by
 rw [continued_contour,OS.Semigroup.side, show stepDrift j v 0=v by unfold stepDrift; rw [add_zero,update_eq_self], show -(sideways r).im=r by simp [sideways]]
 exact (by unfold visual; rw [OS.Semigroup.side,add_zero,sub_zero]; exact h)
lemma mink_cont {D:Type*}[TopologicalSpace D](v : D → Axis→ℝ)(t:D→ℝ)(w:D→L)(p:Continuous v)(q:Continuous t)(e:Continuous w): Continuous (fun i=> π (v i) (t i) (w i)):=by simp_rw [minkOp,ContinuousLinearMap.mul_apply]; exact (G).cont_edge _ _ (paid_cont Y H V Q Qt s j C c g' _ v ((G).cont_edge w _ e q.neg) p) q

lemma contour_cost (v:Axis→ℝ)(z:ℂ)(p:Λp v z): ‖ξ v z‖ ≤ ‖W (Β g'.entry g'.pos)‖:= by
 rw [continued_contour Y H V Q Qt s j C c g' v z p]; unfold minkOp paidOp
 let W'(u:(Axis→ℝ)):= U u
 have cost(u): ‖W' u‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=>by unfold W'; rw [(G).unitary,one_mul])
 have he(u):‖(G).edge u‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v=>by rw [(G).life,one_mul])
 have hL(x y:(L).Op)(p:‖x‖≤1):‖x*y‖≤‖y‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) p)
 have hR(x y:(L).Op)(p:‖y‖≤1):‖x*y‖≤‖x‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) p)
 refine (hR _ _ (he _)).trans ((hL _ _ (he _)).trans ((hR _ _ ((G).shrinks _)).trans ((hR _ _ (cost _)).trans (hL _ _ ((hR _ _ (cost _)).trans ((G).shrinks _))))))
end one
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.continued_contour
