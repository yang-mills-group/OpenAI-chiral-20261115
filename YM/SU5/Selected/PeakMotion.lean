import YM.SU5.FiniteGaugeData.Tower.Synergy
import YM.SU5.Selected.ProofReader
/-! # Pick a separated spatial conjunction. variant using nonnegative *grade* shifts.
May take sufficiently large even in each space direction since common-invariant projection
at that grade safely prices below. Not assuming actual absence of extra grade invariants.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric MeasureTheory Measure
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H : Hilbert} {I : Type*} [Fintype I] (t : List I)
  (M : Mesh)(P:Alliance I (marks M) H)
noncomputable def spotter (s:ℕ) : Moving I H where
 move i:={ wind t:=(P.crew i).play (notch M s t)
           small p:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; rw [one_mul]; exact (P.crew i).pulls _ x)
           nil:=by rw [notch_zero,(P.crew i).play_zero]
           along x y:= by rw [notch_add,(P.crew i).piles] }
 separate i j x y:= P.cCom ..
lemma wind_spot (v:I→ℤ)(s:ℕ): Moving.gallery (spotter M P s) t v=P.raw t (fun i=> notch M s (v i)) := by induction t with|nil=>rfl|cons i t ih=>rw [P.raw_step, Moving.entry, ih]; rfl
lemma peek (x y:H) (l : ℝ) (v:0 < l) (h:t.Nodup) (p : ∀ i : I,∀ u,(P.crew i).play u y=y) (w:‖y‖=1) (b:l < ‖inner ℂ y x‖^2) (s:ℕ)(g:I→ℕ): ∃ k:I→ℤ,(∀ i,(g i:ℤ)≤ k i) ∧ l < ‖inner ℂ x (P.raw t (fun i=> notch M s (k i)) x)‖:=by
 classical
 let T:= spotter M P s; let G:I→ℤ:=fun i=> g i
 have ht:= Moving.median T t (fun _=>G) x h; let z:= T.pause t x
 have h0 := T.par t x
 have hv : y∈ T.aligned t:= T.aligned_ok.mpr (fun i _ _=> p ..)
 have he : inner ℂ x z=inner ℂ z z:= by
   rw [show inner ℂ z z=inner ℂ x (T.pause t z) from T.swing t x z,T.pin z h0]
 have hx : inner ℂ y x=inner ℂ y z:= by unfold z; rw [←T.swing,T.pin y hv]
 have hp : l < ‖inner ℂ x z‖:=by
    rw [he, inner_self_eq_norm_sq_to_K]; change l<‖((‖z‖:ℂ)^2)‖; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)]; rw [hx] at b
    refine lt_of_lt_of_le b (pow_le_pow_left₀ (norm_nonneg _) ((norm_inner_le_norm _ _).trans_eq ?_) _); rw [w,one_mul]
 let f(n:ℕ)(v:I→Fin (n+1)):= inner ℂ x (T.gallery t (Moving.crew n G v) x)
 have hX: Tendsto (fun n:ℕ => ‖Average.center (f n)‖) atTop (𝓝 (‖inner ℂ x z‖)) := by
    have hs(n:ℕ): Average.center (f n)=inner ℂ x (Average.center (fun v:I→Fin (n+1)=> T.gallery t (Moving.crew n G v) x)) := Average.natural _ (innerSL ℂ x)
    simp_rw [hs]; exact (((innerSL ℂ x).continuous.continuousAt.tendsto.comp ht).norm)
 obtain ⟨n,v⟩:= (hX.eventually (lt_mem_nhds hp)).exists
 obtain ⟨v, hv⟩: ∃ v:I→Fin (n+1), l < ‖f n v‖:= not_forall_not.mp (fun j => not_le_of_gt (show l< ‖Average.center (f n)‖ from v) (Average.norm_worth fun i=> le_of_not_gt (j i)))
 let k:= Moving.crew n G v; refine ⟨k,fun i=> le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le (v i).val),?_⟩; rw [←wind_spot t M P k]; exact hv
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.peek
