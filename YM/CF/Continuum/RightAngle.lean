import YM.CF.Continuum.Awning
import YM.CF.Continuum.PayTax

/-! Price in the very same denominator grammar near shifted tilt. Use full-box
    support gate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase RG
open Laurent Next.Free Fir Ember Jill Kea Sods Flare Dial Peaks Cascade Vault Paige Wilson
open MeasureTheory PathData Precision Tree Sods Emu Graph Skye Scree
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b D L x t k H : ℝ}
def compassRate(N:Side)(k:ℝ):ℝ:=10*(More N).val*k

def shifted (N:Side)(t:ℝ):Set (Pane N):= (fun U:Pane N=> U*(Kea.tax (needles N):Pane N)⁻¹) ⁻¹' (stone group (More N) t)
lemma shift_meas(N:Side)(t:ℝ): MeasurableSet (shifted N t):= (stones ..).preimage (show Continuous (fun x: Pane N=> x*(tax (needles N): Pane N)⁻¹) from continuous_id.mul continuous_const).measurable
lemma shift_mass(N:Side)(t:ℝ): (prior group (More N)).real (shifted N t)=(prior group (More N)).real (stone group (More N) t):=by
 let U: Pane N:= Kea.tax (needles N); let G (x:Pane N):= x*U⁻¹
 apply congrArg ENNReal.toReal
 refine (show MeasurePreserving G (prior group (More N)) (prior group (More N)) from ?_).measure_preimage (stones ..).nullMeasurableSet
 refine measurePreserving_pi _ _ (f:=fun i v=> v*(U i)⁻¹) (fun i=> ?_)
 simpa only [one_mul] using group.preserve_two_sided 1 (U i)⁻¹

lemma lineNear (U V : Bkg N)(H:∀ i,chordD group (U i) (V i)≤ t)(x:Site N)(w:Walk): chordD group (travel U x w) (travel V x w)≤w.length*t:=by
 induction w generalizing x with
 | nil=> simp [travel,chordD]
 | cons a b ih=>rw [List.length_cons,Nat.cast_add_one,add_mul,one_mul,add_comm _ t, travel, travel]; refine (chordD.propagate ..).trans (add_le_add ?_ (ih _)); unfold Step.read; split_ifs; rw [chordD.inverse]; exact H _; exact H _
lemma needleFace (U:Pane N)(p:U∈shifted N t) (i: Face (Per (More N))): group.chord (faceValue U i) ≤ 4*t:=by
 let V:Pane N:=Kea.tax (needles N); have h : ∀ i:Edge (Site (More N)),chordD group (U i) (V i)≤t:=fun i=>p i (Set.mem_univ _)
 let W:=square i.2.val.1 i.2.val.2; have he:=lineNear U V h i.1 W; rw [show travel V i.1 W=1 from tax_flat (needles N) ..] at he; unfold chordD at he; rw [inv_one,mul_one, show W.length=4 from rfl,Nat.cast_ofNat] at he; exact he
lemma awake (P:GramM N)(U:Pane N)(p:U∈shifted N t)(h:4*t≤ P.p.threshold):flags P.p.threshold U=∅:=by
 refine eq_empty_iff_forall_notMem.mpr fun i k=>?_ ; obtain ⟨x,u,v⟩:=(flags_spec ..).mp k; exact not_lt_of_ge ((needleFace U p x).trans h) v
lemma compassR(N:Side){t:ℝ}(g:0<t)(U:Pane N)(p:U∈shifted N t): 1/2 ≤ reflectible N (compassRate N t) U:=by
 let V: Pane N:=Kea.tax (needles N); have he: deviation (fourTrace U) (fourTrace V) 1 ≤ 4*((More N).val*t):=by
    unfold deviation; simp only [one_mul,inv_one,mul_one]; apply (sum_le_sum (g:=fun i=> (More N).val*t) _).trans _
    · intro i _; exact le_trans (lineNear U V (fun j=>p j (Set.mem_univ _)) 0 (cyclic (More N) i)) (le_of_eq (by simp [cyclic]))
    simp [Axis]
 apply le_trans _ (le_max_right ..); let n:= compassRate N t
 let r := clampTrace (fourTrace U) (fourTrace V); have hr:= (clampTrace_le (fourTrace U) (fourTrace V) 1).trans he; have hv:r/n ≤ 1/2:= by rw [div_le_iff₀ (by unfold n compassRate; positivity)]; exact hr.trans (by unfold n compassRate; have ht:0 < (More N).val*t:=mul_pos (nPos _) g; linarith)
 change _ ≤ _ - r/n; linarith

private lemma moneyB (P:GramM N)(W:P.path.Bounds P.funds a D L) (V: Pane N) (v:∀ i:Face (Per (More N)),group.chord (faceValue V i) ≤ k)(u:0≤k)(l:P.funds.direct ≤ H) (t:k≤ P.p.threshold)(b:0≤P.beta)(_c:0 ≤ D): P.path.inChannels P.funds P.p P.beta V ≤ stoutY (More N) P.beta k H P.p.threshold D L :=by
 -- rework Graph.money but tilted
 let Z:= stoutY (More N) P.beta k H P.p.threshold D L
 have he(i:Signed): P.path.principal P.funds P.p P.beta (Lattice.pull i 0 V) ≤ Z:=by
    let U:=Lattice.pull i 0 V; let C:= P.path; let F:= P.funds; let q:= P.p
    let L':= Graph.goldY k H q.threshold D; have hu(r:Face (Per (More N))): C.baseTerm F q U r ≤ L':=by
       have hg(r:Face (Per (More N))): group.chord (faceValue U r) ≤ k:=by unfold U; rw [Face.send_price V _ i 0 group.chord group.chord_inv (fun _ u=>group.chord_conj u _)]; exact v _
       unfold baseTerm clipped; rw [if_pos ((hg r).trans t)]; refine add_le_add ?_ ?_
       · apply div_le_div_of_nonneg_right _ (by positivity); exact mul_le_mul l (pow_le_pow_left₀ (group.chord_nonneg _) (hg r) _) (sq_nonneg _) (P.funds.quadratic_pos.le.trans l)
       split; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (Graph.pea W U hg u r) 2) (by positivity); positivity
    obtain ⟨A,B⟩:=Graph.oath W P.p U; unfold Z stoutY taxY PathData.principal; refine (add_le_add (mul_le_mul_of_nonneg_left (add_le_add ((sum_le_sum (g:=fun _=>L') (fun i _=>hu i)).trans_eq (c:=Fintype.card (Face (Per (More N)))*L') ?_) (le_of_abs_le A)) b) (le_of_abs_le B)).trans_eq (by unfold L' q; ring); simp
 unfold inChannels; refine (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> he i)) (by positivity)).trans_eq ?_; simp [Z]

def yieldAngle (P:GramM N)(t:ℝ) :ℝ:= ∫ i, priorWeight P i * reflectible N t i ∂prior group (More N)
theorem paidYield (P:GramM N)(p:P.path.Bounds P.funds a D L)(l:P.funds.direct ≤ H)(u:4*t≤ P.p.threshold)(g:0<t)(e:0≤P.beta)(c:0≤D): gainS (More N) t * Real.exp (-stoutY (More N) P.beta (4*t) H P.p.threshold D L) / 2 ≤ yieldAngle P (compassRate N t):=by
 let n:=More N; let μ:=prior group n; let b:=compassRate N t; let X:= Real.exp (-stoutY (More N) P.beta (4*t) H P.p.threshold D L); have hX:0<X:=by unfold X; positivity
 let a:=shifted N t; have hp:MeasurableSet a:= shift_meas ..; have he(P':Pane N):0 ≤ priorWeight P P' * reflectible N b P' := mul_nonneg (weight_nonneg ..) (reflectible_up ..); let f(i):=priorWeight P i*reflectible N b i; have hf:Integrable f μ:=by
    let B:=priorWeight P; have hs: Envelope B:= env_priorWeight P p; exact ((hs.integrable _).mul_bdd (targetC N b).aestronglyMeasurable (c:=1) (Eventually.of_forall fun i=> (Real.norm_of_nonneg (reflectible_up ..)).trans_le (reflectible_cost (by unfold b compassRate; positivity) i)))
 refine le_trans ?_ (integral_mono ((integrable_const (c:=X/2)).indicator hp) hf fun i=> (show a.indicator (fun _=>X/2) i ≤ f i from ?_)); swap
 · by_cases h:i∈a; swap; · rw [Set.indicator_of_notMem h]; exact he i
   rw [Set.indicator_of_mem h]; unfold f; rw [priorWeight, Set.indicator_of_mem (show i∈ Nova.Calm group _ P.p.threshold from awake P i h u)]; have hQ:X ≤ Graph.past P i:= Real.exp_monotone (neg_le_neg (moneyB P p i (needleFace i h) (by positivity) l u e c)); calc
      _ = X*(1/2):=by ring
      _ ≤ _:= mul_le_mul hQ (compassR N g i h) (by norm_num) (hX.le.trans hQ)
 rw [integral_indicator hp,setIntegral_const,smul_eq_mul,←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); have hg:t ≤ 1:=by linarith [P.p.threshold_le]
 unfold a; rw [shift_mass]; exact mul_le_mul_of_nonneg_right (mass_i group n _ g hg) hX.le
end YM.CF.Window
