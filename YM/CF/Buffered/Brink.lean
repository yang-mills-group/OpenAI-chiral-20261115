import YM.CF.Buffered.Duct
import YM.CF.Buffered.Archive
/-! Finite partition comparison at two anchors. Includes priors (actual gauge groups) -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Buffered.Crust.Grid
open Function Filter Finset Lattice Wilson RG PathData Work.F03 Cube Region Roost Rush MeasureTheory Metric Girt Nova
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators Topology ENNReal
variable {G:Gauge}{N P D:Side}{a b r C L β:ℝ}{s:ℕ} {F:PathData G}{c:Clip}{p:BudgetPoint}
-- same budget anchor is okay: Month is same in simultaneous lists; even if pillars not same Lots

def floorF (N:Side)(F: PathData G)(c:Clip)(p:BudgetPoint)(β a:ℝ): Config G N→ℝ:= (Calm G N a).indicator (fun y=>Real.exp (-(F.inChannels c p β y)))
lemma floor_e (g:F.Bounds c r C L) (P:Side) (p:BudgetPoint)(β v:ℝ): Envelope (floorF P F c p β v) := env_indicator _ (calm_m ..) (pole_w (F.inChannels c p β) (fun x:ℝ=> Real.exp (-x)) (by fun_prop) (F.channels_env g ..))
lemma floor_p(v:Config G P)(a:ℝ): 0 ≤ floorF P F c p β a v:= Set.indicator_nonneg (fun x _=> (Real.exp_pos _).le) _
lemma floor_hit(v:Config G P)(a:ℝ)(h:flags a v=∅): floorF P F c p β a v=Real.exp (-(F.inChannels c p β v)):= Set.indicator_of_mem (show v ∈ Calm G P a from h) _
def globe (N:Side)(F:PathData G)(c:Clip)(p:BudgetPoint)(β a:ℝ): ℝ:=∫ v,floorF N F c p β a v∂ Wilson.prior G N
local notation "Q" => Tower D
variable (K:Planck N P D)
lemma calm_away (K:Planck N P D)(Y:Tower D→ Config G P)(h:∀ i,flags a (Y i)=∅)(t:∀ i x,Legend s b (issue K Y) (Y i) (send K (i,x)) x) (v:2≤ s)(w:a+4*b≤p.threshold): flags p.threshold (issue K Y)=∅:=by
 apply (flags_calm ..).2; rintro ⟨x,i⟩; obtain ⟨⟨y,z⟩,rfl⟩ := (send K).surjective x
 let Z:= issue K Y; let u:= send K (y,z); let d:=G.chord (faceValue Z (u,i)); let e:=G.chord (faceValue (Y y) (z,i))
 have ht : e ≤ a:= (flags_calm ..).1 (h y) (z,i); have hs:d-e≤4*b:= (le_abs_self _).trans ((Dg_lip ..).trans ((t y z (square i.val.1 i.val.2) (by unfold square; simp; omega)).trans_eq (by simp [square]))); change d ≤ _; linarith
lemma plan_ex (K:Planck N P D)(h:F.Bounds c r C L)(W:β≥0) (t:2 ≤ s) (v:0<b)(u:b≤1) (l:a+4*(2*b)≤p.threshold)(d:0≤C) (z:0<globe P F c p β a) : let M:= stripP P (2*s); let Z:=(b/4)^(Module.finrank ℝ G.Mat*M.card)/2* globe P F c p β a
 Real.exp (- Plan.cellsCost N D P β p.threshold C L s (2*b) r c.direct)* Z^(Fintype.card Q) ≤ globe N F c p β p.threshold := by
 classical
 intro M Z; obtain ⟨w,hA⟩ := hose_bin M b v u (floorF P F c p β a) (floor_e h ..) (fun u=>floor_p u a) z
 let Y':=tubing M b w; let T:= Y'.indicator (floorF P F c p β a); let B:=∫ x,T x∂ Wilson.prior G P
 have hz: Z≤B :=by unfold B T; rw [integral_indicator (tubing_closed ..).measurableSet]; exact hA
 let A:= Plan.cellsCost N D P β p.threshold C L s (2*b) r c.direct
 let μ:=Measure.pi (fun _: Tower D=> Wilson.prior G P)
 let f(Y: Tower D→ Config G P):= Real.exp (-A) * ∏ i: Tower D,T (Y i)
 have hf: Integrable f μ := (Integrable.fintype_prod (μ:=fun _:Tower D=> Wilson.prior G P) (fun (_:Tower D)=> (show Integrable T (Wilson.prior G P) from ((floor_e h P p β a).integrable _).indicator (tubing_closed ..).measurableSet))).const_mul _
 let D':= floorF N F c p β p.threshold; have hp:=floor_e h N p β p.threshold; have H(Y: Tower D→ Config G P): f Y ≤ D' (issue K Y):=by
    by_cases e:∀ i: Tower D,Y i∈ Y'∧ flags a (Y i)=∅; swap; ·
      push Not at e; obtain ⟨i,x⟩:=e; unfold f; rw [(Finset.prod_eq_zero (i:=i) (mem_univ i) ?_),mul_zero]; swap; · unfold T; by_cases v:Y i∈Y'; rw [Set.indicator_of_mem v]; exact Set.indicator_of_notMem (show Y i ∉ Calm G P a from (x v).ne_empty) _; exact Set.indicator_of_notMem v _ -- tune
      exact floor_p ..
    have he:Connected (2*s) (2*b) Y:= ⟨fun i j x u=> by refine (Dg_tri G (Y i x) (w x) (Y j x)).trans ?_; rw [Dg_comm _ (Y i x)]; exact (add_le_add ((e i).1 x u) ((e j).1 x u)).trans_eq (two_mul ..).symm⟩
    have hk: ∀ i x,Legend s (2*b) (issue K Y) (Y i) (send K (i,x)) x := fun i x l=>fun p=> travel_g K Y i x l he (by positivity) p
    have ht:= calm_away K Y (fun i=>(e i).2) hk t l
    unfold f D'; rw [floor_hit _ _ ht]; have hg:= p.threshold_pos; have hr:= Plan.grouped h hk (by positivity) ht (fun v=> (flags_calm ..).2 fun i=> ((flags_calm ..).1 (e v).2 i).trans (by linarith)) t d W
    simp_rw [T,show ∀ i:Tower D, Y'.indicator (floorF P F c p β a) (Y i)=floorF P F c p β a (Y i) from fun i=>Set.indicator_of_mem ((e i).1) _,floor_hit _ _ (e _).2]; rw [← Real.exp_sum,←Real.exp_add, sum_neg_distrib]; apply Real.exp_le_exp.mpr; change _ ≤ ∑ i,F.inChannels c p β (Y i) + A at hr; linarith -- may `Q` Lean conflict
 have hl: ∫ x,f x∂ μ ≤ globe N F c p β p.threshold:=(integral_mono hf ((issue_mp K).integrable_comp_of_integrable (hp.integrable _)) H).trans_eq (by -- map
    change (∫ x,D' (issue K x)∂μ)=∫ z,D' z∂ Wilson.prior G N; rw [←(show Measure.map (issue K) μ= Wilson.prior G N from (issue_mp K).map_eq),integral_map (issue_mp K).1.aemeasurable hp.meas.aestronglyMeasurable])
 apply le_trans _ hl; unfold f; rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_fintype_prod_eq_pow] -- tune args
 exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold Z; positivity) hz _) (Real.exp_pos _).le
end YM.CF.Buffered.Crust.Grid
#print axioms YM.CF.Buffered.Crust.Grid.plan_ex
