import YM.CF.Peaks.Age
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)(u v:Bool)
lemma corset {p:Walk}(ho:Odd G.count.val)(i j:Inta G)(c:ℂ)(e:ℝ)(h:0<e)(he:e≤1)(hw : stop (touch G u i) p=touch G v j) :
 let S:=conduit G u v i j p; let w:=((p.length*e+1:ℝ)*(1+e)^p.length)*‖c‖
 Suite (badge _) (parcel G u e) (parcel G v e) S (reed i j w) (fun x=>panel i j (c • (track x.val.1 (touch G u i) p).1)):=by
  intro S w; let A:=traceP (touch G u i) p; let B:= loopTail G u i; let C:=loopTail G v j
  have hp: A⊆S:= subset_trans (subset_union_left) subset_union_left
  have ht: Grove (terr _) S := .unite (.unite (trace_g ..) (trace_g ..) (trace_source ..) (trace_source ..)) (trace_g ..) (mem_union_left (a:=touch G v j) _ (hw ▸ trace_last ..)) (trace_source ..)
  let f(y: Stem (More P)):=c • (track y (touch G u i) p).1
  have Hu:Differentiable ℂ f:=(track_d (touch G u i) p).fst.const_smul c
  let V (g : Site (More P)→E)(k:Inta G):=(matter (g (touch G u k))); let W(g:Site (More P)→ E)(k:Inta G):=matter (g (touch G v k))
  refine panel_ticket (p:=V) (q:=W) (fun g=> warrant ..) (fun g=>warrant ..) i j S w (fun x=>f x.val.1) ht (fun k=> ?_) (fun k=>?_) (fun g x=>?_) (by unfold w; positivity) ?_ ?_ (fun x=>?_) (fun x y=>?_)
  · rw [peg,← loopEnd G u ho i]; exact mem_union_left _ (mem_union_right _ (trace_last ..))
  · rw [peg,← loopEnd G v ho j]; exact mem_union_right _ (trace_last ..)
  · change (c • (track (relayg g x.val.1) (touch G u i) p).1) * (W g j).val = (V g i).val * (c • _)
    rw [track_g,hw]; change (c • ((V g i).val*_*star (W g j).val))*(W g j).val=_; rw [Matrix.smul_mul,mul_assoc _ (star (W g j).val), (W g j).property.1,mul_one, Matrix.mul_smul]
  · intro a b
    apply honors (f:=fun x:Coil N P=> f x.1 a b); exact (differentiable_pi.mp (differentiable_pi.mp (by exact Hu.comp differentiable_fst) a) b).differentiableOn
  · exact Hu.continuous.comp (continuous_fst.comp continuous_subtype_val)
  · unfold f w; rw [norm_smul,mul_comm _ ‖c‖]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_fst_le ..).trans ((track_size e h.le _ p _ (leftL G x.property)).trans (le_mul_of_one_le_left (by positivity) (by simpa using (show (0:ℝ)≤p.length*e by positivity))))
  unfold f w; rw [←smul_sub,norm_smul]; rw [mul_comm _ ‖c‖,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_fst_le (track x.val.1 _ p-track y.val.1 _ p)).trans; apply (track_vol e h.le _ p _ _ (leftL G x.property) (leftL G y.property)).trans
  rw [←mul_assoc]; change _≤ _*(deal G S x.val y.val /|e|)
  let Z:=deal G S x.val y.val; let F:=fare (traceP (touch G u i) p) x.val.1 y.val.1; have hg:F≤Z:= ((fare_inc hp ..).trans (le_add_of_nonneg_right (fare_t ..)))
  rw [abs_of_pos h]
  let R:= (1+e)^p.length; have hr:0≤ R:=by unfold R; positivity
  calc
    _ ≤ p.length * R*Z:= mul_le_mul_of_nonneg_left hg (mul_nonneg (Nat.cast_nonneg _) hr)
    _ = ((p.length*e)*R)*(Z/e):=by field_simp
    _ ≤ _:=by change (p.length*e)*R*(Z/e)≤ ((p.length*e+1)*R)*(Z/e); apply mul_le_mul_of_nonneg_right _ (div_nonneg (deal_pos ..) h.le); exact mul_le_mul_of_nonneg_right (by simp) hr
end YM.CF.Peaks
