import YM.CF.BProof.Floral.Hol
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology NNReal ENNReal
namespace YM.CF.Floral
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E] {L C:ℝ}{f:ℂ→E}
abbrev disk (r:ℝ):=ball (0:ℂ) r
lemma d0 (p:1<L): (0:ℂ)∈disk L:=mem_ball_self (zero_lt_one.trans p)
lemma d1 (p:1<L): (1:ℂ)∈disk L:=by simpa [disk] using p
lemma norm_chord_le (p:1<L)(H:Hol (disk L) f)(w:∀ z∈disk L,‖f z‖≤C):‖f 1-f 0‖ ≤ C / (L-1):=by
 have h0:0<L-1:=sub_pos.mpr p
 apply ge_of_tendsto (tendsto_const_nhds.div (f:=fun _:ℝ=>C) (show Tendsto id (𝓝[<] (L-1)) (𝓝 (L-1)) from nhdsWithin_le_nhds) h0.ne')
 filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds h0)] with r hr ht
 change r<L-1 at hr; change 0<r at ht; let K:=closedBall (0:ℂ) 1; have he(y:ℂ)(q:y∈K):closedBall y r ⊆ disk L:= fun z hz=> mem_ball.mpr <| by
    have h:=dist_triangle z y 0; have ha:=mem_closedBall.mp hz; have hb:=mem_closedBall.mp q; linarith
 have hw(y)(q:y∈K): y∈disk L := he y q (mem_closedBall_self ht.le)
 simpa using (convex_closedBall (0:ℂ) 1).norm_image_sub_le_of_norm_deriv_le (fun x g=> H.differentiableAt (isOpen_ball.mem_nhds (hw x g))) (fun x g=> c_deriv H ht (he x g) w) (mem_closedBall_self (by norm_num)) (show (1:ℂ)∈K from (by simp [K]))
end YM.CF.Floral
