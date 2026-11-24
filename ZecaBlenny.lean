import ZecaStickle
import ZecaEaglefin
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary




variable {n:Gaia}{s α:ℝ}{z:ℂ}{colA:PlaqAxes→ℝ}{G:Gauge}

lemma blenNet (d:‖n‖=1) (sp:1≤ s)
 (u:0<α)(q:α<1):
 fishNet (Kelper colA G n s) (α*s) (stickleFee colA G (1-α^2)⁻¹):=by
 have pos:0< s:=one_pos.trans_le sp
 refine ⟨mul_pos u pos, fun x=>?_⟩
 have a(y:ℂ) (hy:y∈closedBall (x:ℂ) (α*s)):|y.im|≤α*s:=by
   have h:= mem_closedBall.mp hy
   rw [dist_eq_norm] at h
   simpa using (Complex.abs_im_le_norm _).trans h
 refine ⟨DifferentiableOn.diffContOnCl_ball ?_ (Subset.rfl),fun y hy=>
   stickle_priced colA G d sp u.le q (a y (mem_closedBall.mpr <| (mem_sphere.mp hy).le))⟩
 apply satire_d
 refine ⟨fun i=>?_,?_,fun y hy=>?_⟩
 · unfold current; split <;> fun_prop
 · unfold currentQ;fun_prop
 apply norm_pos_iff.mp
 refine lt_of_lt_of_le ?_ (kelp_room pos.le u.le q (a y hy)).2
 have b:0<1-α^2:=sub_pos.mpr (pow_lt_one₀ u.le q (by decide))
 positivity

variable {H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H]
theorem blenny (d:‖n‖=1)(v:n 3=0)
 (sp:1≤ s) {h:ℝ} (d':0<h) {x:ℕ→ℕ→ℤ→H}
 (z:∀t:ℕ,knocks (fun i=>x i t) h (fun y=>spectrumℓ colA G (wake n (s+2*t) y))):
 fishing x h:=by
 refine ⟨d',fun T tp l =>
   ⟨stickleFee colA G (1-(T/2)^2)⁻¹,fun t=>?_⟩⟩
 have a:1≤ s+2*t:=by linarith only [sp,t.cast_nonneg (α:=ℝ)]
 refine ⟨_,?_,_, blenNet d a (show 0<T/2 by linarith) (by linarith),?_⟩
 · nlinarith only [mul_pos (show 0< s by linarith) tp]
 intro i j
 dsimp only
 rw [← kelping _ _ v d (by linarith : s + 2 * ↑t ≠ 0)]
 exact z t i j
#print axioms blenny
