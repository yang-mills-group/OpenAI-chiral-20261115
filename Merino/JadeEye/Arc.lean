import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Metric Filter
open scoped Matrix.Norms.Frobenius Topology ContDiff
variable (G:Gauge)

structure Lip (G:Gauge) (v C:ℝ):Prop where
  pos:0<v
  cost:1≤C
  read (u:G.El):G.chord u≤v → G.lieExp (G.plog (G.mat u))=u ∧ ‖G.plog (G.mat u)‖≤C*G.chord u

lemma lip : ∃ v C,Lip G v C:=by
 obtain ⟨K,t,u,p⟩:=ContDiffAt.exists_lipschitzOnWith (G.plog_diff.of_le (m:=1) le_top)
 have a: ∀ᶠ y in 𝓝 (1:G.El), G.mat y∈t := G.continuous_mat.continuousAt (x:=1) |>.tendsto.eventually u
 obtain ⟨b,r,w⟩:=nhds_basis_closedBall.eventually_iff.mp (G.plog_right.and a)
 -- metric
 let d:= Real.sqrt G.repDim
 have hd:0<d:=Real.sqrt_pos.mpr (by exact_mod_cast G.dimPos)
 refine ⟨b/d,max 1 (K*d),by positivity,le_max_left ..,?_⟩
 intro y k
 have e: ‖G.mat y-1‖≤b:= (div_le_div_iff_of_pos_right hd).mp k
 have g:=w (show y∈ closedBall 1 b from mem_closedBall.mpr (show dist (G.mat y) (1:G.Mat) ≤ b by rwa [dist_eq_norm]))
 have h := p.dist_le_mul _ g.2 _ (mem_of_mem_nhds u)
 rw [G.plog_one,dist_zero_right,dist_eq_norm] at h
 refine ⟨g.1,h.trans (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (G.chord_nonneg _)))⟩
 change _ ≤ (K:ℝ)*d*(‖G.mat y-1‖/d)
 rw [mul_assoc,mul_div_cancel₀ _ hd.ne']

