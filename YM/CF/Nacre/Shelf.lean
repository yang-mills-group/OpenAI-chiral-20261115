import YM.CF.Nacre.Halo
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
import YM.Next.STATIONARY.OneLoop.WilsonVertices
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Bloch Font
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal Matrix Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}
def ramps(x:Site n)(u:InputZ G n)(s:ℝ)(i:Site n) : G.El:= G.lieExp (s • sap x (collect G u) i)
def bend(x:Site n)(u:InputZ G n)(s:ℝ):=Lattice.gauge (ramps x u s) (represent (s • u))
@[simp] lemma ramps_0(x:Site n)(u:InputZ G n): ramps x u 0=1:=funext fun i=> by change G.lieExp _=1; simp
@[simp] lemma bend_0(x:Site n)(u:InputZ G n): bend x u 0=1:=by funext i; simp [bend,Lattice.gauge]
lemma tide_p(x:Site n)(u:InputZ G n)(i:Edge (Site n)): ContDiffAt ℝ ω (fun t=> G.mat (bend x u t i)) 0:=by
 let f(t:ℝ)(i: Site n):= ramps x u t i
 unfold bend Lattice.gauge; have hx(j:Site n):ContDiffAt ℝ ω (fun t:ℝ=> G.mat (ramps x u t j)) 0 := (G.exp_jet.contDiffAt.comp (f:=fun t=>t • sap x _ j) 0 (by fun_prop))
 simp_rw [G.mat_mul, G.mat_inv]; exact ((hx _).mul ((Work.F03.represent_smooth i).contDiffAt.comp (f:=fun t=> t • u) 0 (by fun_prop))).mul ((starL ℝ:G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (hx _))
lemma vane(x:Site n)(u:InputZ G n)(i:Edge (Site n)): HasDerivAt (fun t=> G.mat (bend x u t i)) (G.colorMat (collect G (fullG x u) i)) 0:=by
 unfold bend Lattice.gauge
 have he(j): HasDerivAt (fun t:ℝ=> G.mat (ramps x u t j)) (G.colorMat (sap x (collect G u) j)) 0:=by
    let V:=sap x (collect G u) j
    exact (show HasFDerivAt (fun i:G.Color=> G.mat (G.lieExp i)) _ ((0:ℝ) • V) from (show ((0:ℝ) • V)=0 from zero_smul ..) ▸ G.expDiff_zero).comp_hasDerivAt 0 (show HasDerivAt (fun z:ℝ=> z • V) V 0 from (((hasDerivAt_id' (0:ℝ)).smul_const V).congr_deriv (by simp)))
 simp_rw [G.mat_mul,G.mat_inv];
 convert! ((he _).mul (Work.F03.represent_rate u i)).mul (he _ |>.star) using 1
 rw [sampleX]; simp only [ramps_0,zero_smul,link_one,Pi.one_apply,G.mat_one,mul_one,one_mul,G.colorMat_skew,star_one,Pi.sub_apply,Font.pure,map_sub]; unfold collect; dsimp; simp only [ramps_0,Pi.one_apply,zero_smul,link_one,G.mat_one,one_mul]; abel

def race(x:Site n)(u:InputZ G n)(s:ℝ): InputZ G n:= fun i=>G.plog (G.mat (bend x u s ((Trot _).symm i)))
lemma roundS(x:Site n)(u:InputZ G n): race x u 0=0:=by ext1 i; unfold race; rw [bend_0, Pi.one_apply,G.mat_one,G.plog_one]; rfl
lemma sport(x:Site n)(u:InputZ G n): ContDiffAt ℝ ω (race x u) 0:= by refine contDiffAt_pi.mpr fun i=>?_ ; let f(t:ℝ):=G.mat (bend x u t ((Trot _).symm i)); exact (show ContDiffAt ℝ ω G.plog (f 0) by unfold f; rw [bend_0,Pi.one_apply,G.mat_one]; exact G.plog_diff).comp (f:=f) _ (tide_p x u _)
lemma tough(x:Site n)(u:InputZ G n): HasDerivAt (race x u) (fullG x u) 0:=by
 refine hasDerivAt_pi.mpr ?_; intro i; obtain ⟨e,rfl⟩:=(Trot n).surjective i
 have he:(fun t=> race x u t (Trot n e))=(fun t=>G.plog (G.mat (bend x u t e))):=by funext t; simp only [race,Equiv.symm_apply_apply]
 rw [he]; let f(t):=G.mat (bend x u t e); have hx : HasFDerivAt G.plog (fderiv ℝ G.plog 1) (f 0) :=by unfold f; rw [bend_0, Pi.one_apply,G.mat_one]; exact (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
 have hp:=hx.comp_hasDerivAt (0:ℝ) (vane x u e); exact hp.congr_deriv (Stationary.echo_clr (collect G (fullG x u) e))
lemma wraps(x:Site n)(u:InputZ G n): ∀ᶠ t in 𝓝 (0:ℝ),represent (race x u t)= bend x u t:=by
 have ht(i:Edge (Site n)): ∀ᶠ t in 𝓝 0, represent (race x u t) i=bend x u t i:=by
    have he:Tendsto (fun t=> bend x u t i) (𝓝 (0:ℝ)) (𝓝 (bend x u 0 i)):= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (tide_p x u i|>.continuousAt)
    rw [bend_0, Pi.one_apply] at he; filter_upwards [he.eventually G.plog_right] with t ht; rw [Work.F03.represent_link]; change G.lieExp (race x u t (Trot n i)) = _; simp only [race,Equiv.symm_apply_apply]; exact ht
 filter_upwards [eventually_all.mpr ht] with j hj; exact funext hj
lemma orderD (g:SU.E)(V:Cloud n)(t:ℝ): represent (t • MarkT g V)= Lattice.gauge (fun _=>g) (represent (t • V)):=by
 funext x; simp_rw [Work.F03.represent_link] -- RHS under
 rw [Lattice.gauge,Work.F03.represent_link]; change SU.group.lieExp (t • SU.group.adjoint g _) = _; rw [← map_smul]; exact ProjectorNext.Equivariance.exp_adjoint ..
lemma height(x:Cloud n)(t:Cover)(s:ℝ): represent (s • SubMotion t x)= Yg (lagX t) (represent (s • x)):=by funext i; rw [Ylag]; simp only [Lattice.translate,Work.F03.represent_link,SubMotion]; rfl
end YM.CF.Nacre
