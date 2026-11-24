
import YM.Work.E08
import YM.Work.F03.Transport
import YM.Next.RANK.Ray
set_option autoImplicit false
noncomputable section
namespace YM.CF.Organdy.Payne
open Function Lattice Pressure Wilson Precision Work.F03 Next.Rank.Spindle Exterior
open Filter Topology
open scoped Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}{k:ℕ}{o:Site n}
def stretch (k:ℕ):ℝ:=16*(2*((k+1:ℕ):ℝ)+1)^5*Fintype.card PlaqAxes * 2
lemma stretchPos (k:ℕ):0<stretch k:=by
 haveI:Nonempty PlaqAxes:=⟨⟨(0,1),by decide⟩⟩;unfold stretch;positivity
lemma stretchMono {k l:ℕ}(v:k≤l): stretch k≤stretch l:=by unfold stretch;gcongr

abbrev Cheap (o:Site n)(k:ℕ)(U:Config G n)(t:ℝ):Prop :=
 ∀i:Cell n, separation o i.1 ≤ k+1 → G.chord (faceValue U i) ≤ t

lemma dawn {V:Config G n}{t:ℝ}
   (R:Rules G)(p:2*(k+1)<n.val)(t0:0≤t)(v:stretch k*t < R.c)(h:Cheap o k V t):
   ∃ (u:Site n→G.El)(Y:fieldDir G n 1),
   ‖Y‖ ≤ stretch k*t ∧ ∀e:Edge (Site n), separation o e.1 ≤ k →
     gauge u V e= represent Y e :=by
 obtain ⟨g,q⟩:= Work.E08.axial_patch o V _ _ le_rfl p t t0 (fun i a j=>h (i,j) a)

 let Z(e:Edge (Site n)):=if separation o e.1 ≤ k then gauge g V e else 1
 have hf(e):2*G.chord (Z e)≤ stretch k*t:=by
   by_cases u:separation o e.1≤k
   · rw [show Z e=gauge g V e from if_pos (by exact u : separation o e.1 ≤ k)]
     exact (mul_le_mul_of_nonneg_left (q e u) two_pos.le).trans_eq (by unfold stretch;ring)
   have a:G.chord (Z e) = 0:= by rw [show Z e=1 from if_neg u];simp [Gauge.chord]
   rw [a,mul_zero];exact mul_nonneg (stretchPos _).le t0
 have hc(e):G.chord (Z e)≤R.c:=by linarith only [v,hf e,G.chord_nonneg (Z e)]
 let Y:fieldDir G n 1:=fun e=>G.plog (G.mat (Z (e.1,axisEquiv.symm e.2)))
 refine ⟨g,Y,(pi_norm_le_iff_of_nonneg (mul_nonneg (stretchPos _).le t0)).mpr
      (fun e=>(R.sleeve _ (hc _)).trans (hf (e.1,axisEquiv.symm e.2))),?_⟩
 intro e u
 have H:collect G Y e= G.plog (G.mat (Z e)):=by
   unfold collect Y
   rw [←coord_map, axisEquiv.symm_apply_apply]
 rw [represent,RG.increment,H,R.records _ (hc e),Pi.one_apply,mul_one]
 exact (if_pos u : Z e =gauge g V e).symm

lemma cheapShots (X:fieldDir G n 1)(M:ℝ)
 (f:∀i:Cell n,separation o i.1≤k+1 → ‖faceCurl i X‖ < M):
 ∀ᶠ t:ℝ in 𝓝[>] 0, Cheap o k (represent (t•X)) (t*M):=by
 refine eventually_all.mpr ?_
 intro i
 by_cases g:separation o i.1 ≤ k+1;swap;· exact Eventually.of_forall fun t y=>False.elim (g y)
 let Z(t:ℝ):= faceValue (represent (t•X)) i
 have z0:Z 0=1:=by unfold Z;rw [zero_smul];exact Push.stroll_zero ..
 have hm : Tendsto (fun t : ℝ => t⁻¹ • (G.mat (Z t) - 1)) (𝓝[>] 0) (𝓝 (G.colorMat (faceCurl i X))) := by
    have h: HasDerivAt (fun t => G.mat (Z t)) (G.colorMat (faceCurl i X)) 0 := face_deriv i X
    refine Tendsto.mono_left ?_ (nhdsGT_le_nhdsNE _)
    simpa only [zero_add, z0, G.mat_one] using! (hasDerivAt_iff_tendsto_slope_zero.mp h)
 have he := hm.norm.div_const G.colorScale
 rw [G.colorMat_norm, mul_div_cancel_left₀ _ G.colorScale_pos.ne'] at he
 filter_upwards [he.eventually (gt_mem_nhds (f i g)),self_mem_nhdsWithin] with t h n
 change 0<t at n
 simp only [norm_smul, mul_div_assoc,norm_inv,Real.norm_eq_abs,abs_of_pos n] at h
 exact fun _=>(inv_mul_lt_iff₀ n|>.mp h).le
