import YM.SU5.Reconstruction.Crease.Dance
import YM.SU5.Reconstruction.UVPrice.Temper
import YM.SU5.Reconstruction.Trap.Invariant
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame OS Semigroup Real Roy Boundary Club
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H D K:Hilbert}{C:Clasp K H D}{M:Net H}{Ω:H}{Γ:Set H.Op}{J:Flash H}(h: Club C J M Ω Γ)
include h
lemma soot {A:H.Op} (p:A∈ M)(q:A∈M.commutant)(t:ℝ) : Picket.boost C t (A Ω)=A Ω:= by
 let L:= C.plume; let R:=C.shadow; let x:= A Ω; let y:=J.f (star A Ω); have hu:L x=R y:= h.reverse _ q; have ht:L y=R x:= h.charge _ p; have he : L (x-y)= R (y-x):= by rw [map_sub,map_sub,hu,ht]
 have hxy:x-y=0:= by rw [← show L (x-y)+R (x-y)=x-y from DFunLike.congr_fun C.unites _,he,←map_add]; simp -- rewriting replacements
 have hv:L x= ((1/2:ℝ):ℂ) • x:=by
    have hk : L x= R x:= hu.trans (congrArg R (sub_eq_zero.mp hxy).symm); have ht: L x+L x=x:= by
       conv_lhs=> rhs; rw [hk]; -- layout
       exact DFunLike.congr_fun C.unites _
    -- way
    rw [← two_smul ℂ (L x)] at ht; nth_rw 2 [← ht]; rw [smul_smul]; norm_num
 obtain ⟨s,hs⟩:=C.Left.surjective (A Ω); change L (A Ω)= _ • (A Ω) at hv; rw [← hs] at hv ⊢; unfold L at hv; rw [(Club.pearlA C s).1, ← map_smul] at hv; exact logOne _ _ (C.Left.injective hv) t
variable {a b:Axis}(r:b≠a)(S:OS.Semigroup H a)(p:∀ u x,Picket.boost C u* trans S x=trans S (move a b u x)*Picket.boost C u)
local notation "Φ" t:max=> Picket.boost C t
local notation "U"=>Picket.trans S
omit h
include r p
omit r p in
private abbrev nerve (a b:Axis)(u:ℝ):= basis a+u • basis b
-- p demand all u. on ± boosts costs to 0 directly. no Fourier support statement.
lemma ember (x:H)(q:∀ u,Picket.boost C u x=x)(t:ℝ): cue S x=x:= by -- t unused: only memGround
 have he(i:E4)(u:ℝ): inner ℂ x (U i x) = inner ℂ x (U (move a b u i) x):= by
    let B:= Picket.boost C u; -- h
    rw [← (Picket.boost_pays C u).ordinary x]; rw [show B (U i x)=U _ (B x) from DFunLike.congr_fun (p u i) x]; simp only [B] at *; rw [q] -- unfold
 have hy (k:ℝ)(t:ℝ)(hk:k*k=1) : U (t • nerve a b k) x=x:= by
    let y := t • nerve a b k; have hb(u:ℝ):move a b u y = (cosh u + k*sinh u) • y:=by
       ext1 i; rcases eq_or_ne i a with ht|ht'; · subst i; rw [eye_high r]; unfold y nerve; simp [r, Ne.symm r]; ring
       rcases eq_or_ne i b with ht|ht; · subst i; rw [eye_low r]; unfold y nerve; simp [r,Ne.symm r]; linear_combination -(sinh u*t)*hk
       rw [others _ _ _ ht' ht]; unfold y nerve; simp [*]
    have hc(u:ℝ):move a b (k * u) y= Real.exp u • y:= by
       rw [hb]; have hv:k=1∨k=-1:= eq_or_eq_neg_of_sq_eq_sq k 1 (by nlinarith) -- tune
       rcases hv with k|k <;> rw [k] <;> congr 1 <;> simp [cosh_eq,sinh_eq] <;> ring
    have ht:Tendsto (fun u:ℝ=> move a b (k * u) y) atBot (𝓝 0):=by simp_rw [hc]; simpa using (Real.tendsto_exp_atBot.smul (tendsto_const_nhds (x:=y)))
    have hh:inner ℂ x (U y x) =inner ℂ x x:= by
       have hs : U (0:E4) x=x:= DFunLike.congr_fun S.unit.origin x
       refine Eq.trans (b:=inner ℂ x (U (0:E4) x)) ?_ (congrArg _ hs)
       exact tendsto_nhds_unique_of_eventuallyEq (l:=atBot) tendsto_const_nhds (tendsto_const_nhds.inner (((S.unit.moves x).continuousAt.tendsto).comp ht)) (Eventually.of_forall fun i:ℝ=> he y (k * i)) -- l binder
    apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; change inner ℂ (U y x-x) (U y x-x)=_; simp_rw [inner_sub_left,inner_sub_right,(mobile _ y).ordinary]; rw [show inner ℂ (U y x) x=inner ℂ x x from ?_,hh]; ring
    rw [← inner_conj_symm, hh, inner_conj_symm]
 rw [cue_ground]; apply S.ground.starProjection_eq_self_iff.mpr; refine Boundary.offiero S x ?_
 intro i; rw [show i • basis a=(i/2) • nerve a b 1+(i/2) • nerve a b (-1) from (by unfold nerve; module),← S.unit.sends,ContinuousLinearMap.comp_apply]
 exact Eq.trans (congrArg _ (hy (-1) (i/2) (by ring))) (hy 1 _ (one_mul _))
variable (g: Hearth S Ω)
include h g
lemma clearCenter {A:H.Op} (k:A∈M)(v:A∈M.commutant): ∃ z:ℂ,A=z • (1:H.Op):= by
 let x:= A Ω; use inner ℂ Ω x; apply sub_eq_zero.mp; apply h.cheap (sub_mem k (m_smul _ (one_mem M)))
 change _-(inner ℂ Ω x) • Ω=0; exact sub_eq_zero.mpr ((ember r S p x (fun u=> soot h k v u) 0).symm.trans (g x))
end YM.BridgeClub
