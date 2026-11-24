import YM.SU5.Reconstruction.Trap.Hill
import YM.SU5.Reconstruction.Cone.AxisCheck
/-!
# Minimum test of UNBROKEN translational normalization: ask only EXACT ray probes (+t, t), v for any k. Necessary for Canon & sufficient for its continuity & axial temporal coordinate light.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real
variable {H : Hilbert} {a : Axis} {Γ : AddSubgroup ℝ} (S : OS.Semigroup H a)
variable (d : Dense (Γ:Set ℝ)) (X : Sunbelt a Γ H)
  (g : ∀ i,∀ (z : Γ) (t:ℝ≥0), ((X.track.crew i).play z).comp (S.E t)=(S.E t).comp ((X.track.crew i).play z))
local notation "Gt" => (Axis→Γ)
local notation "C₀" => X.track.aviator X.list
local notation "U" => glass X d S g
local notation "G₀" => X.track.Realm X.list
local notation "H₀" => H.space
local notation "D₁" => {i:Axis//i≠a}
noncomputable def byStamp (a b:Axis)(s:Γ): Axis→Γ:= Function.update (Function.update 0 a s) b s
local notation "Z" u:max s:max=> byStamp a u s
def PacePrice(e:ℝ):Prop := ∀ i:{i:Axis//i≠a},∀ z:Γ,0<(z:ℝ)→ (z:ℝ)<e → ∀ v:H,
   let u:=byStamp a i.val z
   let t:= (face u a).toNNReal
   ‖(S.E t) (transverse_play X u v)- S.E t v‖ ≤ ‖v-S.E t v‖
variable {ε:ℝ}(p:0 < ε)(q:PacePrice S X ε)
include p q
open Measure InnerProductSpace
omit X p q in
private lemma surf (e : ℝ) (p : E4) (b : 0 < e) (x : Cross a)
    (he : ∀ t : ℝ≥0, 0 < t → (t:ℝ)<e → tension ((t:ℝ) • x) t p ≤ 0) :
    (inner ℝ (SEP a p) x)^2 ≤ (p a)^2 := by
  let q:= inner ℝ (SEP a p) x
  let d := fun t:ℝ => exp (-(p a)*t)
  let f(t:ℝ):ℝ:= 2 * Real.sin (t*(q/2))*d t; let g(t:ℝ):ℝ:=1-d t
  have e₀ : d 0=1:= by simp [d];
  have f₀ : f 0=0:= by simp [f]
  have g₀ : g 0=0:= by simp [g,e₀]
  have hd : HasDerivAt d (-(p a)) 0 := by simpa [d] using (((hasDerivAt_id' (0:ℝ)).const_mul (-(p a))).exp)
  have hf : HasDerivAt f q 0 := by
    convert ((((hasDerivAt_id' (0:ℝ)).mul_const (q/2)).sin.const_mul 2).mul hd) using 1 <;> try rfl
    simp [e₀]; ring
  have hg : HasDerivAt g (p a) 0 := by simpa [g] using (hd.const_sub 1)
  apply le_of_tendsto_of_tendsto (hf.tendsto_slope_zero_right.pow 2) (hg.tendsto_slope_zero_right.pow 2)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds b)] with t v ht
  change (t⁻¹ • (f (0+t) - f 0))^2 ≤(t⁻¹ • (g (0+t)-g 0))^2
  simp only [f₀,g₀,sub_zero,smul_eq_mul,mul_pow,zero_add]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  let bt : 0 < t := v
  have H₁:=he ⟨t,bt.le⟩ (show 0<(⟨t,bt.le⟩:ℝ≥0) from bt) ht
  erw [trig_rel, sub_nonpos, real_inner_smul_right (SEP a p) x t] at H₁
  dsimp only [f,g,d,q]; rw [← mul_div_assoc]; exact H₁
include d g
lemma cost_paces (i: D₁): Paces i.val (glass X d S g):= by
 let P:=cross a i.val i.property; let A:=glass X d S g
 have he(p:Γ)(hp:0<(p:ℝ))(b:(p:ℝ)<ε)(x:G₀): ‖(A.U ((p:ℝ) • P)) (A.E (p:ℝ).toNNReal x) - A.E (p:ℝ).toNNReal x‖ ≤ ‖x-A.E (p:ℝ).toNNReal x‖:= by
   let u:=byStamp a i p; have ht:= (buy_clear S d X g x u).2 (q i p hp b x.val)
   obtain ⟨a,b,u⟩:= spotlight2 X p i p; unfold clears at ht
   rw [show diameter (a:=(show Axis from _)) (face (byStamp _ i.val p))=(p:ℝ) • P from Subtype.ext a,show face (byStamp _ i p) _ =_ from b] at ht; exact ht
 -- use continuity along just the ray
 have hc(t:ℝ≥0)(s:0<t)(b:(t:ℝ)<ε)(x:G₀) : ‖(A.U ((t:ℝ) • P)) (A.E t x)-(A.E t x)‖≤ ‖x-(A.E t x)‖:= by
   let y(w:ℝ):= A.E w.toNNReal x; have hp:Continuous y:= (A.continuousE _).comp continuous_real_toNNReal
   have ht: IsClosed {w:ℝ|‖(A.U (w • P)) (y w)-y w‖≤‖x-y w‖}:= isClosed_le (((A.cont_cross _ (fun x:ℝ=> x • P) hp (by fun_prop)).sub hp).norm) ((continuous_const.sub hp).norm)
   have hh: (t:ℝ)∈ {w:ℝ|‖(A.U (w • P)) (y w)-y w‖≤‖x-y w‖}:= closure_minimal ?_ ht (isOpen_Ioo.closure_inter ⟨d _,(show (t:ℝ)∈ Ioo 0 ε from ⟨by exact_mod_cast s,b⟩)⟩)
   · simpa [y] using hh
   rintro w ⟨p,v⟩; exact he ⟨w,p⟩ v.1 v.2 x
 intro x y ay; have hg: |y i.val|^2 ≤ (y a)^2:= by
    have hy (t:ℝ≥0) (p:0<t) (b:(t:ℝ)<ε) : tension ((t:ℝ) • P) t y ≤ 0 := tension_point A _ t (hc t p b) x y ay
    have hb: inner ℝ (SEP a y) P=y i.val:= by rw [← ConePrice.cone_mean]; exact innerB ..
    rw [sq_abs, ←hb]; exact surf _ y p P hy
 exact (sq_le_sq₀ (abs_nonneg _) (show 0≤y a from (U).nonneg x ay)).mp hg
include g
omit d
lemma cost_room: C₀=⊤:= by
 apply le_antisymm le_top; intro x _; apply (X.track.assembled X.list x).2; intro i k
 let E:= X.track.crew i
 let f(w:Γ):= E.play w x
 apply E.living.mpr; intro e v
 have he : ∀ᶠ v in 𝓝 (0:ℝ), dist x (S.E v.toNNReal x) < e/3 ∧ v < ε:= by
   have h1:= (show Continuous fun v:ℝ=> dist x (S.E v.toNNReal x) from continuous_const.dist ((S.continuousE _).comp continuous_real_toNNReal)).tendsto 0
   apply Eventually.and _ (gt_mem_nhds p)
   apply h1.eventually (p:=fun y=> y<e/3); simp only [Real.toNNReal_zero,S.eZero,ContinuousLinearMap.id_apply, dist_self]; exact gt_mem_nhds (by linarith)
 obtain ⟨t,b,u⟩:= Metric.mem_nhds_iff.mp he
 have hv (z:Γ)(w:0<(z:ℝ))(s:|(z:ℝ)|<t): dist (E.play z x) x < e:= by
    let T:=(z:ℝ).toNNReal; obtain ⟨h₁,h₂⟩:=(show dist x (S.E T x)<e/3∧ (z:ℝ)<ε from u (show (z:ℝ)∈ ball 0 t from mem_ball.mpr (by simpa using s)))
    have hp:= q i z w h₂ x; obtain ⟨_,hz,hk⟩:= spotlight2 X z i z; dsimp only at hp; unfold byStamp at hp; rw [hz,hk] at hp
    have ht : dist (E.play z (S.E T x)) (S.E T x)<e/3:= by rw [dist_eq_norm] at *; apply lt_of_le_of_lt _ h₁; unfold E; rw [← ContinuousLinearMap.comp_apply,g]; exact hp
    calc
     _ ≤ dist (E.play z x) (E.play z (S.E T x))+dist (E.play z (S.E T x)) x:= dist_triangle ..
     _ ≤ dist x (S.E T x)+(dist (E.play z (S.E T x)) (S.E T x)+dist (S.E T x) x):= by rw [E.rigid H]; gcongr; exact dist_triangle ..
     _ < e:= by rw [dist_comm _ x]; linarith
 refine ⟨t,b,fun w d=>?_⟩; rcases lt_trichotomy (0:ℝ) (w:ℝ) with v'|v'|v'
 · exact hv w v' d
 · have u:w=0:= Subtype.ext v'.symm; rw [u]; simpa only [E.play_zero,ContinuousLinearMap.id_apply,dist_self]
 have u:=E.returns H w x; rw [← E.rigid H (-w) _ _, E.returns, dist_comm]; exact hv _ (neg_pos.mpr v') (by simpa using d)
omit g p q
include X
lemma starch (i:D₁)(z:Γ)(p:0<(z:ℝ))(u:(z:ℝ)< ε) : face (byStamp a i.val z) ∈ CostDomain a ε:= by
 let S:=byStamp a i.val z
 obtain ⟨d,v,t⟩:= spotlight2 X z i z; change 0<face S a ∧ ‖(diameter (a:=a) _).val‖ ≤ face S a ∧ face S a<ε; unfold S byStamp; rw [v,d]; refine ⟨p,?_,u⟩; rw [norm_smul]; simp [Real.norm_eq_abs,abs_of_pos p]
end YM.Picket
