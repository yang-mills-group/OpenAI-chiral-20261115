import YM.SU5.Assay.Credits
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)
/-! More hold law. -/
lemma sand_sub (A B:H.Op)(a b:ℝ): S.sand (A-B) a b = S.sand A a b-S.sand B a b:=by unfold sand; rw [mul_sub,sub_mul]
lemma sand_add (A B:H.Op)(a b:ℝ): S.sand (A+B) a b = S.sand A a b+S.sand B a b:=by unfold sand; rw [mul_add,add_mul]
lemma sand_smul (A:H.Op)(z:ℂ)(a b:ℝ): S.sand (z•A) a b = z•S.sand A a b:=by unfold sand; rw [mul_smul_comm,smul_mul_assoc]
lemma sand_norm_limit {I:Type*}{l:Filter I}{a b:ℝ}{f g:I→ℝ}{A:H.Op}{m:I→H.Op}
 (h:0<a)(t:0<b)(p:Tendsto m l (𝓝 A))(u:Tendsto f l (𝓝 a))(v:Tendsto g l (𝓝 b)):
 Tendsto (fun i=>S.sand (m i) (f i) (g i)) l (𝓝 (S.sand A a b)):=
    (((S.wax_cont h).tendsto.comp u).mul p).mul ((S.wax_cont t).tendsto.comp v)
variable {S}{w a b c d:ℝ}{T:ℝ→ℝ→H.Op}
lemma Credits.sub_pay {u:ℝ}{R:ℝ→ℝ→H.Op}(p:S.Credits w T)(q:S.Credits u R)
   (h:max w u<a)(t:max w u<b)(v:a≤c)(y:b≤d):
 ‖T c d-R c d‖≤‖T a b-R a b‖:=by
 obtain ⟨j,k⟩:=max_lt_iff.mp h;obtain ⟨i,m⟩:=max_lt_iff.mp t
 rw [p j i v y,q k m v y,←S.sand_sub];exact S.sand_pay ..
lemma Credits.paid {I:Type*}{l:Filter I}[NeBot l]{u:I→ℝ}{G:I→ℝ→ℝ→H.Op}
  (p:Tendsto u l (𝓝 w))(q:∀ᶠ i in l,S.Credits (u i) (G i))
  (h:∀ a>w,∀ b>w,Tendsto (fun i=>G i a b) l (𝓝 (T a b))):
 S.Credits w T:=Credits.earned p q (fun _ a _ b=> BSOT.fromNorm (h _ a _ b))
lemma Credits.norm_on {I:Type*}{l:Filter I}[NeBot l]{u:I→ℝ}{G:I→ℝ→ℝ→H.Op}
  (p:Tendsto u l (𝓝 w))(q:∀ᶠ i in l,S.Credits (u i) (G i))
  (h:∀ a>w,∀ b>w,Tendsto (fun i=>G i a b) l (𝓝 (T a b)))
  {f g:I→ℝ}(ha:w<a)(hb:w<b)(v:Tendsto f l (𝓝 a))(z:Tendsto g l (𝓝 b)):
 Tendsto (fun i=>G i (f i) (g i)) l (𝓝 (T a b)):=by
 obtain ⟨s,w',s'⟩:=exists_between (lt_min ha hb); obtain ⟨ha,hb⟩:=lt_min_iff.mp s'
 rw [Credits.paid p q h w' w' ha.le hb.le]
 apply (S.sand_norm_limit (sub_pos.mpr ha) (sub_pos.mpr hb) (h s w' s w') (v.sub_const s) (z.sub_const s)).congr'
 filter_upwards [p.eventually (gt_mem_nhds w'),v.eventually (le_mem_nhds ha),z.eventually (le_mem_nhds hb),q] with i k n m e; exact (e k k n m).symm
end YM.OS.Semigroup
