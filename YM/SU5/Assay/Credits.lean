import YM.SU5.Assay.Spacers
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)
/-! Currency of operators conditioned on two purchased lags, open interval.
 `Credits w` means threshold `w` for using without clip. -/
local notation "ω"=>S.wax
local notation "Lag"=>ℝ→ℝ→H.Op
def hang (w:ℝ)(A:H.Op):Lag:= fun a b=>S.sand A (a-w) (b-w)
def Credits (w:ℝ) (T:ℝ→ℝ→H.Op) : Prop :=
  ∀ {a b c d:ℝ}, w<a → w<b → a≤c → b≤d → T c d=S.sand (T a b) (c-a) (d-b)
variable {w a b c d:ℝ}{T:ℝ→ℝ→H.Op}
lemma Credits.hang (A:H.Op)(w:ℝ): S.Credits w (S.hang w A):=
   fun {_ _ _ _} p q t h=> S.sand_step p.le q.le t h A
lemma hang_pay (A:H.Op)(w a b:ℝ): ‖S.hang w A a b‖≤ ‖A‖:=S.sand_pay ..
lemma hang_at (A:H.Op)(w:ℝ): S.hang w A w w=A:=by unfold hang sand; rw [sub_self,wax_zero,one_mul,mul_one]
lemma hang_slide {I:Type*}{l:Filter I}{a b:ℝ}{f g:I→ℝ}{A:H.Op}
   (w:ℝ)(p:Tendsto f l (𝓝 a))(q:Tendsto g l (𝓝 b)):
   BSOT (fun i=> S.hang w A (f i) (g i)) l (S.hang w A a b):=
   S.sand_limit (BSOT.stay _) (p.sub_const w) (q.sub_const w)
variable {S}
lemma Credits.pay (p:S.Credits w T)(q:w<a)(u:w<b)(v:a≤c)(y:b≤d): ‖T c d‖≤ ‖T a b‖:=by rw [p q u v y]; exact S.sand_pay ..
lemma Credits.pay₂ {ε:ℝ}(p:S.Credits w T)(h:w<ε)(q:ε≤a)(u:ε≤b): ‖T a b‖≤ ‖T ε ε‖:= p.pay h h q u
lemma Credits.dagger (p:S.Credits w T):S.Credits w (fun a b=>star (T b a)):=by
 intro a b c d u v y z; dsimp only; rw [p v u z y,OS.Semigroup.sand_star]
lemma Credits.mono (p:S.Credits w T)(q:w≤a):S.Credits a T:=fun {_ _ _ _} u v=>p (lt_of_le_of_lt q u) (lt_of_le_of_lt q v)
lemma Credits.norm_slide {I:Type*}{l:Filter I}{f g:I→ℝ}(p:S.Credits w T)
 (h:w<a)(t:w<b)(u:Tendsto f l (𝓝 a))(v:Tendsto g l (𝓝 b)):
 Tendsto (fun i=>T (f i) (g i)) l (𝓝 (T a b)):=by
 obtain ⟨s,w',s'⟩:=exists_between (lt_min h t); obtain ⟨ha,hb⟩:=lt_min_iff.mp s'
 rw [p w' w' ha.le hb.le]
 have z : Tendsto (fun i=>S.sand (T s s) (f i-s) (g i-s)) l (𝓝 (S.sand (T s s) (a-s) (b-s))):=
    (((S.wax_cont (sub_pos.mpr ha)).tendsto.comp (u.sub_const s)).mul tendsto_const_nhds).mul
     ((S.wax_cont (sub_pos.mpr hb)).tendsto.comp (v.sub_const s))
 refine z.congr' ?_; filter_upwards [u.eventually (le_mem_nhds ha),v.eventually (le_mem_nhds hb)] with i a' b'; exact (p w' w' a' b').symm
lemma Credits.slide {I:Type*}{l:Filter I}{f g:I→ℝ}(p:S.Credits w T)
 (h:w<a)(t:w<b)(u:Tendsto f l (𝓝 a))(v:Tendsto g l (𝓝 b)):
 BSOT (fun i=>T (f i) (g i)) l (T a b):=BSOT.fromNorm (p.norm_slide h t u v)
lemma Credits.earned {I:Type*}{l:Filter I}[NeBot l]{u:I→ℝ}{G:I→ℝ→ℝ→H.Op}
  (p:Tendsto u l (𝓝 w))(q:∀ᶠ i in l,S.Credits (u i) (G i))
  (h:∀ a>w,∀ b>w,BSOT (fun i=>G i a b) l (T a b)):
 S.Credits w T:=by
 intro a b c d r s t v; apply (h _ (r.trans_le t) _ (s.trans_le v)).unique
 apply (S.sand_limit (h a r b s) tendsto_const_nhds tendsto_const_nhds).congr'
 filter_upwards [p.eventually (gt_mem_nhds r),p.eventually (gt_mem_nhds s),q] with i k m e; exact (e k m t v).symm
/- BSOT convergence + compatibility implies even BSOT convergence on moving centers -/
lemma Credits.slide_in {I:Type*}{l:Filter I}[NeBot l]{u:I→ℝ}{G:I→ℝ→ℝ→H.Op}
  (p:Tendsto u l (𝓝 w))(q:∀ᶠ i in l,S.Credits (u i) (G i))
  (h:∀ a>w,∀ b>w,BSOT (fun i=>G i a b) l (T a b))
  {f g:I→ℝ}(ha:w<a)(hb:w<b)(v:Tendsto f l (𝓝 a))(z:Tendsto g l (𝓝 b)):
 BSOT (fun i=>G i (f i) (g i)) l (T a b):=by
 obtain ⟨s,w',s'⟩:=exists_between (lt_min ha hb); obtain ⟨ha,hb⟩:=lt_min_iff.mp s'
 rw [Credits.earned p q h w' w' ha.le hb.le]
 apply (S.sand_limit (h s w' s w') (v.sub_const s) (z.sub_const s)).congr'
 filter_upwards [p.eventually (gt_mem_nhds w'),v.eventually (le_mem_nhds ha),z.eventually (le_mem_nhds hb),q] with i k n m e; exact (e k k n m).symm
end YM.OS.Semigroup
