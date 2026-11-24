import YM.SU5.Reconstruction.Quartz.Brill
/-! # At cap. Needs the OTHER FRAME's purchases here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval
open CrossedFrame Clasp Picket Lens Ravin BridgeClub Anvil ConePrice Sail
variable {a b:Axis}(p:b≠a) {H E K:Hilbert}(S:OS.Semigroup H a)(C:Clasp K H E)(B W:H.Op)(R u s:ℝ)
local notation "θ"=> path a b
local notation "V"=> boost C
local notation "ξ"=> (rateTime (b:=b) S B)
lemma curtainJoin(t:ℝ): rateTime (b:=b) S B (u+t,t)=LorTime S t (rateTime (b:=b) S B (u,0)):=by
 unfold rateTime; rw[shift_clock,parcel_add]; unfold parcelUp LorTime; rw [←neg_smul,trans_time,trans_time]; rfl
lemma norm_toll(x y:H)(A:H.Op){t:ℝ}(e:‖A‖ ≤ t): ‖inner ℂ x (A y)‖≤‖x‖*(t*‖y‖):= le_trans (norm_inner_le_norm ..) (mul_le_mul_of_nonneg_left ((A.le_opNorm y).trans (mul_le_mul_of_nonneg_right e (norm_nonneg _))) (norm_nonneg _))
lemma normalized(t:ℝ)(x:H):‖boost C t x‖=‖x‖:= by rw [@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,(boost_pays ..).ordinary]
lemma budgeted(t:ℝ) : ‖ascend t C B‖≤ ‖B‖:= by apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro x; unfold ascend; simp only [boostStar,mul_apply_eq_comp, normalized]; simpa only [normalized] using B.le_opNorm (boost C (-t) x)
@[simp] lemma unAsk(t:ℝ): boost C t*boost C (-t)=1:=by rw [boost_thru,add_neg_cancel,boost_first]
@[simp] lemma reframe(t:ℝ): ascend t C (ascend (-t) C B)=B:=by unfold ascend; rw [boostStar,boostStar,neg_neg]; rw [show V _ *(V (-t)*B*V t)*V (-t)=V t*V (-t)*B*(V t*V (-t)) from by simp only [mul_assoc] ]; simp
lemma scaleClan(t:ℝ)(A:H.Op) : ascend t C (B*A)=ascend t C B*ascend t C A:= by rw [pondLevel,pondLevel,pondLevel]; exact Club.pulsed ..
lemma allotFace(t:ℝ)(x y:H): inner ℂ x (ascend (-t) C B y)= inner ℂ (boost C t x) (B (boost C t y)):= by
 unfold ascend; rw [mul_apply_eq_comp,mul_apply_eq_comp, ← (boost_pays C t).ordinary x]; change inner ℂ (V t x) ((V t*V (-t)) (B _))=_; rw [unAsk,boostStar,neg_neg]; rfl
-- actual fiscal charge. horizon is CPB illumination signed (here b other clock positive space). Bath uses all t,x in REAL.
def Worth (M:Set H.Op):Prop:=∀ s:ℝ,|s|≤3→∀ t:ℝ,|t|≤R → ∀ A∈M,∀ x:ℝ, |x|≤R → Commute A (rateTime (b:=b) S (ascend s C B) (t+x,x)) -- note s shadowed? used macro no
variable {M:Set H.Op} (R0:0≤R) (v: Worth (b:=b) S C B R M)(d c:ℝ≥0)(k: Script S M W d c)
local notation "B₁"=> (ascend s C B)
local notation "W₁"=> (ascend (-s) C W)
local notation "φ"=> rateTime (b:=b) S B₁
local notation "I"=> Complex.I
local notation "δ"=> ((d:ℝ):ℂ)
variable (x y:H)
variable (L:∀ v:E4, boost C (-s) * trans S v= trans S (Picket.move a b (-s) v)* boost C (-s))
include p L
lemma depots(t:Du): (ξ) (Waltz.swap s t) = ascend (-s) C (rateTime (b:=b) S B₁ t):=by
 rw[rateTime,rateTime,motionFrame p (-s) C S L,homeward p, show ascend (-s) C B₁=B from by simpa only [neg_neg] using reframe C B (-s)]
include k v R0
lemma concordance (t:ℝ)(e:|s|≤3)(h:|t|≤R) : Tunneler R (d:ℝ) (‖x‖*((c:ℝ)*‖B‖*‖y‖)) (fun u=> inner ℂ x ((W₁*(ξ) (hike s (t,u))) y)) (fun u=> inner ℂ x (((ξ) (hike s (t,u))*W₁) y)):=by
 let Y:= (φ) (t,0); let X:= boost C s x; let y':=boost C s y; let a(u:ℝ):=(φ) (t+u,u); have hh(u:ℝ):a u=LorTime S u Y:= curtainJoin ..
 obtain ⟨F,U⟩:= k.port (S:=S) (L:=Y) (r:=R) (fun A m u b'=>by rw [←hh]; exact v s e t h A m u b') -- port args
 let g(z:ℂ):= δ-I*z; have hg:Differentiable ℂ g:=by unfold g;fun_prop
 let Vₘ(z:ℂ):= F (g z); have hm (z:ℂ):(g z).re=(d:ℝ)+z.im ∧ (g z).im= -z.re:=by constructor<;>simp[g]
 have goes (t:ℂ)(p:t∈ Board R d):(g t)∈ bore R (d:ℝ):= by
    obtain ⟨h,h'⟩:=p; simp only [bore,mem_setOf_eq, (hm _).1,(hm _).2]; refine ⟨?_,(by rw[abs_neg]; exact abs_le.mpr h)⟩; constructor<;> linarith [show -(d:ℝ)≤t.im from h'.1,show t.im≤0 from h'.2]
 refine ⟨fun z:ℂ=> inner ℂ X (Vₘ z y'),?_,?_,(U.guard X y').comp hg.continuous.continuousOn (fun _ p=>goes _ p),?_⟩
 · intro v₁ p'; simp_rw [hike,depots p S C B s L,← scaleClan,allotFace]; let u:= (v₁:ℂ); constructor
   · change inner ℂ X (F (g u) y')=inner ℂ X ((W * a v₁) y'); rw [U.right (g u) (by simp [g,u]) (by rw [(hm _).2,abs_neg];exact abs_le.mpr p'),(hm u).2,neg_neg]; exact congrArg (fun U:H.Op=> inner ℂ X ((W* U) y')) (hh v₁).symm
   change inner ℂ X (F _ y')=inner ℂ X ((a v₁* W) y'); rw[U.left _ (by simp only [(hm _).1,Complex.sub_im,Complex.mul_I_im,Complex.ofReal_im, Complex.ofReal_re]; ring) (by rw[(hm _).2,abs_neg]; simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_I_re,Complex.ofReal_im,neg_zero, sub_zero] using abs_le.mpr p'), (hm _).2,neg_neg,hh]; congr 3; simp
 · intro t p; refine (norm_toll X y' _ (U.toll _ (goes t p))).trans ?_; unfold X y'; rw [normalized,normalized]; gcongr; exact (parcel_charge S _ _).trans (budgeted ..)
 apply (U.analytic X y').differentiableOn.comp hg.differentiableOn; rintro z a
 rcases a with ⟨d1,⟨h1,h2⟩⟩; show 0< (g z).re∧ (g z).re<(d:ℝ)∧ |(g z).im| <R; rw[(hm _).1,(hm _).2,abs_neg,abs_lt]; refine ⟨?_,?_,d1⟩<;> linarith
end YM.Quartz.Waltz
