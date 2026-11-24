import YM.SU5.Silk.Clock.Gyre
import YM.CF.Mica.Sleet
import YM.CF.Moto.Pin
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Ione.Clock
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open AnalyticBridge.VerifiedReset StressFlux Moto
abbrev move:=PlaqAxes.transform

/-- Include orientation in moving a price on an index sorted smaller-axis first. -/
def levy(s:Signed)(i:PlaqAxes):ℝ:= (sign s i.val.1*sign s i.val.2)*(if s.perm i.val.1<s.perm i.val.2 then 1 else -1)
lemma «levy_±»(s:Signed)(i:PlaqAxes):levy s i=1∨levy s i= -1:=by unfold levy sign; split <;> split<;>split<;>simp
lemma levy_self(s:Signed)(i:PlaqAxes):levy s i*levy s i=1:=by rcases «levy_±» s i with h|h<;>simp [h]
lemma frame_levy(s:Signed){G: Gauge}(u:Flux G)(i:PlaqAxes): reframe u s i= levy s i • u (PlaqAxes.transform s i):=by
 unfold reframe levy
 rcases lt_or_gt_of_ne (s.perm.injective.ne i.property.ne) with h|h
 · simp [orderedDir,h,h.le,not_lt_of_gt h,PlaqAxes.transform,PlaqAxes.rotate,PlaqAxes.ordered]
 simp [orderedDir,h,h.le,not_lt_of_gt h,PlaqAxes.transform,PlaqAxes.rotate,PlaqAxes.ordered]
lemma levies(p q:Signed)(i:PlaqAxes): PlaqAxes.transform p (PlaqAxes.transform q i)=PlaqAxes.transform (p*q) i ∧ levy p (PlaqAxes.transform q i)*levy q i=levy (p*q) i:=by
 have hx(t):sign (p*q) t=sign p (q.perm t)*sign q t:= Pec.dyeM p q t
 obtain ⟨⟨u,v⟩,h'⟩:=i; change u<v at h'; let i:PlaqAxes:= ⟨(u,v),h'⟩
 rcases lt_or_gt_of_ne (q.perm.injective.ne h'.ne) with h|h
 · have hp: move q i=⟨(q.perm u,q.perm v),h⟩:=Subtype.ext (Prod.ext (min_eq_left h.le) (max_eq_right h.le))
   change move p (move q i)= move (p*q) i ∧ levy p (move q i)*levy q i=levy (p*q) i; rw [hp]; refine ⟨Subtype.ext rfl,?_⟩; unfold levy; unfold i; simp only [Signed.mul_perm_apply, hx,h,if_true]; ring
 have hp: move q i=⟨(q.perm v,q.perm u),h⟩:=Subtype.ext (Prod.ext (min_eq_right h.le) (max_eq_left h.le))
 change move p (move q i)= move (p*q) i ∧ levy p (move q i)*levy q i=levy (p*q) i; rw [hp]; refine ⟨Subtype.ext (Prod.ext (min_comm ..) (max_comm ..)),?_⟩; unfold levy; unfold i; simp only [Signed.mul_perm_apply, hx,if_neg (not_lt_of_gt h)]; rcases lt_or_gt_of_ne (p.perm.injective.ne h.ne) with t|t<;> simp only [t,not_lt_of_gt t,if_false,if_true]<;> ring

/-- shape transfer from moved arguments back to original. -/
def localFace(s:Signed)(f:Skate):Skate:=fun i j=> let a:=(move s).symm i; let b:=(move s).symm j; (levy s a*levy s b) • (Pec.pays s (f a b))
lemma face_p(s:Signed)(f:Skate)(i j:PlaqAxes) : localFace s f (move s i) (move s j)=(levy s i*levy s j) • (Pec.pays s (f i j)):=by simp [localFace]
lemma locale_price(s:Signed)(f:Skate):‖localFace s f‖≤‖f‖:=by
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr; rintro i
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr; intro j; obtain ⟨i,rfl⟩:=(move s).surjective i; obtain ⟨j,rfl⟩:=(move s).surjective j; rw [face_p]; refine le_trans ?_ ((norm_le_pi_norm ..).trans (norm_le_pi_norm f i) : ‖f i j‖≤‖f‖); rcases «levy_±» s i with a|a<;>rcases «levy_±» s j with b|b<;> simp [a,b,Pec.pays]<;>split<;>simp
lemma locale_smul(s:Signed)(f:Skate)(r:ℝ) : localFace s (r • f) = r • localFace s f :=by ext i j; unfold localFace; simp_rw [Pi.smul_apply,map_smul]; rw [smul_comm]
lemma locale_sub(s:Signed)(f g:Skate):localFace s (f-g)=localFace s f-localFace s g:=by ext i j; simp only [localFace,Pi.sub_apply,map_sub,smul_sub] -- ext tune
lemma locale_zero(s:Signed):localFace s 0=0:=by funext i j; simp [localFace]
lemma local_m(s t:Signed)(f:Skate): localFace s (localFace t f)=localFace (s*t) f:=by
 funext i j; obtain ⟨i,rfl⟩:=(move (s*t)).surjective i; obtain ⟨j,rfl⟩:=(move (s*t)).surjective j; rw [face_p, ← (levies s t i).1, ← (levies s t j).1]; rw [face_p,face_p,map_smul,Pec.pays_t,smul_smul]; congr 1; rw [← (levies s t i).2,← (levies s t j).2]; ring
@[simp] lemma move_one(i:PlaqAxes):move 1 i=i:=Subtype.ext (Prod.ext (min_eq_left i.property.le) (max_eq_right i.property.le))
lemma levy_one(i:PlaqAxes): levy 1 i=1:=by unfold levy; rw [if_pos (show (1:Signed).perm _ < (1:Signed).perm _ from i.property)]; simp [sign]
lemma local_one(f:Skate):localFace 1 f=f:=by funext i j; simpa [det_i, levy_one,Pec.pays] using face_p 1 f i j

def Taxing(s:Signed)(f:Skate):Prop:= localFace s f= Price s • f
lemma tint(s t:Signed)(f:Skate)(p:Taxing s f)(h:Taxing t f):Taxing (s*t) f:=by
 unfold Taxing at *; rw [price_m,← local_m,h,locale_smul,p,smul_comm,mul_smul]
lemma tint_scale(s:Signed)(f:Skate)(r:ℝ)(p:Taxing s f) : Taxing s (r • f):=by unfold Taxing; rw [locale_smul, show localFace s f= _ from p,smul_comm]
lemma tax_at(s:Signed)(f:Skate):Taxing s f ↔ ∀ i j,f (move s i) (move s j)=(Price s*levy s i*levy s j) • (Pec.pays s (f i j)):=by
 constructor
 · intro h i j; have hp:=face_p s f i j; rw [show localFace s f= _ from h,Pi.smul_apply,Pi.smul_apply] at hp; rw [mul_assoc, mul_smul,←hp,smul_smul,price_o,one_smul]; -- tune
 intro g; funext i j; obtain ⟨i,rfl⟩:=(move s).surjective i; obtain ⟨j,rfl⟩:=(move s).surjective j; simp only [face_p,Pi.smul_apply]; rw [g,smul_smul,←mul_assoc,←mul_assoc,price_o,one_mul]
end YM.CF.Ione.Clock
