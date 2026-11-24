import YM.SU5.Reconstruction.Crease.Profit
import YM.SU5.Reconstruction.Crease.Fountain
import Mathlib.Analysis.LocallyConvex.Separation
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H:Hilbert}{M:Net H}(Ω:H)(a:ℂ)(k:a.re=1/2)
def Taut (M:Net H)(x:H.Op):Prop:= x∈ M∧IsSelfAdjoint x
lemma m_smul (c:ℂ){x:H.Op}(p:x∈ M): c • x∈M:= M.toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem _ p
lemma Taut.merge {x y:H.Op}(p:Taut M x)(q:Taut M y): Taut M (x+y):= ⟨add_mem p.1 q.1,p.2.add q.2⟩
lemma Taut.wide (c:ℝ){x:H.Op}(p:Taut M x): Taut M ((c:ℂ) • x):= ⟨m_smul _ p.1,(by unfold IsSelfAdjoint; rw [star_smul, Complex.star_def,Complex.conj_ofReal,p.2.star_eq])⟩
def ear (b c:H.Op) :ℝ:= ((star a)*inner ℂ (b Ω) (c Ω)).re
lemma ear_add(b c d:H.Op) : ear Ω a b (c + d)= ear Ω a b c+ear Ω a b d:=by simp only [ear,add_apply,inner_add_right,mul_add,Complex.add_re]
lemma ear_r (c:ℝ)(b d:H.Op) : ear Ω a b ((c:ℂ) • d)=c * ear Ω a b d:= by simp only [ear,smul_apply,inner_smul_right,mul_left_comm (star a),Complex.re_ofReal_mul]
lemma ear_l(b c d:H.Op) : ear Ω a (c + d) b= ear Ω a c b+ear Ω a d b:=by simp only [ear,add_apply,inner_add_left, mul_add,Complex.add_re]
lemma ear_p (c:ℝ)(b d:H.Op) : ear Ω a ((c:ℂ) • d) b=c * ear Ω a d b:= by simp only [ear,smul_apply,inner_smul_left,Complex.conj_ofReal,mul_left_comm (star a),Complex.re_ofReal_mul]
lemma Taut.norm (a b:ℝ)(x y:H.Op)(u:‖x‖ ≤1)(v:‖y‖ ≤1)(p:0≤a)(q:0≤b) : ‖(a:ℂ) • x+(b:ℂ) • y‖ ≤ a+b := by
 apply le_trans (norm_add_le ..); rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg p,Real.norm_of_nonneg q]; gcongr<;> nlinarith
variable {N : H.Op}(q:N∈M.commutant)(m:‖N‖≤1)
-- finite-ladder first estimate each rCash.Strict.Eq one true read per stage.
include k q m
lemma allot {ι:Type*} [Fintype ι](A:ι→H.Op)(p:∀ i,Taut M (A i))(ε:ℝ)(h:0<ε) : ∃ y:H.Op, Taut M y ∧ ‖y‖≤1 ∧ ∀ i, dist (ear Ω (1:ℂ) (A i) N) (2*ear Ω a (A i) y)<ε:= by
 let S (x:H.Op):ι→ℝ:= fun i=> 2*ear Ω a (A i) x; let X:ι→ℝ:= fun i=>ear Ω 1 (A i) N
 let Q:= S '' {x | Taut M x ∧ ‖x‖≤1}; have e: X ∈ closure Q:= by
    have ht:Convex ℝ Q:=by
       intro t g u h l r s w z; -- intro signature
       obtain ⟨x,⟨p,a0⟩,rfl⟩:=g; obtain ⟨y,⟨q,b'⟩,rfl⟩:=h
       refine ⟨(l:ℂ) • x+(r:ℂ) •y,⟨(p.wide _).merge (q.wide _), (Taut.norm l r x y a0 b' s w).trans_eq z⟩,?_⟩; ext i; change 2*ear Ω a _ _=l *S x i+r*S y i; rw [ear_add,ear_r,ear_r]; unfold S; ring
    by_contra v
    obtain ⟨F,u,hU,hX⟩:= geometric_hahn_banach_closed_point ht.closure isClosed_closure v
    let D(i:ι):= F (Pi.single i (1:ℝ)); have eF(X:ι→ℝ):F X=∑ i:ι,D i* X i:=by
       nth_rw 1 [← Finset.univ_sum_single X]; rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [show Pi.single i (X i)=X i • Pi.single i (1:ℝ) from ?_,map_smul]; exact mul_comm ..; ext x; by_cases h:x=i <;> simp [h]
    let G:=∑ i:ι,(D i:ℂ) • A i
    have heα(T:Finset ι) : Taut M (∑ i∈T,(D i:ℂ) • A i):= by induction T using Finset.induction_on with
     | empty => rw [Finset.sum_empty]; exact ⟨zero_mem M,IsSelfAdjoint.zero _⟩
     | insert i s h ih => rw [Finset.sum_insert h]; exact ((p i).wide _).merge ih
    have hp(x:H.Op)(b:ℂ) : ear Ω b G x=∑ i:ι,D i*ear Ω b (A i) x:=by
       suffices ∀s:Finset ι, ear Ω b (∑ i∈s,(D i:ℂ) • A i) x=∑ i∈s,D i*ear Ω b (A i) x from this _
       intro s; induction s using Finset.induction_on with
       | empty=> simp [ear]
       | insert i s h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,ear_l,ear_p,ih]
    have he : F X= (inner ℂ (G Ω) (N Ω)).re:= by calc
        _ = ear Ω 1 G N:= by rw [hp,eF]
        _ = _:= by simp [ear]
    have hu(y:H.Op):F (S y)=2*ear Ω a G y:= by rw [eF,hp,Finset.mul_sum]; congr 1; exact funext fun i=> mul_left_comm (D i) 2 _
    set δ :=(F X-u) / (1+‖Ω‖^2); have z':0<δ:=by unfold δ; apply div_pos (sub_pos.mpr hX) (by positivity)
    have t:δ * (1+‖Ω‖^2)=F X -u:= div_mul_cancel₀ _ (by positivity)
    obtain ⟨y,v,h2,p2,b⟩:= priceAny ((heα Finset.univ).1) q m a k Ω ((heα Finset.univ).2) δ z'; have hx:= hU (S y) (subset_closure (show S y∈ Q from ⟨y,⟨⟨v,h2⟩,p2⟩,rfl⟩)); rw [←he, show 2*( (star a)*inner ℂ (G Ω) (y Ω)).re = F (S y) from (hu y).symm] at b; linarith
 obtain ⟨y,⟨x,⟨p1,p2⟩,rfl⟩,t⟩:= Metric.mem_closure_iff.mp e _ h; exact ⟨x,p1,p2,fun i=> lt_of_le_of_lt (dist_le_pi_dist X (S x) i) t⟩
end YM.BridgeClub
