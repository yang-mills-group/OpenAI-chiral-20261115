import YM.CF.Fir.Gliss
/-! Analytic kernel stocks in position basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

def tub {n:Type*} (f:Momentum→Op n) (x:Cover):Op n:=Matrix.of fun a b=> market (placed (fun p=> f p a b)) 0 x
lemma tub_bill {ι n:Type*} [Fintype n] {w:ι→ℝ}{f:ι→Momentum→Op n}(h: Pay w f) (he:∀ i (p:Momentum), p∈realCube zone→∀ x,p+reciprocal x∈realCube zone→ f i (p+reciprocal x)=f i p) :
 (∃ σ C : ℝ,0<σ ∧ 0<C ∧ ∀ i a b, Width σ (C*w i) (fun x=> tub (f i) x a b)) ∧ (∀ i p, p∈baseCube→∀ a b, read (fun x=> tub (f i) x a b) p=f i p a b):=by
  obtain ⟨θ,C,hp,hC,H⟩:= h.stapleMat; let d:=min θ zone; let b:=d/3; have ht:=lt_min hp zone_pos; have hb: 0<b:=by unfold b; positivity
  let B:=(2*((1+b)/b))^(Fintype.card Axis)
  have hx (i a y) := hol_on_thickening ht ((H (i,a,y)).mono (min_le_left ..) le_rfl) ((show Overlaps zone _ from (fun p hp x hh=> congr_fun (congr_fun (he i p hp x hh) a) y)).mono (min_le_right ..))
  constructor
  · refine ⟨b,C*B,hb,mul_pos hC (by unfold B; positivity),fun i a y=>?_⟩; rw [mul_right_comm]; exact (hx i a y).1.issues (hx i a y).2.1 b b hb.le hb (by unfold b; linarith)
  intro i p hs a y
  have hu:= mem_cube_real (base_subset_realCube ht hs) ht; exact ((hx i a y).1.paints (hx i a y).2.1 p hu.1).trans ((hx i a y).2.2 _ hu)
variable (u:Bool)(j:ℕ)(L M:Side)(hj:Even j)(ho:Odd L.val)(hm:Odd M.val){p:Momentum}
def boards (p:Momentum):Stk L:=trident L p*clockK u j L M p
def brix (p:Momentum): Stk L:=trident L p*stackW j L p
lemma brix_scale (hp:physical p): brix j L p=trident L p*sprig j L p+(1-peb L):=by
  rw [brix,stackW,mul_add, ← mul_assoc,returned,show star p=p from hp,show trident L p* Matrix.conjTranspose (trident L p)=1 from (pointed _ _ hp).2,one_mul]
lemma alias_pin (g:Momentum)(x:Cover) (l:Site L)(r:Site L): mode (aliasAt (g+reciprocal x) l) (lift r)=mode (aliasAt g (l+wrap L x)) (lift r):=by
  obtain ⟨y,hy⟩:=alias_exchange g l x; rw [hy,mode_phase,mode_periodic,mul_one]
lemma verifies (hp:p∈realCube zone)(x:Cover)(hx:p+reciprocal x∈realCube zone): brix j L (p+reciprocal x)=brix j L p:=by
  rw [brix_scale j L hx.1,brix_scale j L hp.1]; congr 1
  ext ⟨i,a⟩ ⟨r,b⟩
  simp only [Matrix.mul_apply,St,Fintype.sum_prod_type]; conv_rhs=>rw [← Equiv.sum_comp (Equiv.addRight (wrap L x))]
  apply sum_congr rfl; intro l _; apply sum_congr rfl; intro y _; obtain ⟨e,he⟩:=alias_exchange p l x
  simp only [trident, Matrix.smul_apply,aliasBlock,Matrix.of_apply, sprig,c_app,smul_eq_mul,money,he,mode_phase,mode_periodic,mul_one,muff_period]; rfl
include ho in
lemma torso (hp:p∈realCube zone)(x:Cover)(hx:p+reciprocal x∈realCube zone):
    trident L (p+reciprocal x)*born u j L M (p+reciprocal x)*star (trident L (p+reciprocal x))= trident L p*born u j L M p*star (trident L p):=by
  ext ⟨i,a⟩ ⟨r,b⟩
  have he (p: Momentum)(i r:Site L)(a b:SpinIdx): (trident L p*born u j L M p) (i,a) (r,b) = ∑ k : SpinIdx, trident L p (i,a) (r,k) * bent u j M (aliasAt p r) k b:=by
    simp only [Matrix.mul_apply, born,s_app,St,Fintype.sum_prod_type,mul_ite,mul_zero]
    rw [Finset.sum_eq_single r]; simp; intro y _ hy; simp [hy]; simp
  rw [Matrix.mul_apply]; conv_rhs => rw [Matrix.mul_apply]
  simp only [St,Fintype.sum_prod_type,he]; conv_rhs=>rw [← Equiv.sum_comp (Equiv.addRight (wrap L x))]
  apply sum_congr rfl; intro l _; apply sum_congr rfl; intro y _
  have hh := alias_pin L p x l
  obtain ⟨e,hE⟩:=alias_exchange p l x
  simp only [Matrix.star_apply,trident,Matrix.smul_apply,aliasBlock,Matrix.of_apply,hh]
  rw [hE]
  have ht : bent u j M (aliasAt p (l+wrap L x)+ reciprocal e)=bent u j M (aliasAt p (l+wrap L x)) := by
    unfold bent; rw [bar_overlap _ _ (alias_in_real zone_pos hp _ ho) _ (hE ▸ alias_in_real zone_pos hx l ho)]
  rw [ht]; rfl
include ho hj hm in
lemma board_verify (hp:p∈realCube zone)(x:Cover)(hx:p+reciprocal x∈realCube zone): boards u j L M (p+reciprocal x)= boards u j L M p:=by
  by_cases h:x=0
  · simp [h, show reciprocal (0:Cover)=0 from (funext fun i=> by simp [reciprocal])]
  obtain ⟨he,hg⟩:= overlap_regular h hp hx
  let c:=p+reciprocal x; let K q:= wood u j L q; let Z q:=trident L q; let T q:=stackW j L q
  let P q:=born u j L M q; let Y q:=splitY u j L M q; let C q:=clockK u j L M q; let U q:=vine u j L M q
  have hV: U c=U p:=by unfold U vine grow bent c; rw [bar_overlap _ _ hp x hx]
  let B:=brix j L p; let Q:=Z p*P p*star (Z p)
  have hh: Z c*P c*star (Z c)=Q:=torso u j L M ho hp x hx
  have hZ := pointed L _ hp.1; have hX:= pointed L _ hx.1
  have hY(q:Momentum)(hq:q∈realCube zone)(hy:brix j L q=B): K q*star (Z q)=B⁻¹*sA u L+star B*(1-sA u L):=by
    unfold K wood returned; rw [← hy,brix,show star q=q from hq.1]
    have hq': sA u L*star (Z q)=star (Z q)*sA u L:=by
      have h:=congr_arg star (slateT u L q); rwa [star_mul,star_mul,slateS] at h
    have ht: (trident L q)⁻¹=star (Z q):= (Matrix.inv_eq_right_inv (pointed L q hq.1).2)
    rw [Matrix.mul_inv_rev,ht,star_mul,add_mul]
    rw [mul_assoc,hq', ← mul_assoc]; congr 1
    change star (T q)*(1-sA u L)*star (Z q)=_
    simp only [mul_assoc,sub_mul,one_mul,mul_sub,mul_one,hq']; rfl
  let W:= U p * (B⁻¹*sA u L+star B*(1-sA u L))*Q
  have ha (q : Momentum)(hq:q∈realCube zone)(ho':q≠0)(hy:brix j L q=B)(hP:Z q*P q*star (Z q)=Q)(hv : U q=U p): Z q*C q*W=Q ∧ W*(Z q*C q)=U p ∧ Z q*C q*U p=Z q*C q ∧ Q*(Z q*C q)= Z q*C q:=by
    have Hz:star (Z q)*Z q=1:= (pointed _ _ hq.1).1
    have hk:K q*star (Z q)= _:= hY q hq hy
    have hw : W= Y q * star (Z q):=by
      unfold W
      rw [← hk,← hv,← hP]; simp only [← mul_assoc]; rw [mul_assoc _ (star (Z q)),Hz,mul_one]; rfl
    have h₁ : C q*Y q=P q:= roundabout u j L M hj ho hm hq ho'
    obtain ⟨h₂,h₃,h₄⟩:= chase u j L M hj ho hm hq ho'
    change Y q * C q=U q at h₂; change C q * U q=C q at h₃; change P q * C q=C q at h₄
    rw [hw]
    constructor
    · rw [← mul_assoc,mul_assoc (Z q),h₁,hP]
    refine ⟨?_,?_,?_⟩
    · rw [← mul_assoc,mul_assoc _ _ (Z q),Hz,mul_one,h₂,hv]
    · rw [← hv,mul_assoc,h₃]
    rw [← hP,←mul_assoc,mul_assoc _ _ (Z q), Hz,mul_one,mul_assoc,h₄]
  obtain ⟨h1,h2,h3,h4⟩:= ha c hx hg (verifies j L hp x hx) hh hV
  obtain ⟨g1,g2,g3,g4⟩:= ha p hp he rfl rfl rfl
  change Z c*C c=Z p*C p
  calc
    _ = Z c*C c*(W*(Z p*C p)):=by rw [g2,h3]
    _ = _:=by rw [←mul_assoc,h1,g4]
end YM.CF.Fir
