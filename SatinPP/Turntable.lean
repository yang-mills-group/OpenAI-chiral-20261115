
import SatinPP.Tidal

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
section Scale

variable (a)
def reelT (b:ℝ): E4→ₗ[ℝ] E4 where
 toFun x:=WithLp.toLp 2 (fun i=>(if i=a then b else 1)*x i)
 map_add' x y:= by ext i; simp [mul_add]
 map_smul' c x :=by ext i; simp; ring
lemma reelT_val (b:ℝ)(x:E4)(i:Axis): reelT a b x i = (if i=a then b else 1)*x i:=rfl
lemma reelT_self(b:ℝ)(x:E4):reelT a b x a=b*x a:=by simp [reelT_val]
lemma reelT_cross(b:ℝ)(x:E4): SEP a (reelT a b x)=SEP a x:=by
 apply Subtype.ext
 change reelT a b x-(reelT a b x a) • basis a=x-x a • basis a
 ext i; rw [reelT_self]
 by_cases h:i=a<;>simp [h,reelT_val]
lemma reelT_basis (b:ℝ)(i:Axis):reelT a b (basis i)=(if i=a then b else 1) • basis i:=by
 ext k; rw [reelT_val,PiLp.smul_apply];by_cases d:i=k<;>simp [basis,d]


lemma reelT_det(b:ℝ):LinearMap.det (reelT a b)=b:=by
  let u:Module.Basis Axis ℝ E4:=(EuclideanSpace.basisFun Axis ℝ).toBasis
  let w(i:Axis):=if i=a then b else 1
  rw [←LinearMap.det_toMatrix u,show LinearMap.toMatrix u u (reelT a b) = Matrix.diagonal w from ?_,Matrix.det_diagonal]
  · unfold w; simp
  ext i j; rw [LinearMap.toMatrix_apply]
  have hh: u j=basis j:=by simp [basis,u]
  rw [hh,reelT_basis,←hh,map_smul,u.repr_self]
  by_cases h:i=j
  · simp [h,w]; split <;> simp
  simp [h]; split <;> simp [h]
variable {b:ℝ}(h:0<b)
def earlyT: E4≃L[ℝ]E4 :=
 (LinearEquiv.ofLinear (reelT a b) (reelT a b⁻¹)
    (by ext x i; simp [reelT_val]; split <;> simp [h.ne'])
    (by ext x i; simp [reelT_val]; split <;> simp [h.ne'])
 ).toContinuousLinearEquiv


#check earlyT
def rev (g:Test4):Test4:= (b⁻¹:ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (earlyT a h).symm g

lemma rev_val(g:Test4)(p:E4):
  rev a h g p=(b⁻¹:ℂ)*g (reelT a b⁻¹ p):=rfl
lemma revP(g:Test4)(p:E4):
  rev a h g (reelT a b p)=(b⁻¹:ℂ)*g p:=by
 rw [rev_val, show reelT a b⁻¹ (reelT a b p)=p from (earlyT a h).left_inv p]

include h in
theorem reel_cost {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (F:E4→X):
 (∫ p,F (reelT a b p))= b⁻¹ • (∫ p,F p):=by
  have me:MeasurableEmbedding (reelT a b):=(earlyT a h).toHomeomorph.measurableEmbedding
  rw [←me.integral_map,Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (show LinearMap.det (reelT a b)≠0 by rw [reelT_det];exact h.ne'),reelT_det,
    abs_of_pos (inv_pos.mpr h),integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.mpr h).le]


variable (g:Test4)
-- substitution including normalization
lemma rev_integral {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][NormedSpace ℝ X][IsScalarTower ℝ ℂ X](F:E4→X):
   (∫ p,g p • F (reelT a b p))=(∫ p, rev a h g p • F p):=by
  have h₁:=reel_cost a h (fun p=> rev a h g p • F p)
  simp_rw [revP,mul_smul,← ofReal_inv, show ∀ x:X,(↑b⁻¹:ℂ) • x=b⁻¹ • x from fun x=>IsScalarTower.algebraMap_smul ℂ b⁻¹ x,integral_smul] at h₁
  exact smul_right_injective X (inv_ne_zero h.ne') h₁

lemma rev_total : (∫ p,rev a h g p)=(∫ p,g p):= by
 simpa only [smul_eq_mul,mul_one] using (rev_integral a h g fun _=>(1:ℂ)).symm
-- support equality

lemma rev_place :tsupport (rev a h g)= reelT a b '' tsupport g:=by
 symm
 rw [tsupport,tsupport,show reelT a b '' closure (support ⇑g)= closure (reelT a b '' support ⇑g)
    from (earlyT a h).toHomeomorph.image_closure (support ⇑g)]
 congr 1; ext y; constructor
 · rintro ⟨x,hx,rfl⟩
   change _ ≠ _
   rw [revP]
   exact mul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr h.ne')) hx
 intro hy
 obtain ⟨x,rfl⟩: ∃x,reelT a b x=y := (earlyT a h).surjective y
 rw [mem_support,revP,mul_ne_zero_iff] at hy
 exact mem_image_of_mem _ hy.right


local notation "δ" a => Hierarchy.Seld.shade (basis a)
lemma rev_shade :(δ a) (rev a h g)=(b⁻¹:ℂ) • (rev a h ((δ a) g)):=by
 ext1 x
 apply HasDerivAt.unique (show HasDerivAt (fun u:ℝ=>rev a h g (x+u • basis a)) _ 0 from shadeD _ _ _)
 let v:=reelT a b⁻¹ x
 let f(u:ℝ):= u*b⁻¹
 have e:HasDerivAt f b⁻¹ 0:=by simpa using (hasDerivAt_id' (0:ℝ)).mul_const b⁻¹
 have p:=shadeD (basis a) g v
 unfold HasLineDerivAt at p
 rw [← show f 0=0 from zero_mul _] at p
 have d:= (p.scomp 0 e).const_mul (b⁻¹:ℂ)
 simp_rw [rev_val,map_add,map_smul,reelT_basis] -- last goal


 simpa [smul_smul, Complex.real_smul,rev_val,v, f, comp_def] using d
end Scale

variable (l u:ℝ)(A:H.Op)(g:Test4)(p:E4){b:ℝ}
local notation "V" => S.edge
lemma edge_entry (b:ℝ):
 entry S l u A (sideways b) p=V (-l*b)*optx S A (reelT a b p)*V (u*b):=by
 let v:=reelT a b p
 let t:=b*p a
 have hv :M S v=V t*Q S p:=by change V (v a)*_= _ ;rw[show v a=t from reelT_self a b p]; congr 1; exact congrArg _ (reelT_cross a b p)
 have hh:M S (-v)=Q S (-p)*V (-t):=by
    change V ((-v) a)*Q S (-v)=_
    have c: (-v) a=-t:= by simp [v,t,reelT_self]
    have e:SEP a (-v)=SEP a (-p):=by rw [map_neg, map_neg,reelT_cross]
    rw [c, Q,e]; exact S.both ..


 have tleft:infer (sideways b) (fore a l p)=sideways (-l*b+t):=by unfold infer sideways fore t; push_cast;ring
 have tright:infer (sideways b) (aft a u p)=sideways (-t+u*b):=by unfold infer sideways aft t; push_cast;ring
 unfold entry optx;rw [tleft,tright,tide_edge,tide_edge,hv,hh,
    show V (-l*b+t)=V (-l*b)*V t from (S.send ..).symm,
    show V (-t+u*b)=V (-t)*V (u*b) from (S.send ..).symm]
 simp only [mul_assoc]

lemma coat_edge (h:0<b):coat S l u A g (sideways b)=
   V (-l*b)*valise S A (rev a h g)*V (u*b):=by
 ext1 x
 let y:= V (u*b) x
 change _=V (-l*b) (valise S A (rev a h g) y)
 rw [vmap,← (V (-l*b)).integral_comp_comm (emberI S y A (rev a h g))]
 simp_rw [coat_val,edge_entry,map_smul]
 exact rev_integral a h g (fun p=> V (-l*b) (optx S A p y))

#print axioms coat_edge
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
