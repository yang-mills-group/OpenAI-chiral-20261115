import YM.CF.Nacre.Pall
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{m:ℕ}
abbrev Cloud(n:Side):=fieldDir group (More n) 1
abbrev MarkT(g:E)(V:Cloud n):Cloud n:= fun x=> group.adjoint g (V x)
def folk(g:E)(n:Side):=tradew n fun _=>g
def RaysX (A: Cloud n → Op (Single n)):Prop:= (∀ g x,A (MarkT g x)=twist (folk g n) (A x)) ∧ ∀ t x,A (SubMotion t x)=ZoneH (lagX t) (A x)
lemma thump(g:E)(x:Cloud n)(y)(r:PrizeX n): heat y (collect group (MarkT g x)) r= group.adjoint g (heat y (collect group x) r):=by
 have hx(w:Walk)(z:Site (More n)): linkSum (collect group (MarkT g x)) z w= group.adjoint g (linkSum (collect group x) z w):=by
    induction w generalizing z with
    | nil=> simp [linkSum]
    | cons i w h=>rw [linkSum,linkSum,h,map_add]; congr 1; split; rw [map_neg]; rfl; rfl
 cases r <;> exact hx ..
def ni(x y:HopK n)(A:Op (Single n)):Op Slot:= Matrix.of fun i j=> A (x,i) (y,j)
lemma twistW(x y:HopK n)(A:Op (Single n))(g:Site (More n)→E):ni x y (twist (tradew n g) A)= (matter (g (terse x))).val * ni x y A *star (matter (g (terse y))).val:=by
 unfold tradew; rw [twist_formula]; let P (x:HopK n):=(matter (g (terse x))).val; let f:=Equiv.refl (HopK n); have hh(X:Op (Single n))(g : HopK n → Op Slot): ni x y (jump f g * X)=g x*ni x y X ∧ ni x y (X*jump f g)= ni x y X*g y:=by
    constructor <;> ext i j
    · simp only [ni, Matrix.of_apply,Matrix.mul_apply, Single]; rw [Fintype.sum_prod_type]; simp only [jump_apply,f, Equiv.refl_apply,ite_mul,zero_mul,sum_ite_irrel,sum_const_zero,sum_ite_eq, mem_univ,ite_true]
    simp only [ni,Matrix.of_apply, Matrix.mul_apply,Single]; rw [Fintype.sum_prod_type]; simp only [jump_apply,f,Equiv.refl_apply,mul_ite,mul_zero,sum_ite_irrel,sum_const_zero,sum_ite_eq', mem_univ,ite_true]
 change ni x y (jump f P*A*star (jump f P))=_; rw [jump_star,show f.symm=f from rfl,(hh _ _).2,(hh _ _).1]; rfl
private lemma lure(P: Toy m n)(h:RaysX (pyre P)):pyre (lantern P)= pyre P:=by
 funext x; ext ⟨u,i⟩ ⟨v,j⟩; let V(p:Trip m n):Fin m→CoreX:=fun k=>heat (terse u) (collect group x) (p k); let F(p:Trip m n)(g:E):=halo (lowerP P g) u v p (V p)
 have he(p:Trip m n): (halo (lantern P) u v p (V p) i j)=∫ g:E,F p g i j ∂group.probHaar:=by
    rw [lifeP]; apply integral_congr_ae; apply Eventually.of_forall; intro g; exact (Matrix.ext_iff.mpr (keynote ..) i j).symm -- private keynote?
 have hp(g:E):∑ p:Trip m n, F p g= ni u v (pyre P x):=by
    let L:= twist ((matter g)⁻¹); simp_rw [F,keynote]
    rw [←map_sum]; have hf:∑ p:Trip m n,halo P u v p (fun i=> group.adjoint g (V p i))=ni u v (pyre P (MarkT g x)):=by ext a b; simp only [Matrix.sum_apply,ni,Matrix.of_apply]; unfold pyre; simp only [Matrix.of_apply]; simp_rw [thump]; rfl
    rw [hf, h.1,folk,twistW,show (matter g).val*_ *star _= twist (matter g) (ni u v (pyre P x)) from ?_, ← twin, inv_mul_cancel]; swap; exact (twist_formula ..).symm; simp only [twist_formula]; change 1*_ *star (1:Op Slot)=_; rw [star_one,one_mul,mul_one] -- tune
 change ∑ p:Trip m n, halo (lantern P) u v p (V p) i j=(ni u v (pyre P x)) i j
 simp_rw [he]; rw [← integral_finsetSum]; swap; · exact fun l _=> (Continuous.integrable_of_hasCompactSupport ((ContinuousMultilinearMap.apply ℝ _ _ (V l)).continuous.comp (lacy P (u,i) (v,j) l)) (HasCompactSupport.of_compactSpace _))
 simp_rw [← Matrix.sum_apply,hp]; simp
lemma lit(P: Toy m n)(h:RaysX (pyre P)):∃ Q:Toy m n, handy Q∧Prints Q∧pyre P=pyre Q ∧ ∀ C a:ℝ,(∀ i, balance a P i≤C)→∀ i,balance a Q i≤C*sugarK:=by
 let L:=lantern P; let W:=polish L; have hp:pyre L=pyre P:=lure P h; refine ⟨W,polish_h _ (lantern_f _),sugar _,?_,fun C a H i=> honored a _ (fun i _=> makes P a C H i) _⟩
 funext x; ext ⟨⟨z,i⟩,u⟩ ⟨⟨t,j⟩,v⟩; let y:=(t-z); let T:= natural z
 let s:=SubMotion T x
 have hg:pyre P s= ZoneH (lagX T) (pyre P x):= h.2 T _
 have hv:pyre W s=ZoneH (lagX T) (pyre W x):=dialback W x T (sugar _)
 have hm: pyre W s ((0,i),u) ((y,j),v)=pyre P s ((0,i),u) ((y,j),v):=by rw [←hp]; unfold W pyre; simp_rw [Matrix.of_apply,ripples]
 rw [hg,hv,limo,limo,zero_add,show wrap n T=z from nat_true _, show y+z=t from sub_add_cancel ..] at hm; apply mul_left_cancel₀ _ hm.symm; exact mul_ne_zero (norm_pos_iff.mp (lt_of_lt_of_eq zero_lt_one (fee_norm _).symm)) (norm_pos_iff.mp (lt_of_lt_of_eq zero_lt_one (fee_norm _).symm))
end YM.CF.Nacre
