import YM.CF.Font.Trail
import YM.Extra.ITERATION_NO_LOSS.Inherited
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n f c: Side}{a C:ℝ}
def Faro(a:ℝ)(x y:Site n):=Real.exp (a * separation x y)
lemma fstop(x:Site n)(z:Cover): separation x (x+wrap n z)≤ size z:=by
 let W:= route 0 z 1; have he:stop x W=x+wrap n z:=by
   have hx(u:Cover)(w:Walk):stop (x+wrap n u) w=x+wrap n (stop u w):=by
    induction w generalizing u with
    | nil=> rfl
    | cons i p H=> rw [stop,add_assoc,←wrap_vec, ← map_add,H]; rfl
   simpa [W,route_end] using hx 0 W -- tune
 rw [←he]; refine (Work.E04.stop_separation_le ..).trans ?_; unfold W; rw [route_length,sub_zero]
lemma tinct {α: Type*}[NormedAddCommGroup α](x:Site n){g:Cover→α}(h:0≤a)(e: Width a C g) : (∑ y:Site n,Faro a x y* ‖∑' z:Cover, if y=x+wrap n z then g z else 0‖)≤ C:=by
 let f(y:Site n)(z:Cover):α:=if y=x+wrap n z then g z else 0
 have he(y:Site n): Summable fun z=>‖f y z‖:=by
   apply Summable.of_nonneg_of_le (f:=fun z=>‖g z‖) (fun _=>norm_nonneg _) _ ((e.unweighted h).2.1)
   intro z; unfold f; split <;> simp
 have ht(y:Site n): Summable fun z=> Faro a x y*‖f y z‖:= (he y).mul_left _
 have hh(y:Site n): ‖∑' z,f y z‖≤ ∑' z,‖f y z‖:= norm_tsum_le_tsum_norm (he y) -- tune
 refine (Finset.sum_le_sum (g:=fun y=>∑' z,Faro a x y*‖f y z‖) ?_).trans ?_
 · intro i _; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hh i) (Real.exp_pos _|>.le)
 have hp:= Summable.tsum_finsetSum (s:=univ) (fun i _=> ht i); rw [←hp]; apply le_trans _ e.2.2
 refine Summable.tsum_le_tsum (fun z=> ?_) (summable_sum (fun i (_:i∈(univ:Finset _))=> ht i)) e.2.1
 rw [sum_eq_single (x+wrap n z)]; rotate_right
 · simp
 · unfold f; rw [if_pos rfl]; unfold Faro; gcongr; exact fstop ..
 intro y _ e; change _*‖f y z‖=0; unfold f; rw [if_neg e,norm_zero,mul_zero]
lemma coat_cross (g: Ratio n f){α β:Type*}[Fintype β]{R:Cross g.count α β}(h:0≤a)(e:R.strip a C)(x:Site f)(i:α): ∑ j:Co n β, Faro a (g.parent x) j.1 * ‖installed g R (x,i) j‖ ≤ Fintype.card β * C:=by
 simp only [Co,installed,split_co,Matrix.submatrix_apply,id_eq]; rw [Fintype.sum_prod_type,Finset.sum_comm]; apply (sum_le_sum (g:=fun _=>C) ?_).trans_eq (by simp)
 intro k _; apply tinct _ h (e _ _)

abbrev Ps(n:Side) := Face (Per n)
variable {S:StepData c f}
def ŧ(n:Side) : Ps n ≃ Body 2 n:=Equiv.prodCongr (Equiv.refl _) plaqEquiv
def lambda (P Q:Bed)(T:Towers S.patch.L)(x: Ps f)(y:Ps c) := installed S.ratio (psi P Q T none) (ŧ _ x) (ŧ _ y)
structure Rails (g:Ratio c f)(A a:ℝ)(Λ:Ps f→ Ps c→ℝ):Prop where
 rate(x:Ps f): ∑ y: Ps c, Faro a (g.parent x.1) y.1*‖Λ x y‖≤ A/(g.count.val:ℝ)^2
 gap(x:Ps f)(i:Axis): ∑ y: Ps c, Faro a (g.parent x.1) y.1*‖Λ (x.1+step i,x.2) y-Λ x y‖≤ A/(g.count.val:ℝ)^3
variable (S)
def eta(A B:ℝ):=Fintype.card (TypeFace 2)*(psiPrice A B)
lemma produce1 (P Q: Bed) (T:Towers S.patch.L){A B a:ℝ}(h:0<a)(he:P.dual_diag.strip a A)(hf:Q.diagonal.strip a B)(v: T.Deep a A 1): Rails S.ratio (eta A B) a (lambda (S:=S) P Q T):=by
 let g:=S.ratio
 have hp(z):= psi_strip h he hf (show 1≤1 from le_rfl) v z
 constructor
 · intro x; have ht:= coat_cross g h.le (hp none) x.1 (plaqEquiv x.2); rw [←Equiv.sum_comp (ŧ c)] at ht; exact ht.trans_eq (by unfold eta; rw [mul_div_assoc]; rfl)
 intro x i; have ht:= coat_cross g h.le (hp (some i)) x.1 (plaqEquiv x.2); rw [←Equiv.sum_comp (ŧ c)] at ht; refine le_trans (le_of_eq (sum_congr rfl ?_)) (ht.trans_eq (by unfold eta; rw [mul_div_assoc]; rfl)); intro y _; congr 2 -- tune
 let u:Body 2 c →ℝ:= Pi.single (ŧ c y) (1:ℝ); have hx:= psi_read h he hf (show 1 ≤1 from le_rfl) v S.sizes S.patch.odd_side (some i) u x.1 (plaqEquiv x.2)
 have hz (b: Body 2 f)(z): (Matrix.mulVec (installed S.ratio (psi P Q T z)) u) b=installed S.ratio (psi P Q T z) b (ŧ c y):=by simp [u]
 change (Matrix.mulVec (installed S.ratio (psi P Q T (some i))) u) (x.1,_)= Matrix.mulVec (installed S.ratio (psi P Q T none)) u (x.1+step i,_)-Matrix.mulVec (installed S.ratio (psi P Q T none)) u (x.1,_) at hx; rw [hz _ (some i),hz _ none, hz _ none] at hx; exact hx.symm
lemma curlV {G:Gauge}{p:Clip}(P Q: Bed)(T:Towers S.patch.L){a A B γ:ℝ}(h:0<a)(he:P.dual_diag.strip a A)(hf:Q.diagonal.strip a B)(v:T.Deep a A 1)(H:Floor P p f γ B)(g:Towers.Diagonal S P Q T)(R:Forest S.ratio)(x:fieldDir G c 1)(u:Ps f):
 let Y:=Channel.rising R (installed S.ratio T.A0) x
 heat 0 (collect G Y) (.inl u)= ∑ y: Ps c, lambda (S:=S) P Q T u y • heat 0 (collect G x) (.inl y):=by
 intro Y; cases u with | mk i t=>
 let U (p:Site c)(r:PlaqAxes):=heat 0 (collect G x) (.inl (p,r))
 have ht(z:Ps c):heat 0 (collect G x) (.inl z)=dColor G c 1 x (ŧ _ z):=fundamental G ..
 ext1 j; rw [show heat 0 (collect G Y) (.inl (i,t))=dColor G f 1 Y (i,plaquette t) from (fundamental G Y i t)]; simp_rw [ht]; rw [WithLp.ofLp_sum,Finset.sum_apply]; simp only [WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]; -- tune
 have hx:= Work.F04.parts_stretch R (installed S.ratio T.A0) x j; change parts G 1 Y j=_ at hx
 change (Matrix.mulVec (d 1 f) (parts G 1 Y j)) (i,plaquette t)= _
 have hw:= psi_curl h he hf (show 1 ≤ 1 from le_rfl) v S.sizes H.diagonalInv g.stays
 rw [hx,Matrix.mulVec_mulVec,extracted,Matrix.mul_add,← Matrix.mul_assoc (d 1 f) (d 0 f), Exterior.closed 0,Matrix.zero_mul,add_zero,← show installed S.ratio (psi P Q T none)*d 1 c=d 1 f* installed S.ratio T.A0 from hw,← Matrix.mulVec_mulVec, Matrix.mulVec,dotProduct,←Equiv.sum_comp (ŧ c)]; rfl
end YM.CF.Font
