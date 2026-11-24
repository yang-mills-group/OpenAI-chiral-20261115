import YM.CF.Nacre.Mary
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{m:ℕ}
def duos (n: Side)(t:Cover): Site (More n):=wrap _ (2 • t)
def pinP (w:Cover): Equiv.Perm (Wind n):= Equiv.sumCongr ((Equiv.addRight (wrap n w)).prodCongr (Equiv.refl _)) (Equiv.refl _)
def pinch(t:Cover): Equiv.Perm (Trip m n):= Equiv.piCongrRight (fun _=>pinP (2 • t))
def rollH(t:Cover)(x:HopK n):HopK n:=(x.1+wrap _ t,x.2)
def ramH(t:Cover): Equiv.Perm (Single n):=((Equiv.addRight (wrap n t)).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)
lemma rolls(t:Cover)(x:HopK n):terse (rollH t x)=terse x+duos n t:=by change node (x.1+wrap _ t)= _; rw [← lag_i,Shape.nodex]; unfold Shape.anon lagX affine duos terse; simp
lemma printH(t:Cover)(x y:HopK n)(i j:Slot): gear (ramH t (x,i)) (ramH t (y,j))=gear (x,i) (y,j):=by unfold gear; change (↑(separation (terse (rollH t x)) (terse (rollH t y))):ℝ)=_; rw [rolls,rolls,separation_translate]; rfl
lemma pin_d(t:Cover)(x:HopK n)(p:PrizeX n): dial (terse (rollH t x)) (pinP (2 • t) p)=dial (terse x) p:=by rw [rolls]; rcases p with p|p; change separation (terse x+duos n t) (_+duos n t)=_; rw [separation_translate]; rfl; rfl
lemma notx_t(t:Cover)(i j:Single n)(r:Trip m n): notx m (ramH t i) (ramH t j) (pinch t r)=notx m i j r:=by rcases i with ⟨x,i⟩; rcases j with ⟨y,j⟩; unfold notx; rw [printH t x y i j]; congr 1; apply sum_congr rfl; intro a h; change (↑(dial (terse (rollH t x)) (pinP (2 • t) (r a))):ℝ) = _; rw [pin_d]; rfl
def jazzC(x y:HopK n): ℂ:=Rush.wind x.1 (lift (y.1-x.1))
lemma mon1(x y:HopK n): jazzC x y*jazzC x y=1:=fee_one _
lemma monF(x y:HopK n): ‖jazzC x y‖=1:=fee_norm _
lemma verge (x y:HopK n)(t:Cover): jazzC (rollH t x) (rollH t y)= Rush.wind x.1 t*Rush.wind y.1 t*jazzC x y:=by
 let p:=lift (y.1-x.1); have hx:x.1+wrap n p=y.1:=by unfold p; rw [wrap_lift,add_sub_cancel]
 have hl:=footFee (lagX t) x.1 p; rw [lag_p, lag_i,hx,lag_p] at hl
 let z:= (x.1+wrap n t); let u:=Rush.wind x.1 t
 change u*Rush.wind z ((1:Signed).act p)= jazzC x y*Rush.wind y.1 t at hl; rw [Signed.act_one] at hl
 change Rush.wind z (lift ((y.1+wrap _ t)-z))= _; rw [show _-z=y.1-x.1 by unfold z; abel]; apply mul_left_cancel₀ (a:=u) (by rw [← norm_pos_iff,show ‖u‖=1 from fee_norm _]; norm_num); rw [hl]; unfold u; rw [←mul_assoc,←mul_assoc,show Rush.wind _ _*Rush.wind x.1 t=1 from fee_one _,one_mul,mul_comm]
def Prints (P:Toy m n) :Prop:=∀ (t:Cover)(i j: Single n)(r:Trip m n), P (ramH t i) (ramH t j) (pinch t r)= (Rush.wind i.1.1 t*Rush.wind j.1.1 t) • P i j r

def Across (V:Bkg (More n)→Op (Single n)):Prop:=∀ t x,V (Yg (lagX t) x)=ZoneH (lagX t) (V x)
lemma y_up(t:Cover)(x:Site n)(V: Config group n)(w:Walk): travel (Lattice.translate (wrap n t) V) x w=travel V (x+wrap n t) w:=by
 induction w generalizing x with
 | nil=> rfl
 | cons a w h=> rw [travel,travel,h]; rw [add_right_comm x]; cases a with| mk a p=> cases p; rfl; simp [Step.read,Step.used,translate, add_sub_right_comm] -- tune
lemma pin_v(t:Cover)(x:Site n)(p:Wind n):boot (x+ wrap _ t) (pinP t p)=boot x p:=by cases p with
 | inl i=>unfold boot; change shiftH (x+wrap n t) (i.1+wrap n t)++ square _ _++ reverse (shiftH (x+wrap n t) (i.1+wrap n t))= _; rw [show shiftH (x+wrap n t) (i.1+wrap n t)=shiftH x i.1 by unfold shiftH; rw [add_sub_add_right_eq_sub]]; rfl
 | inr i=>rfl
lemma pre_a (P: Toy m n)(t:Cover)(U:Bkg (More n))(H:Prints P): cavil P (Yg (lagX t) U)=ZoneH (lagX t) (cavil P U):=by
 let V:=Yg (lagX t) U; ext ⟨⟨x,p⟩,i⟩ ⟨⟨y,q⟩,j⟩
 let k:HopK n:= (x,p); let w:HopK n:=(y,q); let z:=Rush.wind x t*Rush.wind y t
 let K:=rollH t k; let W:=rollH t w; have he : walkB k w V=walkB K W U:=by unfold walkB V K W; rw [rolls,rolls,Ylag,y_up]; unfold shiftH; rw [add_sub_add_right_eq_sub]; rfl
 have hh(r:Trip m n): mold P K W (pinch t r) U=z • mold P k w r V:=by
    have hv (a:Fin m): silt (terse k) (r a) V=silt (terse K) (pinch t r a) U:=by unfold V silt K; rw [Ylag,y_up,rolls, show pinch t r a=pinP (2 • t) (r a) from rfl, show duos n t=wrap _ (2 • t) from rfl,pin_v]
    unfold mold; rw [←he]; simp_rw [hv]; rw [←Matrix.smul_mul]; congr 1; ext a b; change P (ramH t (k,a)) (ramH t (w,b)) (pinch t r) _ = z • P _ _ r _; rw [H]; rfl
 rw [limo]; unfold cavil; rw [Matrix.of_apply,Matrix.of_apply]; change _=z*(∑ r,mold P K W r U) i j; conv_rhs=> rw [← Equiv.sum_comp (pinch (m:=m) t)]; -- maybe chooses lhs
 simp_rw [hh,← Finset.smul_sum,Matrix.smul_apply,smul_eq_mul,←mul_assoc]; rw [show z*z=1 by unfold z; rw [mul_mul_mul_comm,Rush.wind, Rush.wind, fee_one,fee_one,one_mul],one_mul]; -- tune
end YM.CF.Nacre
