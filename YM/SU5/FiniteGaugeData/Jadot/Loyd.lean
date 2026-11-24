import YM.SU5.FiniteGaugeData.Jadot.Celeste
/-! # Aperture bill on Art. Rephase and signs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 17000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims Dijon Currency Fist Ziz Thera Spire Scroll Celeste Buffered
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Loyd
variable {n:Type*}[LinearOrder n][Fintype n]
abbrev Upt(Q:Op n) (x:Ket n): Prop:= acts Q x=x
abbrev Ram(T:Finset n): Ket n→ Prop:=Upt (cutM T)
inductive Art(h:ℝ)(Q:Op n)(S:Finset n): Bool→ FC n →ℝ→Prop where
 | hid(b:Bool): Art h Q S b 0 0
 | lone : Art h Q S false 1 1
 | chor(x:Ket n)(u:Upt Q x)(p:Ram S x): Art h Q S true (create x) (h*‖x‖)
 | thal(x:Ket n)(u:Upt (1-Q) x)(p:Ram S x): Art h Q S true (remove x) (h*‖x‖)
 | sum{b:Bool} {X Y:FC n}{x y:ℝ}:Art h Q S b X x→Art h Q S b Y y→ Art h Q S b (X+Y) (x+y)
 | work{a b:Bool}{X Y:FC n}{x y:ℝ}:Art h Q S a X x→Art h Q S b Y y→ Art h Q S (a.xor b) (X*Y) (2*x*y)
 | scale{a:Bool} {T:FC n}{x:ℝ}(z:ℂ):Art h Q S a T x→ Art h Q S a (z • T) (‖z‖*x)
 | pump{a:Bool}{T:FC n}{x y:ℝ}:Art h Q S a T x → x≤ y → Art h Q S a T y
variable {S T V R:Finset n}{Q P Q':Op n}{X Y:FC n}{b a:Bool}{h w l c k u:ℝ}
lemma Ram.incl {x:Ket n} (p:Ram S x)(l:S⊆T):Ram T x:=by nth_rw 1 [Ram,Upt]; nth_rw 1 [←p]; rw [←act_mul,cut_meet,inter_eq_right.mpr l,p]
lemma Ram.cost {A:Op n}(u:cellU S A c)(p:0≤ c)(v:S.card≤ l)(x:Ket n)(t:Ram S x): ‖acts A x‖ ≤ c*l*‖x‖:=by
 have he: x=∑ i∈ S,x.ofLp i• basisKet i:=by refine (basis_expand x).symm.trans ?_; exact (sum_subset (subset_univ _) fun i _ v=>by rw [((within_test ..).mp t i v),zero_smul]).symm -- tune orientation
 nth_rw 1 [he]; rw [map_sum]; apply (norm_sum_le ..).trans; calc
    _ ≤ ∑ i∈ S, c*‖x‖ := by apply sum_le_sum; intro i v; rw [map_smul,norm_smul,mul_comm _ ‖x‖]; exact mul_le_mul (PiLp.norm_apply_le _ _) (u i v) (norm_nonneg _) (norm_nonneg x)
    _ ≤ _:=by rw [sum_const,nsmul_eq_mul,←mul_assoc,mul_comm c l]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right v p) (norm_nonneg _)
lemma Upt.flip (V:UNI n)(P Q:Op n)(x:Ket n)(t:Upt P x)(p:twist V P=Q): Upt Q (acts V.val x):=by unfold Upt; rw [←p,←Fock.swivel,t]
namespace Art
variable (x:Art h Q S b X c)
include x
lemma sameRoom : Sector S b X:=by
 induction x with
 | hid=> exact Sector.zero _
 | lone=> exact Sector.one
 | chor x h p=> exact .makeP x p
 | thal x h p=> exact (Sector.makeP x p).contr
 | sum _ _ a b=> exact .add a b
 | work _ _ a b=> exact .mul a b
 | scale _ _ a=> exact .scale a _
 | pump _ _ a=> exact a
lemma bless (u:S⊆T):Art h Q T b X c:=by
 induction x with
 | hid=> exact hid _
 | lone=> exact lone
 | chor v p q=> exact chor _ p (Ram.incl q u)
 | thal v p q=> exact thal _ p (Ram.incl q u)
 | sum _ _ a b=> exact sum a b
 | work _ _ a b=> exact work a b
 | scale _ _ a=> exact scale _ a
 | pump _ p a=> exact pump a p
lemma decrease (u:w≤h): Art w Q S b X c:=by
 induction x with
 | hid=> exact hid _
 | lone=> exact lone
 | chor v p q=> exact (chor _ p q).pump (mul_le_mul_of_nonneg_right u (norm_nonneg _))
 | thal v p q=> exact (thal _ p q).pump (mul_le_mul_of_nonneg_right u (norm_nonneg _))
 | sum _ _ a b=> exact sum a b
 | work _ _ a b=> exact work a b
 | scale _ _ a=> exact scale _ a
 | pump _ p a=> exact pump a p
lemma minus : Art h Q S b (-X) c:=by simpa using scale (-1:ℂ) x
lemma reflectX(U:UNI n)(q:twist U Q=1-Q')(p:twist U (cutM S)=cutM T):Art h Q' T b (theta U X) c:=by
 induction x with
 | hid=> rw [theta_zero]; exact hid _
 | lone=> rw [theta_one]; exact lone
 | chor v g t=> rw [theta_upV]; have hv:=scale (-Complex.I) (thal (acts U.val v) (Upt.flip U Q (1-Q') v g q) (Upt.flip U _ _ v t p) (h:=h)); rw [act_unit_norm,norm_neg, Complex.norm_I,one_mul] at hv; exact hv
 | thal v g t=> rw [theta_downV]; have hv:=scale Complex.I (chor (acts U.val v) (Upt.flip U (1-Q) Q' v g (by rw [map_sub,map_one,q]; abel)) (Upt.flip U _ _ v t p) (h:=h)); rw [act_unit_norm, Complex.norm_I,one_mul] at hv; exact hv
 | sum _ _ a b=> rw [theta_add]; exact sum a b
 | work _ _ a b=> rw [theta_mul]; exact work a b
 | scale z _ i=> simpa only [theta_smul,norm_star] using scale (star z) i
 | pump _ p a=> exact pump a p
variable [Nonempty n] {M Z U W N L:Op n} {p r A₀:ℝ}
-- normalized source. second for unreg peak.
structure Marge(h:ℝ)(Q M Z:Op n)(S:Finset n):Prop where
  live: Milieu Q M
  root: Spear Q Z
  rise(x:Ket n)(t:Upt Q x)(l:Ram S x):‖acts (Pall M Z) x‖ ≤ h*‖x‖
  fall(x:Ket n)(t:Upt (1-Q) x)(l:Ram S x):‖acts (star (Hail M Z)) x‖ ≤ h*‖x‖
lemma basic (v:1≤h): ‖X‖≤ c:=by
 induction x with
 | hid=> exact norm_zero.le
 | lone=> exact norm_one.le
 | chor x p q=> exact (Flare.cost_pe false x).trans (le_mul_of_one_le_left (norm_nonneg _) v)
 | thal x p q=> exact (Flare.cost_pe true x).trans (le_mul_of_one_le_left (norm_nonneg _) v)
 | sum _ _ a b=> exact (norm_add_le ..).trans (add_le_add a b)
 | @work i j X Y p r x y a b=> exact (norm_mul_le ..).trans ((mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a)).trans (by have ht:= (norm_nonneg _).trans a; have hp:0≤r:=(norm_nonneg _).trans b; linarith only [mul_nonneg ht hp])) -- tune
 | scale _ _ a=> exact (norm_smul ..).le.trans (mul_le_mul_of_nonneg_left a (norm_nonneg _))
 | pump _ p a=> exact a.trans p
-- operated costs.
lemma leanP(O:Marge h Q M Z S): ‖Celeste.cost M Z X‖≤ c:=by
 have he:= Pall.mun O.live O.root; have hp:= Pall.wun O.live O.root; unfold Celeste.cost
 induction x with
 | hid=> rw [lever.nilV he hp]; exact norm_zero.le
 | lone=> rw [lever.stockI he hp]; exact norm_one.le
 | chor v g0 q=> rw [lever.uphill he hp]; exact (Flare.cost_pe false _).trans (O.rise v g0 q)
 | thal v g0 q=> rw [lever.takeDown he hp]; exact (Flare.cost_pe true _).trans (O.fall v g0 q)
 | sum _ _ a b=> rw [lever.sums he hp]; exact (norm_add_le ..).trans (add_le_add a b)
 | @work i j X Y p r x y a b=> rw [lever.mult he hp]; exact (norm_mul_le ..).trans ((mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a)).trans (by have ht:= (norm_nonneg _).trans a; have hp:0≤r:=(norm_nonneg _).trans b; linarith only [mul_nonneg ht hp])) -- tune
 | scale _ _ a=> rw [lever.semi he hp]; exact (norm_smul ..).le.trans (mul_le_mul_of_nonneg_left a (norm_nonneg _))
 | pump _ p a=> exact a.trans p
lemma crux_turn (l:Marge h Q M Z S)(v:∀x:Ket n,Upt Q x→ Ram S x→Ram T (acts (Pall M Z) x))(t:∀x:Ket n,Upt (1-Q) x→Ram S x→Ram T (acts (star (Hail M Z)) x)): Sector T b (Celeste.cost M Z X):=by
 have he:= Pall.mun l.live l.root; have hp:=Pall.wun l.live l.root; unfold Celeste.cost
 induction x with
 | hid=> rw [lever.nilV he hp]; exact .zero _
 | lone=> rw [lever.stockI he hp]; exact .one
 | chor x h p=> rw [lever.uphill he hp]; exact Sector.makeP _ (v x h p)
 | thal x h p=> rw [lever.takeDown he hp]; exact (Sector.makeP _ (t x h p)).contr
 | sum _ _ a b=> rw [lever.sums he hp]; exact a.add b
 | work _ _ a b=> rw [lever.mult he hp]; exact a.mul b
 | scale _ _ a=> rw [lever.semi he hp]; exact a.scale _
 | pump _ p a=> exact a
-- difference cost, no $\kappa$ renewal.
lemma humane (q0:0≤p)(l:Marge h Q M Z S)(v:Marge h Q N L S)
 (i:∀ x:Ket n,Upt Q x→Ram S x→‖acts (Pall M Z - Pall N L) x‖≤ p*h*‖x‖)
 (j:∀ x:Ket n,Upt (1-Q) x→Ram S x→ ‖acts (star (Hail M Z)-star (Hail N L)) x‖≤ p*h*‖x‖): ‖Celeste.cost M Z X-Celeste.cost N L X‖ ≤ p*c:=by
 let A:= Pall M Z; let B:=Pall N L; have he:= Pall.mun l.live l.root; have hp:=Pall.wun l.live l.root; have hj:=Pall.mun v.live v.root; have hd:=Pall.wun v.live v.root; unfold Celeste.cost
 induction x with
 | hid=> rw [lever.nilV he hp,lever.nilV hj hd,sub_zero,norm_zero,mul_zero]
 | lone=> rw [lever.stockI he hp,lever.stockI hj hd,sub_self,norm_zero,mul_one]; exact q0
 | chor x g h=> rw [lever.uphill he hp,lever.uphill hj hd,←map_sub,←act_sub,←mul_assoc]; exact (Flare.cost_pe false _).trans (i x g h)
 | thal x g h=> rw [lever.takeDown he hp,lever.takeDown hj hd]; unfold remove; rw [←star_sub,norm_star,←map_sub,←act_sub,←mul_assoc]; exact (Flare.cost_pe false _).trans (j x g h)
 | sum _ _ a b=>
    rw [lever.sums he hp,lever.sums hj hd]; set X:= Pall M Z; simp_rw [show ∀ x y p q: FC n,x+y-(p+q)=x-p+(y-q) from (fun x y p q=> by abel)]; rw [mul_add p] -- tune rewrite
    exact (norm_add_le ..).trans (add_le_add a b)
 | @work α b x y u c aX bY ih v'=>
    rw [lever.mult he hp,lever.mult hj hd]; let F:= Celeste.lever A (Hail M Z); let G:= Celeste.lever B (Hail N L); have hF:‖F x‖≤u:= leanP aX l; have hG:‖G y‖≤c:=leanP bY v; change ‖F x*F y-G x*G y‖≤_; rw [show F x*F y-G x*G y= F x*(F y-G y) + (F x-G x)*G y from by noncomm_ring]
    exact (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul hF v' (norm_nonneg _) ((norm_nonneg _).trans hF))) ((norm_mul_le ..).trans (mul_le_mul ih hG (norm_nonneg _) (mul_nonneg q0 ((norm_nonneg _).trans hF))))).trans_eq (by ring))
 | @scale _ X u z a b=> rw [lever.semi he hp,lever.semi hj hd,←smul_sub,norm_smul, mul_left_comm]; exact mul_le_mul_of_nonneg_left b (norm_nonneg _) -- order
 | pump _ h a=> exact a.trans (mul_le_mul_of_nonneg_left h q0)
end Art
open Art
/- use Art only for charge. Gate any tilt.P. -/
section
variable [Nonempty n] {M Z:Op n}{Y:FC n} (p:Standing Q P)(Tim: Milieu Q M)(v:Spear Q Z)
include p
lemma kWeight(f:Wave n)(y: Sea Q f)(X:FC n): Volt Q P X= inner ℂ f (acts (smut Q P X) f):= by rw [mission p]; exact pressORT p.carpet (mantleP p.carpet) y _
lemma inner_diff(f:Wave n)(y:Sea Q f)(X Y:FC n): |(inner ℂ f (acts X f)-inner ℂ f (acts Y f)).re| ≤ ‖X-Y‖:=by
 rw [←inner_sub_right, ←act_sub]; exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm ..).trans (by rw [y.2,one_mul]; exact (wing_opy ..).trans_eq (by rw [y.2,mul_one]))) -- tune orientation
lemma chip (m:Marge h Q (Lemp Q P) (Zemp Q P) S)(F:Art h Q S a X c): ‖Volt Q P X‖ ≤ c:=by
 rw [mission p]; let f:= mantle Q; have he:‖f‖=1:=(mantleP p.carpet).2; let V:=smut Q P X; apply le_trans (norm_inner_le_norm ..); change ‖f‖*‖acts V f‖≤_; rw [he,one_mul]; exact (wing_opy ..).trans (by rw [he,mul_one]; exact F.leanP m)
-- Single insertion of interest. use $add linear`. identity.I.Skelling.
include Tim v
lemma harvestX (f:Wave n)(y:Sea Q f)(F:‖Celeste.cost M Z X‖ ≤ h)(U:‖Celeste.cost M Z X - smut Q P X‖ ≤ c):
 ‖acts (star (Celeste.cost M Z (1+X))) f‖≤ Real.exp ((Volt Q P X).re+c+h^2/2):=by
 let A:=Celeste.cost M Z X; let z:=smut Q P X; have he:= Pall.mun Tim v; have hp:= Pall.wun Tim v; unfold Celeste.cost; rw [lever.sums he hp,lever.stockI he hp]; let V:= acts (star A) f; let u:= (inner ℂ f (acts z f)).re; rw [star_add,star_one,act_add,act_one, kWeight p f y]; change ‖f+V‖ ≤ Real.exp (u+c+h^2/2); apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp; have hx := (Real.add_one_le_exp (2*(u+c+h^2/2))); have hv : (inner ℂ f V).re ≤ u+c := by
    have hz: V=acts (star A) f:=rfl; let y':= inner ℂ f (acts A f); have hu: inner ℂ f V=star y':=by unfold V y'; rw [←act_inner, star_star]; exact (inner_conj_symm ..).symm -- tune
    have ht := abs_le.mp ((inner_diff p f y A z).trans U); rw [Complex.sub_re] at ht; rw [hu]; change y'.re≤_; linarith only [ht.2]
 have hh: ‖V‖≤h:= (wing_opy ..).trans (by rw [y.2,mul_one,norm_star]; exact F)
 rw [norm_add_sq (𝕜:=ℂ), y.2]; change (1:ℝ)^2+2*(inner ℂ f V).re+_ ≤ _; rw [sq (Real.exp _),←Real.exp_add,←two_mul]; nlinarith only [hx,hv,pow_le_pow_left₀ (norm_nonneg V) hh 2]
end
end Loyd
end YM.CF.Fock.Reduction
