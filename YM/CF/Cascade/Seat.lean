import YM.CF.Cascade.Sectors
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Pec
abbrev pulse (n:Side):=Ember.pinch n
lemma glance (v: Air n)(u:CoreX)(p:‖u‖=1)(g:‖v‖≤1):‖pour n u v‖≤1:=by
 apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; change ‖pill n v i • u‖≤ 1; rw [norm_smul,p,mul_one]; unfold pill; split; exact (norm_le_pi_norm v _).trans g; simp
lemma crayon (v:Cloud n)(g:‖v‖≤1)(i: Blip (More n))(s:Signed): ‖collect group (litX s v) i‖≤1:=by
 change ‖Bid.pulled v s (Channel.bondBody _ i)‖≤_; rw [Channel.pulled_edge]; split; rw [norm_neg]; exact (norm_le_pi_norm v _).trans g; exact (norm_le_pi_norm v _).trans g
lemma route_p (A:Links (Per n) CoreX)(p:∀ i,‖A i‖≤1)(i:Site n)(x:Walk): ‖linkSum A i x‖≤ x.length:=by
 induction x generalizing i with
 | nil=>simp [linkSum]
 | cons j l H => rw [linkSum]; apply (norm_add_le ..).trans; rw [List.length_cons, Nat.cast_add,Nat.cast_one,add_comm (l.length:ℝ)]; exact add_le_add (by split; rw [norm_neg]; exact p _; exact p _) (H _)
def Sway {Y:Type*}[NormedAddCommGroup Y](V:Links (Per n) Y)(b:ℝ):Prop:=∀ x:Site n,∀ i:Axis,∀ t:Step, ‖V (x+t.vec,i)-V (x,i)‖≤ b
lemma partSound (v:Air n)(p:∀ x: Orig n,∀ t:Step,‖v (x+t.vec)-v x‖≤ b)(u: CoreX)(h:‖u‖=1)(t:0≤b):Sway (collect group (pour n u v)) b:=by
 intro x i s; unfold collect; change ‖(if coord i=coord 1 then v (x+s.vec) else 0) • u-(if coord i=coord 1 then v x else 0) • u‖≤_; split_ifs; · rw [←sub_smul,norm_smul,h,mul_one]; exact p _ _
 simpa only [sub_self,norm_zero]
lemma spunV (v:Cloud n)(p:Sway (collect group v) b)(s:Signed): Sway (collect group (litX s v)) b:=by
 let F:=collect group v; have he(i:Blip (More n)):collect group (litX s v) i= if s.flip i.2 then -F (sendEdge s 0 i) else F (sendEdge s 0 i):=Channel.pulled_edge .. -- namespace inspect
 intro x a t; rw [he,he]; let y:= sendEdge s 0 (x,a); let w: Site (More n):= (t.rotate s).vec -- tune
 have hz :sendEdge s 0 (x+t.vec,a)=(y.1+w,y.2):=by unfold sendEdge y w; simp [sendEdge,Step.used,affine,Step.vec_rotate,Signed.act_add]; split <;> simp [*] <;> abel -- tune
 simp only at *
 rw [hz]; split; rw [neg_sub_neg,norm_sub_rev]; apply p
 exact p _ _ _
lemma squareK {V:Cloud n}(h: Sway (collect group V) b)(s:Orig n)(a: Signed)(y:Orig n)(i:PlaqAxes): ‖heat y (collect group (litX a V)) (Sum.inl (s,i))‖≤ b+b:=by
 have hp:=spunV V h a; let F:=collect group (litX a V); let p:=i.val.1; let q:=i.val.2
 have hx:linkSum F s (square p q)=(F (s+step p,q)-F (s,q))-(F (s+step q,p)-F (s,p)):=by simp [linkSum,square,Step.used,posDir,negDir,Step.vec,sub_eq_add_neg]; abel_nf -- tune
 unfold Font.heat; change ‖linkSum F _ _‖≤ _; rw [hx]; exact (norm_sub_le ..).trans (add_le_add (hp s q (posDir p)) (hp s p (posDir q)))
lemma softness (v:Cloud n)(b:ℝ)(hc:‖v‖≤1)(h:Sway (collect group v) b)(p: pulse n ≤ b)(a:Signed) (x:Orig n)(u w: Ok n):‖heat x (collect group (litX a v)) u‖≤2*b*(1+contour x u w)^2:=by
 let y:=More n; let c:= contour x u w; have he:=ct_pos x u w; have hp:0<b:= (pinch_pos n).trans_le p
 cases u with
 | inl i=>exact (squareK h _ a _ _).trans ((two_mul b).symm.le.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (le_add_of_nonneg_right he))))
 | inr i=>
   apply (route_p (collect group (litX a v)) (fun i=> crayon v hc i a) x (swirl _ i)).trans; rw [swirl,List.length_replicate]; have hm: ((More n).val:ℝ)* pulse n= 2*Real.pi:=by unfold pulse Ember.pinch; have hz:0 < (n.val:ℝ):= side_pos n; simp [More]; field_simp
   unfold contour dial; let q:=dial x w; change (↑(More n).val:ℝ)≤ 2*b*(1+ ((More n).val+ (q:ℝ)))^2
   let z:=((More n).val:ℝ); have hv:0≤z:= Nat.cast_nonneg _; have ht:1≤ b*z:=by nlinarith only [Real.pi_gt_three,hm,mul_le_mul_of_nonneg_left p hv]
   change z≤ 2*b*(1+ (z+ (q:ℝ)))^2
   calc
     z ≤ b*z*z := le_mul_of_one_le_left hv ht
     _ ≤ 2*b*(1+(z+(q:ℝ)))^2:=by
        rw [mul_assoc,pow_two,← pow_two,← pow_two]; gcongr; linarith; linarith only [show (0:ℝ)≤q from Nat.cast_nonneg _]
lemma dataFee (v:Cloud n)(b:ℝ)(hc:‖v‖≤1)(h:Sway (collect group v) b)(p:pulse n≤ b)(g:0<a)(x:Site n)(s:Signed)(P:Dues n):‖datam (node x) P (litX s v)‖≤ (4*b^2*momentPrice 4 a)*cents (node x) P a:=by
 unfold datam cents; simp_rw [Finset.mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)); rw [norm_smul]; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 have hx:=softness v b hc h p s (node x) i j; have he:= softness v b hc h p s (node x) j i; let c:=contour (node x) i j; rw [show contour (node x) j i=c by unfold contour c; unfold contour; rw [add_comm]] at he -- tune
 let D:= 2*b*(1+c)^2; have hD:0≤D:=(norm_nonneg _).trans he; have ht:=ct_pos (node x) i j; apply (norm_inner_le_norm (𝕜:=ℝ) _ _).trans; apply (mul_le_mul hx he (norm_nonneg _) hD).trans; unfold nick; change D*D≤ _; have hh : 1≤1+c:= le_add_of_nonneg_right ht; unfold D; calc
   _ = 4*b^2*(1+c)^4:=by ring
   _ ≤ 4*b^2*(momentPrice 4 a*Real.exp (a*c)):= mul_le_mul_of_nonneg_left (spendMoment 4 g ht) (by positivity)
   _ ≤ _:=by
      rw [← mul_assoc]; unfold c; refine mul_le_mul_of_nonneg_left ?_ (by have he:=momentPrice_pos 4 g; positivity); exact le_mul_of_one_le_left (Real.exp_pos _|>.le) hh
end YM.CF.Cascade
