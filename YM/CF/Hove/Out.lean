import YM.CF.Hove.Bay
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable{c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male)(j m:ℕ)(e:Use j G.count T)(p:Even j)(u:Bool)(M:Male)(o:Site f)
abbrev stickW(i:Kt):Single f:=((o,i.1),i.2)
abbrev tagF:Kt:=Classical.arbitrary _
def feeT(k:Single c):ℝ:= streak G m (stickW o tagF) k
lemma feeK(k:Single c):1 ≤ feeT G m o k:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
abbrev jazzP:=fan G w T j u M
def lensF :Matrix (Single f) (Single c) ℂ:= skewE j M u f 1 * fan G w T j u M []
abbrev toneT (s:Kt):=pax G w T j u M (stickW o s)
def flute (s:Kt)(x:Cover)(k:Single c):ℂ:= Rush.wind o x*lensF G w T j u M (plot (stickW o s) x) k
def apron (x:Cover)(i s:Kt):Single c→ℂ:= ∑ z:Axis, (moonB u z x i s) • toneT G w T j u M o s [z] 0
def vowel (i s:Kt):Single c→ℂ:= (baseF u i s) • toneT G w T j u M o s [] 0
def indexF(i:Kt): Single c→ℂ:= ∑ s:Kt,vowel G w T j u M o i s
def plyT(i:Kt)(x:Cover): Single c→ℂ:= ∑ s:Kt,apron G w T j u M o x i s
variable(h:1≤j)(X:Cover)(z':Single c)(i s:Kt)
local notation "Pa"=> Paw j M u
local notation "V"=> toneT G w T j u M o
local notation "R"=> Tap.trix
local notation "Y"=> (baseF u)
local notation "Z"=> (moonB u)
local notation "H_"=> (V s)
include h
lemma boatT : flute G w T j u M o i X z'=∑ s:Kt, ∑' x:Cover,Pa x i s*V s [] (X+x) z':=by
 obtain ⟨c₂,v,H⟩:=pawn_p j 1 h u; unfold flute lensF; rw [← snapP _ h M,mornY _ _ _ _ _ _ 1 (H M),Finset.mul_sum]; apply sum_congr rfl; intro k _; rw [←tsum_mul_left]; apply tsum_congr; intro x; unfold toneT pax; dsimp only [stickW,plot]; rw [route_H, map_add,←add_assoc o]; ring
local notation "Vκ"=> V s
local notation "ζκ"=> vowel G w T j u M o i s
local notation "ωκ"=> apron G w T j u M o X i s
lemma moxT : let G(x:Cover):= Pa x i s* (H_ [] 0 z'+R H_ (X+x) z'); Summable G ∧ (∑' x:Cover,G x)=ζκ z'+ωκ z':=by
 intro J; let f:= fun x:Cover=> Pa x i s; obtain ⟨A,h',pX⟩:= pawn_p j 1 h u; have hK:= pX M i s
 let B(x:Cover):= H_ [] 0 z'; let Zi (a:Axis):= H_ [a] 0 z'; let g(a:Axis)(x:Cover):= ( (X+x) a:ℂ )*f x * Zi a
 have ht(a:Axis):Summable (g a)∧ (∑' x:Cover,g a x)= moonB u a X i s * Zi a:=by
    have hp:= hK.falls.2.1.of_norm.mul_left (X a:ℂ); have hb:= (moments hK (by omega) a).1; unfold g; constructor
    · simpa only [Pi.add_apply,Int.cast_add,add_mul (_:ℂ) (_:ℂ) (f _)] using (show Summable (fun x:Cover=> ((X a:ℂ) * f x+(x a:ℂ)*f x) *Zi a) from (hp.add hb).mul_right _)
    rw [tsum_mul_right]; congr 1; change _ = (X a:ℂ) * baseF u i s+ _; rw [←mixY u M h, ←mox u M h]; simp_rw [Pi.add_apply,Int.cast_add,add_mul]; rw [hp.tsum_add hb,tsum_mul_left] -- tune
 have hp(a):= (ht a).1; have hh(x:Cover):J x= f x*H_ [] 0 z'+ ∑ a:Axis, g a x:=by unfold J trix; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum,mul_add]; congr 1; refine Finset.sum_congr rfl fun j _=> ?_; unfold g f; ring
 have hv:= hK.falls.2.1.of_norm.mul_right (H_ [] 0 z'); have hz:= summable_sum (s:=univ) (fun a (_:a∈ (univ:Finset Axis))=>hp a)
 constructor
 · rw [funext hh]; exact hv.add hz
 simp_rw [hh]; rw [hv.tsum_add hz,Summable.tsum_finsetSum (fun a _=>hp a),tsum_mul_right, show (∑' x:Cover,f x)= _ from mox u M h _ _]; simp_rw [(ht _).2,apron, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; rfl -- tune
variable (C A K:ℝ)(uP:RailP m (Paw j M u) C)(U:0≤A)(hZ:0≤K)
local notation "Fx"=> (feeT G m o)
omit h
include uP U
lemma post_P (hp:∀ (s:Kt) (x:Cover),paidX Fx (V s [] x) ≤ A * ratioY (Tap.oneF G) m x)(h:1≤j) : paidX Fx (flute G w T j u M o i X)≤ Fintype.card Kt * (A * ratioY (Tap.oneF G) m X * C):=by
 let Ft(s:Kt)(z:Single c):= ∑' x:Cover, Pa x i s* V s [] (X+x) z; -- T shadow.Name
 have hv(s):paidX Fx (Ft s)≤ A*ratioY (Tap.oneF G) m X*C:=by
    let B:= A*ratioY (Tap.oneF G) m X
    have hb(x:Cover): paidX Fx (V s [] (X+x))≤B*tweight m x:= (hp s _).trans ((mul_le_mul_of_nonneg_left (ray_m (show 1 ≤ Tap.oneF G by unfold Tap.oneF; exact_mod_cast G.count.property) X x) U).trans_eq (mul_assoc ..).symm)
    exact (paid_l Fx (uP i s) (feeK G _ o) _ hb (by unfold B ratioY; positivity)).2
 rw [show flute _ _ _ _ _ _ o i X=∑ s:Kt,Ft s from ?_]; swap; · ext1 z; rw [Finset.sum_apply]; exact boatT G w _ _ _ M o h X z i
 apply (p_posts _ (fun s=> zero_le_one.trans (feeK G _ o s)) _ Ft).trans; apply (sum_le_sum (fun s _=> hv s)).trans; simp
omit U
include hZ
lemma post_Y (hp:∀ (s:Kt)(x:Cover), paidX Fx (thorn (V s) x) ≤ K * tweight m x)(h:1≤j) : paidX Fx (flute G w T j u M o i X-(indexF G w T j u M o i + plyT G w T j u M o i X)) ≤ Fintype.card Kt * (K*tweight m X*C):=by
 let Uν:= flute G w T j u M o i
 let Vν:= indexF G w T j u M o i
 let W:= plyT G w T j u M o i
 let J(s:Kt)(z:Single c):= ∑' x:Cover, Pa x i s * thorn (V s) (X+x) z
 have hx(s:Kt) : (∀ z:Single c,Summable fun x:Cover=> Pa x i s * thorn (V s) (X+x) z) ∧ paidX Fx (J s) ≤ K*tweight m X*C:=by
    apply paid_l _ (uP i s) (feeK G m o) (fun x=>thorn (V s) (X+x)) (fun x=> (hp s _).trans ((mul_le_mul_of_nonneg_left (tw_n m X x) hZ).trans_eq (mul_assoc ..).symm)) (mul_nonneg hZ (tw_pos ..)) -- tune
 change paidX Fx _ ≤ _; rw [show Uν X -(Vν+ W X)= ∑ s:Kt, J s from ?_ ] -- definal
 swap
 · unfold Uν Vν W indexF plyT; ext1 z; rw [Pi.sub_apply,Pi.add_apply, Finset.sum_apply, Finset.sum_apply,Finset.sum_apply, ←sum_add_distrib, boatT G w T j u M o h,←sum_sub_distrib]; apply sum_congr rfl; intro k _; obtain ⟨r,y⟩:=moxT G w T j u M o h X z i k -- order
   let F(x:Cover):=Pa x i k; have he(x): Pa x i k* V k [] (X+x) z = F x*thorn (V k) (X+x) z +Pa x i k*(V k [] 0 z +trix (V k) (X+x) z):=by simp only [thorn,F,Pi.sub_apply,Pi.add_apply]; ring
   simp_rw [he]; rw [(hx k|>.1 z).tsum_add r,y,add_sub_cancel_right]
 apply (p_posts _ (fun s=> zero_le_one.trans (feeK G _ o s)) _ _).trans; apply (sum_le_sum (fun i _=> (hx i).2)).trans; simp
end YM.CF.Hove
