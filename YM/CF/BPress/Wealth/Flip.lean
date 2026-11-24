import YM.CF.BPress.Wealth.Row
/-!
eq:B-magcancel sym. For any translate over all PHYSICAL tangential sites in a channel, the shifted-square sum has a simple curl formula, with all horizontal shifts erased. Physical/tang origin here unchanged except the right flips chosen by proof in native coords. Keys C0,G computed with actual legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side} (v:Signed) (a t : Per s) (x : PlaqAxes) (k : Axis) (o : Site s) (w: Directions group s)

-- x physical root plus shift. reindex saved formula to use on vertical & pair legs
lemma translate_sum {F:Type*} [AddCommMonoid F](f: Site s→ F) : ∑ p:Tri s, f (o+event t p) =∑ p:Tri s, f (event (o 0+t) p):=by
 have he(p:Tri s): o+event t p=event (o 0+t) (Fin.tail o+p):=by funext i; refine Fin.cases ?_ ?_ i; rfl; intro k; simp [event, Fin.tail]
 simp_rw [he]; exact Equiv.sum_comp (Equiv.addLeft (Fin.tail o)) (fun p=> f (event (o 0+t) p))
def shiftLeg (p:Tri s) := v⁻¹.act (event t p)
def sleeve (u:Per s)(w:Directions group s):= ∑ p:Tri s, opSigns v k (w (event (if v.flip k then u-(step (v.perm k) :Site s) 0 else u) p,v.perm k))
private lemma horizontal_sum : ∑ p:Tri s, orbitW v w (o+shiftLeg v t p,k)= sleeve v k ((v.act o) 0+t) w:=by
 simp only [orbitW,address_inv, shiftLeg, v.act_add,v.act_inv]; unfold sleeve; split; next p=>
    have he(p:Tri s): v.act o + event t p-step (v.perm k)= (v.act o-step (v.perm k))+event t p:=by abel
    simp_rw [he]; rw [show _ + _ - (step (v.perm k):Site s) 0=(v.act o-step (v.perm k) : Site s) 0+t from (by simp; abel)]; exact translate_sum t (v.act o-step (v.perm k)) (fun i=> opSigns v k (w (i,v.perm k)))
 exact translate_sum t (v.act o) (fun i=> opSigns v k (w (i,v.perm k)))
-- unmarked times orientation explicit. note term legs signs remain in sleeve
lemma curl_eq : ∑ p:Tri s, orbitP v (o+shiftLeg v t p,x) w=
    sleeve v x.val.1 ((v.act o) 0+t) w + sleeve v x.val.2 ((v.act (o+step x.val.1)) 0+t) w -
    sleeve v x.val.1 ((v.act (o+step x.val.2)) 0+t) w - sleeve v x.val.2 ((v.act o) 0+t) w:=by
 let P:=x.val; let X(p:Tri s):= o+shiftLeg v t p; simp only [orbitP,LinearMap.coe_mk, AddHom.coe_mk, brandW,circle,sum_sub_distrib,sum_add_distrib]; change ∑ p:Tri s,orbitW v w (X p,P.1) + ∑ p:Tri s,orbitW v w (X p + step P.1,P.2) - ∑ p:Tri s,orbitW v w (X p+step P.2,P.1) - ∑ p:Tri s,orbitW v w (X p,P.2)=_; have he(p:Tri s)(x:Axis): X p+step x=o+step x+shiftLeg v t p:=by unfold X; abel
 simp_rw [he]; unfold X P; rw [horizontal_sum,horizontal_sum,horizontal_sum,horizontal_sum]
lemma step_quiet (p:v.perm k≠0) : (v.act (o+step k)) 0=(v.act o) 0:=by rw [act_step]; split<;> simp [Ne.symm p]
lemma cup_zero (p:v.perm x.val.1 ≠ 0)(h:v.perm x.val.2≠0): ∑ p:Tri s,orbitP v (o+shiftLeg v t p,x) w=0:=by rw [curl_eq, step_quiet v x.val.1 o p, step_quiet v x.val.2 o h]; abel
lemma turned_view (q:v.perm k ≠ 0): ((v*Signed.mirror k).act o) 0=(v.act o) 0:=by
 obtain ⟨j,h⟩:= v.perm.surjective 0; nth_rw 1 [←h]; nth_rw 1 [←h]; rw [Signed.act_mul,Signed.act_at,Signed.act_at]; have he:k≠j:=fun p=>q (p ▸ h); simp [Signed.act,Signed.mirror,he]
lemma same_sleeve {j : Axis} (p:k≠j): sleeve (v*Signed.mirror k) j t w= sleeve v j t w:= by simp only [sleeve,opSigns,Signed.mul_perm_apply,Signed.mirror,Equiv.refl_apply,Signed.mul_flip,p,decide_false,Bool.xor_false]
lemma mirror_orbit (q:v.perm k ≠ 0)(h:k≠x.val.1)(g:k≠ x.val.2):
    ∑ p:Tri s,orbitP (v*Signed.mirror k) (o+shiftLeg (v*Signed.mirror k) t p,x) w=∑ p:Tri s,orbitP v (o+shiftLeg v t p,x) w:=by
 rw [curl_eq,curl_eq]; simp_rw [turned_view v k _ q, same_sleeve v _ k w h,same_sleeve v _ k w g]
lemma no_color (e:v.perm x.val.1 = 0 ∨ v.perm x.val.2=0): psi v x=0:=by
 unfold psi; have he(i:Axis)(p:v.perm i=0):oriDir v i=0:=by rw [oriDir,p]; unfold opSigns; split <;> simp [backgroundDir]
 rcases e with g|g <;> simp [he _ g]
lemma mirror_color (p:k=x.val.1 ∨ k=x.val.2): psi (v*Signed.mirror k) x= -psi v x:=by
 unfold psi; have he(i:Axis)(p:k≠i): oriDir (v*Signed.mirror k) i=oriDir v i:=by simp only [oriDir,opSigns,Signed.mul_perm_apply,Signed.mul_flip,Signed.mirror, p,decide_false,Bool.xor_false,Equiv.refl_apply]
 have hx: oriDir (v* Signed.mirror k) k = -oriDir v k:=by simp only [oriDir,opSigns,Signed.mul_perm_apply,Signed.mul_flip,Signed.mirror, decide_true,Bool.xor_true,Equiv.refl_apply]; cases v.flip k<;> simp
 rcases p with e|e; · rw [e] at he hx; rw [e,hx,he _ x.property.ne]; simp
 rw [e] at he hx; rw [e,hx,he _ (x.property.ne')]; simp
end YM.CF.BPress.Wealth
