import YM.SU5.Reconstruction.Marque.Concourse
import YM.Mink.Poincare
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Matrix Real Complex
open Mink Ray
open scoped Matrix MatrixGroups Topology InnerProductSpace Classical
variable (g h:Two) (x:E4)
local notation "ρ"=>Motion
abbrev Fit(g:Two):=∃ L:Lorentz, (Lorentz.act L:E4→E4)=ρ g
-- using generation lemma all Spin built from axes
noncomputable def MCourse : Passage ℝ where
  ok g:={x|Fit g}
  pass:= ⟨1,(funext fun p=>(identity p).symm)⟩
  plus{g h _ _} p q:= by obtain ⟨r,b⟩:=p; obtain ⟨t,a⟩:=q; exact ⟨r*t,funext (fun x=>by rw [multiplies]; change Lorentz.act _ _= _; rw [Lorentz.act_mul]; exact b ▸ a ▸ rfl)⟩
  opp{g _} p:= by obtain ⟨r,b⟩:=p; exact ⟨r⁻¹,funext fun x=>by apply (Lens g).injective; rw [Lens_on,Lens_on,Motion_inv]; rw[←congrFun b]; apply Lorentz.undoes⟩
lemma fullCost : MCourse.Upright:=by
   have hp{g:ℝ→Two}(i:Fin 3)(p:∀ v,ρ (g v)= Picket.move timeAxis i.castSucc (2*v)): MCourse.Agree g:=
      ⟨_,nowC.mpr (fun x:ℝ=>plainLimit _ (1:Wander ℝ)), fun x=> ⟨(fromAxis i).boost (2*x), (p x) ▸ (funext fun y=>(Picket.boost_eq ..).symm)⟩⟩
   exact ⟨hp (i:=2) (motionZ), hp (i:=0) (motionX), hp (i:=1) (motionY)⟩ -- explicit is i
lemma fitAll: Fit g:=by obtain ⟨u,p⟩:= fullCost.always g; exact p
noncomputable def onWorld(g:Two):Lorentz:=(fitAll g).choose
lemma onWorld_at:Lorentz.act (onWorld g) x=ρ g x:= congrFun (fitAll g).choose_spec x
lemma onWorld_mul:onWorld (g*h)=onWorld g*onWorld h:= by apply Lorentz.ext; intro p; rw [onWorld_at, Lorentz.act_mul,onWorld_at,onWorld_at,multiplies]
lemma onWorld_one:onWorld 1=1:=Lorentz.ext _ _ (fun x=> (onWorld_at ..).trans (identity x))
-- particular Rotation x→z (for sewing V). formulas.
noncomputable def low:ℝ:= Real.sqrt 2/2
lemma low_sq : 2*low^2=1:= by unfold low; nlinarith [Real.sq_sqrt (by norm_num:(0:ℝ)≤2)]
noncomputable def Nine := pin low low (-(low:ℂ)) low (by
    have h: (2:ℂ)*(low:ℂ)^2=1:= by exact_mod_cast low_sq
    linear_combination h)
lemma Ninety : (ρ Nine x) clock=x clock ∧ ρ Nine x 0 =- x 2∧ ρ Nine x 1=x 1∧ ρ Nine x 2=x 0:= by
 unfold Nine clock
 refine ⟨?_,?_,?_,?_⟩; all_goals (sway <;> first | linear_combination (x 0)*low_sq | linear_combination -(x 2)*low_sq| linear_combination (x 1)*low_sq| linear_combination (x 3)*low_sq)
lemma wing_turn: x∈ BridgeClub.Wedge clock 0 ↔ Motion Nine x∈ BridgeClub.Wedge clock 2:= by simp only [BridgeClub.Wedge,mem_setOf_eq,BridgeClub.Scope, (Ninety x).1,(Ninety x).2.2.2]
lemma turn_rail(s:ℝ): rehome Nine (Zip s)=Tuning s:=by
 have h: (2:ℂ)*(low:ℂ)^2=1:= by exact_mod_cast low_sq
 have hz:(↑(rich s):ℂ)⁻¹=(Real.exp (-s):ℝ):=by rw [Real.exp_neg,ofReal_inv]; rfl
 apply tone <;> simp only [rehome,A_mul,B_mul,C_mul,D_mul,A_inv,D_inv,C_inv,B_inv,Zip,Tope,Tuning,Pole,Nine,Ap,Bp,Cp,Dp, rich_val,Real.cosh_eq,Real.sinh_eq, Units.val_one,inv_one] <;> push_cast <;> first | (solve|ring)| linear_combination Complex.exp (s:ℂ)*h| linear_combination Complex.exp (-(s:ℂ))*h + (Complex.exp_neg (s:ℂ)) -- tune
variable (s:ℝ)
lemma crossBasin(p:ℂˣ): rehome Basin (Tope s p)=Tope (-s) p:= by apply tone <;> simp [rehome,Basin,Tope,Pole] <;> ring_nf <;> rw [Complex.I_sq] <;> ring -- tune
lemma blankOut (p:ℂˣ): rehome (Tope (s/2) p) Basin*Basin= bezel*Tope s p:= by
 have ht(w:ℝ): (Tope w p)⁻¹=Tope (-w) p:= inv_eq_of_mul_eq_one_left (by rw [←tope_add, neg_add_cancel,tope_one])
 unfold rehome; rw[ht]; have h: Basin * Tope (-(s/2)) p=Tope (s/2) p * Basin:=by apply mul_right_cancel (b:=Basin⁻¹); rw[mul_assoc _ Basin, mul_inv_cancel,mul_one]; exact (crossBasin (-(s/2)) p).trans (by rw [neg_neg])
 rw[mul_assoc (Tope _ p) Basin (Tope _ p),h,←mul_assoc,←tope_add,show s/2+s/2=s by ring,mul_assoc,reverse2 Basin basin_price, bezel_stays] -- need tope_add & reverse2 & bezel
end YM.Marque.Flow
