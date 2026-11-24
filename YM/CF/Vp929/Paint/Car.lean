import YM.CF.Vp929.Paint.Run
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
local notation "ℙ"=> Fin 4
structure Car (J I:Type*)(τ:I→I)(k:ℕ) where
 run : J × RunX k ≃ I
 same(j)(x:RunX k):run (j,x+1)=τ (run (j,x))
variable {J J' I L:Type*}{τ:I→I}{σ:L→L}{k:ℕ}
local notation "Ξ"=> RunX k
namespace Car
variable [Fintype J] [Fintype J'] [Fintype I] [Fintype L] [DecidableEq J][DecidableEq J'][DecidableEq I][DecidableEq L]
variable (p:Car J I τ k)(q:Car J' L σ k)
def carriage (x:I→ℙ):ℤ:= ∏j:J,W k (fun i:Ξ=>x (p.run (j,i)))
abbrev wash (h:Mask I)(j:J):Mask Ξ:=fun i=>h (p.run (j,i))
def seat : (J→Ξ→ℙ) ≃ (I→ℙ) where
 toFun x i:=x (p.run.symm i).1 (p.run.symm i).2
 invFun x j v:=x (p.run (j,v))
 left_inv x:= by ext; simp
 right_inv x:= by ext; simp
protected lemma sector(h:Mask I): ∑x:I→ℙ,p.carriage x * ∏i:I,h i (x i)=∏j:J,poll (p.wash h j) (Rc k) (circle k):=by
 rw [← Equiv.sum_comp p.seat (fun x=>p.carriage x * ∏i:I,h i (x i))]; simp_rw [← Wmask]; rw [Fintype.prod_sum]; refine sum_congr rfl fun i _=>?_; rw [← p.run.prod_comp (fun v=> h v (p.seat i v)), Fintype.prod_prod_type, Finset.prod_mul_distrib]; simp [carriage,Car.seat,wash]
lemma health(x:I→ℙ):0 ≤ p.carriage x:= Finset.prod_nonneg fun _ _=> Wnn ..
lemma charge_total:0<∑x:I→ℙ,p.carriage x:=by have v:0 < ∏j:J,poll (p.wash 1 j) (Rc k) (circle k):= Finset.prod_pos fun _ _=> (poll_circ (X:=Rc k) (by simp [Rc])); rw [← p.sector] at v; simpa using v
lemma halves(h t: Mask I)(X:∀i,ApartM h t i i)(Y:∀i,ApartM h t i (τ i)): (∑x:I→ℙ,p.carriage x*∏i:I, (h*t) i (x i)) * (∑x:I→ℙ,p.carriage x) =(∑x:I→ℙ,p.carriage x*∏i:I,h i (x i)) * (∑x:I→ℙ,p.carriage x*∏i:I,t i (x i)):=by
 have e:=p.sector 1; simp only [Pi.one_apply,prod_const_one,mul_one] at e; rw [p.sector,p.sector,p.sector,e,← Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
 apply prod_congr rfl; intro i _; exact Wsector (p.wash h i) (p.wash t i) (fun i=> X _) (fun j=> by unfold wash; change ApartM h t _ _; rw [p.same]; exact Y _ )
lemma legal(x:I→ℙ)(i:I)(v:x i=x (τ i)): p.carriage x=0:=by
 obtain ⟨⟨j,k⟩,rfl⟩:=p.run.surjective i; rw [← p.same] at v; exact Finset.prod_eq_zero (Finset.mem_univ j) (Wfails (fun t=>x (p.run (j,t))) k v)
section
variable (e:I≃ L)(u:∀x,e (τ x)=σ (e x))
def carj(j:J):J':=(q.run.symm (e (p.run (j,0)))).1
def caret(j:J):Ξ:=(q.run.symm (e (p.run (j,0)))).2
include u
lemma carV(j:J)(i:Ξ): e (p.run (j,i))= q.run (p.carj q e j,i+p.caret q e j):= by
 induction i using Fin.induction with
 | zero=> simp [carj,caret]
 | succ i ih=> rw [← advanceOne i, p.same, u, ih, show i.castSucc+1+p.caret q e j=i.castSucc+p.caret q e j+1 from by abel,q.same]
lemma cavalSymm(x):e.symm (σ x)=τ (e.symm x):=e.injective (by simp [u])
lemma canon(j:J): q.carj p e.symm (p.carj q e j)=j:=by
 have h:= p.run.injective ((q.carV p e.symm (cavalSymm e u) (p.carj q e j) (0+p.caret q e j)).symm.trans (by rw [←carV p q e u]; exact e.symm_apply_apply (p.run (j,0)))); exact Prod.mk.inj h|>.1
lemma cTurn(x:L→ℙ): p.carriage (x ∘ e)=q.carriage x:=by
 let E:J ≃ J':= ⟨p.carj q e,q.carj p e.symm,p.canon q e u,q.canon p e.symm (cavalSymm e u)⟩; unfold carriage; refine Fintype.prod_equiv E _ _ fun j=>?_ ; simp_rw [Function.comp_apply,p.carV q e u]; exact Wtrans (fun i=>x (q.run (E j,i))) (p.caret q e j)
end
end Car
end YM.CF.VolumeCape.Paint
