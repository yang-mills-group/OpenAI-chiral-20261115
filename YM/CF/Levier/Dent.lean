import YM.CF.Levier.Tone
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
variable (S:Seal (Site (More P)))(W:Toll (Iota G))(F:Raw (cro G e) (Iota G))
local notation "κ₀"=>castX k⁻¹
local notation "π"=>paceU κ₀ G
abbrev scene (X Y: Hand G)(x y p q:QuiltF):ℂ:=let Z:= spinU (k⁻¹).charge (κ₀).s; (milU κ₀ Z (xtra (k⁻¹).charge) X.1).val x p * star ((milU κ₀ Z (xtra (k⁻¹).charge) Y.1).val y q)
def chase :Toll κ:= fun i j=>∑ p:QuiltF,∑ q:QuiltF, let X:=(abbe G i).1; let Y:=(abbe G j).1; ‖scene G k X Y (abbe G i).2 (abbe G j).2 p q‖* W (beamH G (π X) p) (beamH G (π Y) q)
def perch(d:cro G e):= toSpin G k⁻¹ (F (toWish G e k d))
lemma curb(X:Op κ)(i j:Hand G)(p q:QuiltF):toSpin G k⁻¹ X (beamH G i p) (beamH G j q)= ∑ v:QuiltF,∑ w:QuiltF, scene G k i j p q v w * cSignX k.charge (X (beamH G (π i) v) (beamH G (π j) w)):=by
 change tap ((toSpin G k⁻¹ X).submatrix (abbe G).symm (abbe G).symm) i j p q=_
 unfold toSpin steer; rw [port_back]; unfold fros; rw [tap_sg,Matrix.mul_assoc,Matrix.mul_apply]; apply sum_congr rfl; intro v _; rw [Matrix.mul_apply, Finset.mul_sum]; apply sum_congr rfl; intro w _; have he(A:Op QuiltF)(x y): windX k.charge A x y=cSignX k.charge (A x y):=by cases k.charge <;>rfl
 rw [show Sweep.charge k⁻¹=k.charge from rfl,he]; unfold scene; rw [mul_comm (cSignX ..) (star (milU _ _ _ _).val _ _),←mul_assoc]; rfl
include h
lemma pivot (u t:Bool)(p:Suite (badge _) (pinH G e u) (pinH G e t) S W F): Suite (badge _) (pinH G e u) (pinH G e t) (toRoar G k S) (chase G k W) (perch G e k F):=by
 let Y:= toSpin G k; have hx(U):Y (toSpin G k⁻¹ U)=U:=by rw [show Y _= _ from skim G h k⁻¹ k U,inv_mul_cancel, skey G h]
 refine ⟨⟨fun g d=> ?_,fun i j=> ?_⟩,?_⟩
 · let D:=wish k.charge (castX k) G e; let z:= starG k.charge (Shape.broad G (castX k)) g; have he(u:Bool):Y ((pinH G e u|>.run g).val)= ((pinH G e u|>.run z).val):= tut k.charge (castX k) G h e _ _ rfl g
   have ht: Injective Y:=by intro i j p; have hh(v:Op κ):toSpin G k⁻¹ (Y v)=v:=by unfold Y; rw [skim _ h,mul_inv_cancel,skey _ h]; -- tune
                            rw [← hh i,← hh j, p] -- tune second
   have hm (A B:Op κ): Y (A*B)=Y A*Y B:= singm ..
   apply ht; unfold perch; rw [hm,hm,hx,hx,he,he]; unfold toWish; rw [wish_cov]; exact p.frame z (D d)
 · obtain ⟨⟨X,x⟩,rfl⟩:=(abbe G).symm.surjective i; obtain ⟨⟨Z,z⟩,rfl⟩:=(abbe G).symm.surjective j
   unfold perch chase; simp_rw [Equiv.apply_symm_apply]; change Expo _ _ (beamH G X x) (beamH G Z z) _ _; simp_rw [show (abbe G).symm (X,x)=beamH G X x from rfl,show (abbe G).symm (Z,z)=beamH G Z z from rfl]; simp_rw [curb]
   exact Expo.sumK _ _ _ fun v _=> Expo.sumK _ _ _ fun w _=> (lineage G h e k X Z v w S _ _ (p.expo ..) x z).discount _
 let T(c:cro G e):= F (toWish G e k c); let V:= pflux κ₀ G (spinU (k⁻¹).charge (κ₀).s) (xtra (k⁻¹).charge); have ht:(badge (cro G e)).all fun x=> windX k.charge (T x):=fun i j=> by
    have he(w): windX k.charge (T w) i j=cSignX k.charge (T w i j):=by cases k.charge <;>rfl
    simp_rw [he]; exact looks_p k.charge (castX k) G e (fun x=> F x i j) (p.fuel i j)
 exact License.times _ (License.times (g:=fun x=>windX _ (T x)) _ (License.base _ V.val) ht) (License.base _ (star V.val)) -- tune syntactic perch formula
end YM.CF.Levier
