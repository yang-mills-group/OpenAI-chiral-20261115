import YM.CF.Hive.SealT
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye
variable {N B m L:Side}{k j:ℕ}{a b d c e H:ℝ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e} {I:Aim (CSide m B)}{M:Male}{S:Seal (Seat (CSide m B))}
local notation "N₀"=>CSide m B
private lemma twist_in(P Q: FC (Single N)):Injective (acts Q) → P=Q→True:=fun _ _=>True.intro
lemma arum_in {n:Side}(b:Bool)(s:Shape)(U: UNI SpinIdx)(p:JetS s.s b (detX s.s) U): Injective (arum (siteU s b U n) b (detX s.s) (mateK n)):=by
 let X:=siteU s b U n; let q:=mateK n; let r:=detX s.s; have hx: ‖glaze X b r q‖=1:= gazeN X b r (Tset _) (touchP n ▸ tickB n) (tickR s (xtra b) U p n)
 intro y z g; have hj: oculus X b r y=oculus X b r z:=mark_ext (c:=(glaze X b r q)⁻¹) (inv_ne_zero (norm_pos_iff.mp (by rw [hx]; exact one_pos))) g
 have h(f:Bool):Injective (fun v:Wave (Single n)=>dove f v):=by
    intro x y p; apply PiLp.ext; intro i; let g:= congrFun (congrArg (fun t=>WithLp.ofLp t) p) i; cases f; exact congrFun (congrArg (fun t=> WithLp.ofLp t) p) i; exact star_injective (congrFun (congrArg (fun t=>WithLp.ofLp t) p) i)
 have hi(u:UNI (Finset (Single n))):Injective (acts u.val):= fun i j p=>by have ht:= congrArg (acts (star u.val)) p; rw [←act_mul,←act_mul,u.property.1,act_one,act_one] at ht; exact ht
 cases k:r<;> rw [k] at hj; exact h b (hi _ hj); exact h b (h true (hi _ hj)) -- tune r dependency
lemma eff_in(f: Seat N→ E): Injective (effectK (tradew N f).val):= by intro i j p; let U:= quantU (tradew N f); change acts U.val i=acts U.val j at p; have ht:= congrArg (acts (star U.val)) p; rw [←act_mul,←act_mul,U.property.1,act_one,act_one] at ht; exact ht
lemma roll_u (A: Ids N₀)(h:Pearl P)(hp:Stamped j L o Y)(k:P.roundZ≤(N₀).val)(hv:1≤j)(w:I.toll a b d H)(hx:Reef.Cry I)(S:Seal (Seat N₀))(x:Castle m B e S) (Q: FC (Single N₀))(H:Keys Q) (p:acts Q (nest P I M ((strideH S A x).val false))= nest P I M ((strideH S A x).val true)): acts (mallC S A Q) (nest P I M (x.val false))= nest P I M (x.val true):=by
 let U:=chip S A; let R:=frameP A; let V:=tradew N₀ R; let u:=nest P I M; let t:=castX U; let c:=U.charge
 let Z:= lotB c (detX t.s) (siteU t c (spinU c t.s) N₀); let Y:=arum (siteU t c (spinU c t.s) N₀) c (detX t.s) (mateK _)
 apply eff_in R; apply arum_in c t _ (n:=N₀) (spinZ ..)
 have he(U:FC (Single N₀))(z:Wave (Single N₀)):effectK V.val (acts U z)=acts (Gaze R U) (effectK V.val z):= Fock.swivel (quantU V) U z
 change arum (siteU t c (spinU c t.s) N₀) c (detX t.s) _ (effectK _ (acts _ _))=_
 rw [he _ _]; unfold V at *; rw [salt_g h hp k hv R I w _ (x.property.1 false),salt_g h hp k hv R I w _ (x.property.1 true), arum_act,birds c h hp k hv t (spinU c t.s) (spinZ ..) I w hx _ ((x.property.1 false).cov R),birds c h hp k hv t (spinU c t.s) (spinZ ..) I w hx _ ((x.property.1 true).cov R)]
 change acts (warpC S A (mallC S A Q)) _=nest _ _ _ ((strideH S A x).val true); rw [morn S A Q H]; exact p
end YM.CF.Hive
