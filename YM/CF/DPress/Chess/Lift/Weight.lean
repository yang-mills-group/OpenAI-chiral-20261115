import YM.CF.DPress.Chess.Lift.Gamma
import YM.CF.Scree.Locus
/- `plankP` is plus Q/2, minus -Q/2; use exact exp forms without reducing away the support projector. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson Fock Fixed NormedSpace Spire Scree Skye Tap
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}(Q:Op Slot)
def peak (n:Side)(Q:Op Slot): Op (Single n):= exp (plankP n Q)
def pit (n:Side)(Q:Op Slot): Op (Single n):=exp (-(plankP n Q))
lemma careZ (Z:Op (Single n))(p:Commute Z (plankP n Q)): Commute Z (peak n Q) ∧ Commute Z (pit n Q):=by letI : NormedAlgebra ℚ (Op (Single n)):= NormedAlgebra.restrictScalars ℚ ℂ _; exact ⟨p.exp_right,p.neg_right.exp_right⟩
lemma peekU : Commute (tickA n) (peak n Q):= (careZ Q (tickA _) (plank_tick _)).1
lemma peekL : Commute (tickA n) (pit n Q):= (careZ Q (tickA _) (plank_tick _)).2
lemma peekK (X:Support (More n)) : Commute (cutM (matterRegion n X)) (plankP n Q):=by
 unfold Commute SemiconjBy; ext i j; rw [cutM,Matrix.diagonal_mul, Matrix.mul_diagonal,plankP]; by_cases h:i.1.1=j.1.1
 · simp only [mem_matterRegion,h]; split <;> simp
 have hu:headW n (Aop-(1/2:ℂ) • 1) Q i j=0:=by rw [headW,loveAt]; exact if_neg (show (Equiv.refl _) ((helix n i).1)≠(helix n j).1 from h) -- tune
 rw [hu]; simp
-- support frame
lemma peak_W (x:Ket (Single n))(y: Phys n): acts (create x) (scaleZ Q y)=scaleZ Q (acts (create (acts (peak n Q) x)) y):=by
 let F:=pit n Q; have ht: F*peak n Q=1:= mul_eq_one_comm.mp (wind_inv (plankP n Q)); have hx: x=acts F (acts (peak n Q) x):=by rw [←act_mul,ht,act_one]
 rw [scaleZ,map_smul,show exp _=F from rfl,quant_up F x _ hx y,scaleZ]; rfl
lemma pit_W (t:star Q=Q)(x:Ket (Single n))(y:Phys n):acts (remove x) (scaleZ Q y)=scaleZ Q (acts (remove (acts (pit n Q) x)) y):=by
 let F:=pit n Q; have h:star F=F:=by unfold F pit; rw [star_exp,star_neg,Tap.plank_h t]
 rw [scaleZ,map_smul,show exp _=F from rfl,quant_down F x (acts F x) (by rw [h]), scaleZ]; rfl
-- support.Flection. `JetS a.s false true U` reflection convention. Stay at Shape level
variable {M : Shape}(b:Shape)(u: UNI SpinIdx)(v:JetS b.s false true u)
local notation "prep"=> prepU b u inert n
include v
lemma plank_ref : twist (prepU b u inert n) (plankP n Q)= -(plankP n Q):=by
 let H:= Aop-(1/2:ℂ) • 1; let A:=H⊗ₖ Q; let V:=(Equiv.refl (Site n)); let F:Op (Model n):=jump V (fun _=> A); let B:=mealU b u inert n; change sings false (prepU b u inert n) (love n F)=-love n F; rw [wingX]; suffices he:sings false B F= -F from (he ▸ map_neg ..)
 have hv: sings false u H= -H:=by
    have he: twist u Aop=1-Aop:= angleX v true; unfold H; change twist u (Aop-(1/2:ℂ) • 1)=_; rw [map_sub,twist_scalar,map_one,he]; module
 have h1:sings false inert.V Q=Q:=one_des .. -- Find
 have he(X Y:Site n):Scroll.tap F X Y = if X=Y then A else 0:=by ext i j; by_cases p:X=Y <;> simp [F,V,Scroll.tap,jump_apply,p]
 suffices h:∀ i j:Site n,Scroll.tap (sings false B F) i j= - Scroll.tap F i j by ext ⟨i,a⟩ ⟨j,k⟩; exact congrFun (congrFun (h i j) a) k
 intro x y; unfold B mealU; rw [tap_sg,he,he]; by_cases t:x=y; swap; · rw [if_neg t,if_neg ((Tofu b n).injective.ne t),win_z,mul_zero,zero_mul,neg_zero]
 subst y; simp only [ite_true]; change sings false (milU b u inert x) (H⊗ₖ Q)= -A; rw [wingM,Scroll.wingK u inert _ _, hv,h1, op_kron_neg]
omit v in
lemma act_cost {I:Type*}[Fintype I][DecidableEq I](X:UNI I)(A B:Op I)(p:twist X A=B)(x:Ket I) : acts X.val (acts A x)=acts B (acts X.val x):=by rw [←p]; exact (Fock.swivel ..)
lemma peak_flip (x:Ket (Single n)): acts (prepU b u inert n).val (acts (peak n Q) x)= acts (pit n Q) (acts (prepU b u inert n).val x):= act_cost (prepU b u inert n) _ _ (by rw [Lift.peak, breeze_exp,plank_ref Q b u v]; rfl) x -- v is binder in act_cost? name
lemma pit_flip (x:Ket (Single n)): acts (prepU b u inert n).val (acts (pit n Q) x)= acts (peak n Q) (acts (prepU b u inert n).val x):= act_cost (prepU b u inert n) _ _ (by rw [Lift.pit, breeze_exp,map_neg,plank_ref Q b u v,neg_neg]; rfl) x -- tune
end YM.CF.DPress.Chess.Lift
