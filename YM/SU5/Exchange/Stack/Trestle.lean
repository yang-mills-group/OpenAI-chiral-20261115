import YM.SU5.Exchange.Stack.Louvre
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v s t:ℝ}{l q:ℕ}{p:BudgetPoint}
local notation "Ω"=> Single N
open Sault Leaf
-- Match physical coupon BEFORE EXP! All exc waves, even off-shell junk, not
-- asserting state readings until next Tape on actual measure.
structure JointJ (P W Q:Op (Single N)) (M:FC (Single N)) (J:FC (Dwell N)):Prop where -- Q reserved tag? delete
 rank: Leaf.rank2 J
 sends (h:IsStarProjection P)(u:Wave (Single N))(v:Sea P u)(Y:Wave (Dwell N)): let x:= acts (exp (dg (capT P W))) u; let Bu:=Sault.ballL (nursery P h) x
    acts M (Bu Y)= Bu (acts J Y)
namespace JointJ
variable {P W Q:Op (Single N)}{M M':FC (Single N)}{J J':FC (Dwell N)}
lemma nil :JointJ P W Q 0 0:=⟨fun x y z=> by simp [bump],fun h x v Y => by simp_rw [act_zero,map_zero]⟩ -- tune
lemma rime (f:JointJ P W Q M J)(g:JointJ P W Q M' J'):JointJ P W Q (M+M') (J+J'):=by
 refine ⟨Leaf.σX J J' f.rank g.rank,?_⟩; intro h u v Y; dsimp only; rw [act_add,show acts M _= _ from f.sends h u v Y,show acts M' _= _ from g.sends h u v Y,act_add, map_add] -- tune let
lemma dec (f:JointJ P W Q M J)(g:JointJ P W Q M' J'):JointJ P W Q (M-M') (J-J'):=by
 refine ⟨Leaf.θX J J' f.rank g.rank,?_⟩; intro h u v Y; dsimp only; rw [act_sub,show acts M _= _ from f.sends h u v Y,show acts M' _= _ from g.sends h u v Y,act_sub, map_sub]
lemma scale (f:JointJ P W Q M J)(t:ℂ):JointJ P W Q (t • M) (t • J):=by
 refine ⟨Leaf.ψX _ J f.rank,?_⟩; intro h u v Y; dsimp only; rw [act_smul,show acts M _= _ from f.sends h u v Y,act_smul,map_smul]
lemma minus (f:JointJ P W Q M J):JointJ P W Q (-M) (-J):=by simpa only [neg_one_smul] using f.scale (-1)
end JointJ
-- operator.Pig.Test firing pair, bundle arbitrary.B. until chop, mask-independent Juve
abbrev phy (N:Side):= Orbit N→ FC (Single N)
structure Fence (P W:SOp N)(K:Scree.Loom N)(p:BudgetPoint)(q l:ℕ)(o:Seat N)(h s:ℝ)(V:phy N)(a b:ℝ):Prop where
    stock:∃ J:Firing N,Plasma p q (grooveB l p o) h s J a b ∧ ∀ x:Orbit N,JointJ (P (profile (K x))) (W (profile (K x))) 0 (V x) (J x)
namespace Fence
variable {P W:SOp N}{K:Scree.Loom N}{V M:phy N}{h:ℝ}
lemma zeroJ:Fence P W K p q l o h s 0 0 0:=⟨0,Plasma.null,fun x=> JointJ.nil⟩
lemma arc(f:Fence P W K p q l o h s V a b)(g:Fence P W K p q l o h s M c d):Fence P W K p q l o h s (V+M) (a+c) (b+d):=by obtain ⟨X,A,H⟩:=f.stock; obtain ⟨Y,B,G⟩:=g.stock; exact ⟨_,A.arc B,fun i=>(H i).rime (G i)⟩
lemma sub(f:Fence P W K p q l o h s V a b)(g:Fence P W K p q l o h s M c d):Fence P W K p q l o h s (V-M) (a+c) (b+d):=by obtain ⟨X,A,H⟩:=f.stock; obtain ⟨Y,B,G⟩:=g.stock; exact ⟨_,A.subW B,fun i=>(H i).dec (G i)⟩
lemma scale(f:Fence P W K p q l o h s V a b)(y:ℂ):Fence P W K p q l o h s (y • V) (‖y‖*a) (‖y‖*b):=by obtain ⟨X,A,H⟩:=f.stock; exact ⟨_,A.scale y,fun i=>(H i).scale y⟩
lemma smaller(f:Fence P W K p q l o h s V a b)(hx:c≥a)(hy:d≥b):Fence P W K p q l o h s V c d:=by obtain ⟨X,A,H⟩:=f.stock; exact ⟨X,A.dropW hx hy,H⟩ -- tune choose no underscore
end Fence
abbrev firePlate (K:Scree.Loom N)(F:SOp N):phy N:=fun x=> dg (F (profile (K x)))
abbrev blazePlate (K:Scree.Loom N)(F:SOp N):phy N:=fun x=> Matrix.trace (F (profile (K x))) • 1
variable {P W A Q:SOp N}{K:Scree.Loom N} (r:ℝ) (h:ℝ) (T:DockPulse p K t d a h s l q) (u:Solo a b P d) (vQ:Solo a b W d)
local notation "S"=> grooveB l p o
local notation "L"=> roller T.pos T.roof
local notation "Y💫"=> reefCost l p s h
include T
lemma glowTrace (f:Soak o Q a v d):Fence P W K p q l o h s (blazePlate K Q) (reefCost l p s h*v) (reefCost l p s h*v):=by
 let A:=Mortgage T true Q f _ _ (oreV h T.high N) (by simp); refine ⟨_,A,?_⟩; intro x
 let X:= Q (profile (K x)); refine ⟨Leaf.ψX _ _ (Leaf.ρX),?_⟩; intro p u v Y
 unfold blazePlate; dsimp only; rw [act_smul,act_smul,act_one,act_one,map_smul]; rfl -- tune beta
-- untruncated dΓ generic for stencil family. one binder W corresponds AIM.T not cap.
variable (f:Soak o Q a v d)
abbrev feeSprig (a b:ℝ):ℝ:= Real.exp a+feeRise a b
-- formal valuation at Flow Z0: (1-C)_ω
abbrev levPrice(a b v:ℝ):ℝ:=2*((2*(feeSprig a b*v))*feeSprig a b)
abbrev vessel(P W Q:Op Ω):= let C:= capT P W;(1-C)*Q*(1+C)
local notation "I🌠"=> levPrice a b
abbrev treeEarnings(l:ℕ)(p:BudgetPoint)(s h a b:ℝ): ℝ:= let T:= reefCost l p s h; let l:=levPrice a b 1; let W:=2*(b*l); let V:=2*(l*(Real.exp a+b)); T*l+T*V+(T*W+T*W)+T*(2*(W*(Real.exp a+b)))
include f u vQ
lemma trimQ : Fence P W K p q l o h s (firePlate K Q) (treeEarnings l p s h a b*v) (treeEarnings l p s h a b*v):=by
 let D:= fun x:Chin N=>1-P x; let E:= fee_Ξ u vQ T.hint.le
 have h1: Solo a (Real.exp a) (fun _:Chin N=>(1:Op Ω)) d:= Crown.ident ..
 have hD:Solo a (Real.exp a+b) D d:=h1.sub u
 let F(x):=vessel (P x) (W x) (Q x); have hp:Soak o F a (levPrice a b v) d:=aura_X (aura_Y f (show Solo a _ (fun x=> 1-sunA P W x) _ from h1.sub E) T.hint.le) (show Solo a _ (fun x=>1+sunA P W x) _ from h1.plus E) T.hint.le -- tune'_'
 let H:= aura_Y hp u T.hint.le; let w:=aura_X hp hD T.hint.le; let V:=aura_X H hD T.hint.le
 let Hu:= Mortgage T true F hp _ _ (pal_v h T.high) (by simp); let Qp:= Mortgage T true _ H _ _ (tail_k h T.high) (by simp); let X:= Mortgage T true _ H _ _ (oreV h T.high N) (by simp); let Hv:= Mortgage T true _ w _ _ (leg_k h T.high) (by simp); let Hw:= Mortgage T true _ V _ _ (less_k h T.high) (by simp)
 let R:= fun x:Orbit N=> let M:=F (profile (K x)); let Y:= P (profile (K x)); Sault.forge (Y*M) M (M*(1-Y)) (Y*M) (Y*M*(1-Y))
 have hx:= (((Hu.arc Hv).arc (X.arc Qp)).arc Hw)
 refine ⟨R,?_,?_⟩
 · let y:=levPrice a b v; let G:=2*(b*y); let U:=2*(y*(Real.exp a+b)); let T:=2*(G*(Real.exp a+b)) -- shadows
   let Z:=reefCost l p s h; let u':=Z*y+Z*U+(Z*G+Z*G)+Z*T
   change Plasma p q _ h s _ u' u' at hx -- tune `?Q`
   rw [show treeEarnings l p s h a b*v=u' from ?_]; swap; · unfold u' U G T Z y treeEarnings levPrice; ring
   convert hx using 1
   funext i; unfold R; rw [Sault.forkL]; rfl
 intro x; let U:=P (profile (K x)); let J:=W (profile (K x)); let Y:=Q (profile (K x)); refine ⟨Leaf.ore2 _ _ _ _ _,?_⟩; intro p u v Z; unfold firePlate; have hp:= Sault.plume p (capT U J) 0 (Thera.tag_g J p) u v Z Y; -- remove 0 terms.
 dsimp only at hp; rw [zero_mul,Matrix.trace_zero,zero_smul,sub_zero,sub_zero] at hp; exact hp.symm
omit f
lemma spinPlasma (x: Op Ω)(f:Soak o (fun _=>x) a v d): let T:= payΩ a b v; let V:=reefCost l p s h; Fence P W K p q l o h s (fun U=>kerLocal (P (profile (K U))) (tickA N) x (W (profile (K U)))) (V*(2*(T*(Real.exp a+b)))+V*(2*(b*T))) 0:=by
 let T0:=payΩ a b v; intro Y X; let D(U):=blockD (P U) x
 have hp:= blockE u vQ T.hint.le x f; let H:=aura_Y hp u T.hint.le; let B:= fun v:Chin N=>1-P v; let A: Solo a (Real.exp a+b) B d:= (Crown.ident (badge _) (bail N d) a).sub u; let U:=aura_X hp A T.hint.le
 let F:= Mortgage T false _ H _ _ (tail_k h T.high) fun _ y=> Sault.urn_stop ..; let G:= Mortgage T false _ U _ _ (leg_k h T.high) fun _ y=> Sault.urn_stop ..
 let J:=fun v:Orbit N=>derail (P (profile (K v))) x; refine ⟨-J,?_,?_⟩
 · have hp:Plasma p q (grooveB l p o) h s J (X*(2*(Y*(Real.exp a+b)))+X*(2*(b*Y))) 0:=by
       have he:= G.arc F; let J' (z:Orbit N):=let v:=(P (profile (K z))); let D:=blockD v x; Sault.crib true (D*(1-v))+Sault.crib false (v*D)
       rw [show J=J' from ?_]; swap; · funext v; unfold J J' derail Sault.crib; simp only [gritz, Sault.urn_neg,sub_eq_add_neg]; rfl
       exact zero_add (0:ℝ) ▸ (show Plasma p q (grooveB l p o) h s J' _ (0+0) from he) -- rw 0 maybe
   exact hp.minus
 intro U; refine ⟨?_,?_⟩; · rw [Pi.neg_apply,←neg_one_smul ℂ]; exact Leaf.ψX _ _ (rank2Rail _ _)
 intro h v p Y
 dsimp only; exact voidPlume _ _ _ _ h v p Y -- tune implicit
end YM.CF.Swell
