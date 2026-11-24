import YM.CF.DPress.FD.Warp.Port
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row Wilson
open Cube (More assembly)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
abbrev fromE(i:reach n):Now n:=(i.1,i.1+step i.2)
lemma twin_ne(h: 1<(More n).val) (i:reach n):i.1≠ i.1+step i.2:=by
 have hp:1≠(0: Per (More n)):=by letI : NeZero ((More n).val-1):= ⟨by omega⟩; intro p; have q:= congrArg (ZMod.val) p; rw [ZMod.val_one'' h.ne', ZMod.val_zero] at q; omega -- tune
 intro v; have he:= congrFun (show (step i.2: Seat n)=0 from add_eq_left.mp v.symm) i.2; rw [step_apply,if_pos rfl] at he; exact hp he
lemma fromV(s:Sweep n)(e:reach n): fromE (lane s e)= let x:=(boxA s e.1,boxA s (e.1+step e.2)); if s.s.flip e.2 then x.swap else x :=by
 let x:=boxA s e.1; have he:boxA s (e.1+step e.2)= x+((posDir e.2).rotate s.s).vec:= salt (N:=n) (castX s) (posDir e.2) e.1
 rw [he]; dsimp only; unfold lane x; cases h:s.s.flip e.2 <;> simp [fromE,sitA,sendEdge,Step.used, Step.rotate,posDir,h,Step.vec,sub_eq_add_neg] -- tune
variable {a:ℝ}{T:Trophy n l u} {I:Type*}[Fintype I] {V:Vision (More n) r I} (U:Plan V l m)(P:Leader T m 5 a)(Q:Valve n (rate a/(m:ℝ)))
variable (x:I) (η μ:Cotton n)(X:Pane n){i j:Seat n}
def hand(x:I)(η:Cotton n)(X:Pane n)(i:Now n): E:=Q.F η i (realF U P x η X i.1,realF U P x η X i.2)
lemma hand_s(s:Sweep n)(i j:Seat n): hand U P Q (moveK U s x) (act s η) (flashA s X) (i,j)=polarT s.charge (hand U P Q x η X (boxA s i,boxA s j)):=by
 unfold hand; dsimp only; rw [real_s,real_s]; let V:=(boxA s i,boxA s j); have he:(i,j)=(bothP n).mv s V:=Prod.ext ((boxA s).symm_apply_apply i).symm ((boxA s).symm_apply_apply j).symm; rw [he]; exact Q.pol s V η (realF U P x η X V.1, realF U P x η X V.2) -- tune rw pair
lemma hand_v(z: Now n)(t:z.1≠z.2): hand U P Q x η X z= (hand U P Q x η X z.swap)⁻¹:=Q.rev _ _ z t
local notation "F"=> hand U P Q
abbrev mild (U:Plan V l m)(u:ℝ)(x:I)(X:Pane n)(i:Now n):Prop:= Grade l u X (pat U x i.1)∧ Grade l u X (pat U x i.2)
def flow(x:I)(η:Cotton n)(X:Pane n):Pane n:=fun e=> if mild U u x X (fromE e) then X e else hand U P Q x η X (fromE e)
lemma flow_M : Measurable (flow U P Q x η) := measurable_pi_lambda _ fun i=> Measurable.ite ((grade_M l u _).inter (grade_M l u _)) (measurable_pi_apply _) ((Q.m_F _ _).comp ((real_M ..).prodMk (real_M ..))) -- tune
lemma flow_K (h:1<(More n).val)(s:Sweep n) :flow U P Q (moveK U s x) (act s η) (flashA s X) = flashA s (flow U P Q x η X):=by
 funext i; rw [flash]; let B:=boxA s i.1; let D:=boxA s (i.1+step i.2); let z:=moveK U s x; let e:= lane s i; have hz:mild U u z (flashA s X) (fromE i)=mild U u x X (fromE e):=by
    have hv(i:Seat n):Grade l u (flashA s X) (pat U z i)= Grade l u X (pat U x (boxA s i)):= by unfold z; rw [pat_s,grade_u,ζ_rev]
    unfold mild e; rw [hv,hv,fromV]; dsimp only; split; next t=> exact propext and_comm
    rfl
 unfold flow; split
 next t=> simp only [if_pos (show mild U u x X (fromE (lane s i)) from hz ▸ t)]; exact flash s X i
 next t=>
   let u : ¬ mild U u x X (fromE (lane s i)):=hz ▸ t; simp only [if_neg u]; have ht:=hand_v U P Q x η X (B,D) (show B≠ D from fun p=> twin_ne h i ((boxA s).injective p))
   rw [show fromE i=(i.1,i.1+step i.2) from rfl,hand_s,fromV]; dsimp only; split; exact congrArg (polarT s.charge) ht; rfl
lemma flow_est (t:0<m)(v:baseP≤ a)(p:0<l)(hu:0≤u)(κ:Treasure l m u)(i:reach n): dist (sail (realF U P x η X i.1) (flow U P Q x η X i)) (realF U P x η X (fromE i).2) ≤ rate a/(m:ℝ):=by
 obtain ⟨i,l⟩:=i; unfold flow; split; next h=> exact premium U P x η X v p t hu κ h.1 h.2
 next h=> exact Q.bill η (fromE (i,l)) (realF U P x η X i,realF U P x η X (i+step l)) (real_pair U P x η X v t hu κ (Work.E01.sep_step_le i l)) -- maybe nondefeq
end Turf
end YM.CF.DPress.FD
