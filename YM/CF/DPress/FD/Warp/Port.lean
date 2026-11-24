import YM.CF.DPress.FD.Warp.Trap
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
abbrev bothF {I J:Type*}(P:Tw n I)(Q:Tw n J): Tw n (I×J):=⟨fun i x=>(P.mv i x.1, Q.mv i x.2),funext fun i=>by rw [P.one,Q.one]; rfl,fun a b x=>by rw [P.pair,Q.pair]⟩ -- tune
abbrev Now(n:Side) := Seat n × Seat n
abbrev PushP(n:Side) := rug n × rug n
lemma dist_duo (x:E)(B C:rug n) : dist (sail B x) C=dist (sail C x⁻¹) B:=by rw [←Frame.sail_L (sail C x⁻¹) B x,sail_mul,inv_mul_cancel,sail_id,dist_comm] -- tune
private lemma repair (u:ℝ): ∃ F:PushP n→E, Measurable F∧ ∀ (s:PushP n), Frame.Fits u s.1 s.2→ dist (sail s.1 (F s)) s.2 ≤ u:=by
 obtain ⟨g,h,v⟩:= BPress.choose_if_closed (X:=PushP n) (Y:=E) {x|dist (sail x.1.1 x.2) x.1.2 ≤ u} (isClosed_le (by unfold sail; fun_prop) continuous_const)
 exact ⟨g,h,v⟩
private def sto (g:PushP n→E)(i:Now n)(v:PushP n): E:= if Fintype.equivFin (Seat n) i.1< Fintype.equivFin (Seat n) i.2 then g v else (g v.swap)⁻¹ -- diag solution no uses
private lemma sto_P(g:PushP n→E)(i j:Seat n)(h:i≠j)(A:PushP n): sto g (i,j) A=(sto g (j,i) A.swap)⁻¹:=by
 unfold sto; dsimp only; rcases lt_or_gt_of_ne (show Fintype.equivFin (Seat n) i ≠ Fintype.equivFin (Seat n) j from fun v=> h ((Fintype.equivFin _).injective v)) with h|h; rw [if_pos h,if_neg (not_lt_of_ge h.le),inv_inv]; rfl
 rw [if_pos h,if_neg (not_lt_of_ge h.le)]
private lemma sto_t(g:PushP n→E)(p:∀ s,Frame.Fits u s.1 s.2→ dist (sail s.1 (g s)) s.2≤ u)(i:Now n)(s:PushP n)(v:Frame.Fits u s.1 s.2): dist (sail s.1 (sto g i s)) s.2 ≤ u:=by unfold sto; split; exact p s v; next t=> rw [dist_duo,inv_inv]; exact p s.swap (Frame.transpose v)
abbrev pairU(i:Now n):Support (More n):= {i.1,i.2}
abbrev bothP(n:Side):Tw n (Now n):= bothF (pos n) (pos n)
abbrev bothK(n:Side):Tw n (PushP n):=bothF (chart n) (chart n)
lemma turn_pair (s:Sweep n)(x:Now n): pairU ((bothP n).mv s x)= ζ s⁻¹ (pairU x):=by rw [pairU,pairU,ζ,map_insert,map_singleton,sitU]; rfl
structure Valve (n:Side)(u:ℝ) where
 F : Cotton n → Now n → PushP n → E
 m_F : ∀ c i, Measurable (F c i)
 bill : ∀ c i x, Frame.Fits u x.1 x.2 → dist (sail x.1 (F c i x)) x.2 ≤ u
 pol : ∀ s i c x, F (act s c) ((bothP n).mv s i) ((bothK n).mv s x)= polarT s.charge (F c i x)
 rev : ∀ x c i, i.1 ≠ i.2 → F c i x=(F c i.swap x.swap)⁻¹
 read : ∀ c d i,c (pairU i)=d (pairU i)→ F c i=F d i
lemma vents : Nonempty (Valve n u):=by
 obtain ⟨g,h,v⟩:=repair (n:=n) u; let f(η:Cotton n)(i:Now n):=tune (bothK n) (lyng n) (sto g) (bothP n) (η (pairU i)) i; have hz (i):Measurable (sto g i):=by
    by_cases w:Fintype.equivFin (Seat n) i.1< Fintype.equivFin (Seat n) i.2; swap; · rw [show sto g i=(fun x=> (g x.swap)⁻¹) from funext (fun x=> if_neg w)]; exact (h.comp measurable_swap).inv
    rw [show sto g i=g from funext (fun i=> if_pos w)]; exact h
 refine ⟨⟨f,?_, ?_,fun s i c x=> tune_v (bothK n) (lyng n) s c (bothP n) i pairU (turn_pair s) x (sto g),?_,fun c d i v=>by unfold f; rw [v]⟩⟩
 · intro c i; let s:=c (pairU i); have ht:Measurable ((chart n).mv s):= (by apply Continuous.measurable; exact (neat s).continuous); exact (rev_C s⁻¹.charge).measurable.comp ((hz ((bothP n).mv s i)).comp ((ht.comp measurable_fst).prodMk (ht.comp measurable_snd)))
 · intro c i x p; let s:=c (pairU i); let V:=chart n; let A:=(bothP n).mv s i; let Y:=(bothK n).mv s x; let k:= sto g A Y; change dist (sail _ (polarT s⁻¹.charge k)) _≤ u; have hg: (bothK n).mv s⁻¹ Y=x:=(bothK n).vert s x; nth_rw 1 [←hg]; -- also rhs
   -- use Eq from congrArg... inspect
   rw [show ((bothK n).mv s⁻¹ Y).1=Tw.Ω s⁻¹ Y.1 from rfl,←sailX]; conv_lhs => rhs; rw [←hg];
   exact ((neat s⁻¹).dist_eq _ _).trans_le (sto_t g v A Y (fitX s p))
 rintro x c ⟨i,j⟩ y; unfold f tune; rw [show pairU (i,j)=pairU (j,i) from Finset.pair_comm ..]; let s:=c (pairU (j,i)); let D:= (pos n).mv s; let P:=(bothK n).mv s x; change polarT s⁻¹.charge (sto g (D i,D j) P) = (polarT _ (sto g (D j,D i) P.swap))⁻¹; rw [sto_P g _ _ (show D i≠ D j from fun p=> y ((e (pos n) s).injective p)),map_inv]; rfl
end Turf
end YM.CF.DPress.FD
