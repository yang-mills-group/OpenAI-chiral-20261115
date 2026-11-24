import YM.SU5.WakeFields.Flood
import YM.SU5.Exchange.Seed.Marks

/-! # Divide ticket lists at a lower-step recharge
    Each pose contributes EITHER its previous procedure, OR its new physical Mark at that step. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.Mew
open Function Filter NormedSpace Finset Topology MeasureTheory Fock Liss
open scoped Topology Classical BigOperators Matrix.Norms.L2Operator
variable {I E F A : Type*}

/-- Sum over assignments of a pose to the old OR the new program. Preserves order in each leg. -/
def puzzleRecharge [Add E] (W : List I→ List I→ E) : List I→E
 | [] => W [] []
 | i::l => puzzleRecharge (fun x y=> W (i::x) y) l + puzzleRecharge (fun x y=> W x (i::y)) l
lemma puzzleRechargeExt [Add E] (W U : List I→List I→ E) (l : List I) (p : ∀ x y:List I,x.Sublist l→y.Sublist l→ W x y=U x y) :
    puzzleRecharge W l= puzzleRecharge U l := by
 induction l generalizing W U with
 | nil => exact p _ _ (List.Sublist.refl _) (List.Sublist.refl _)
 | cons i l ih =>
    unfold puzzleRecharge; exact congrArg₂ (·+·)
       (ih _ _ (fun x y h v=> p _ _ (List.cons_sublist_cons.mpr h) (List.sublist_cons_of_sublist _ v)))
       (ih _ _ (fun x y h v=> p _ _ (List.sublist_cons_of_sublist _ h) (List.cons_sublist_cons.mpr v)))

variable [Fintype I] [LinearOrder I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]

lemma beam_on (V : E →L[ℂ] F →L[ℂ] A) (f : Key I→ E) (g : Key I→ F) (p : River f) (q : River g) (l : List I) (t:l.Nodup):
    tipI (fun z=>V (f z) (g z)) l=puzzleRecharge (fun x y=>V (tipI f x) (tipI g y)) l := by
 induction l generalizing f g with
 | nil=> rfl
 | cons i l ih=>
    obtain ⟨h,b⟩:=List.nodup_cons.mp t
    rw [beam_tip V p q, ih (cutI f i) (g ∘dune i) (p.flow i) (q.stay i) b, ih (f ∘dune i) (cutI g i) (p.stay i) (q.flow i) b, puzzleRecharge]; refine congrArg₂ (·+·) (puzzleRechargeExt _ _ l ?_) (puzzleRechargeExt _ _ l ?_)
    · intro x y v w; exact congrArg (fun j=> V (tipI f (i::x)) j) (tip_V i y (fun p=>h (w.subset p)))
    intro x y v w; exact congrArg (fun t=>V t (tipI g (i::y))) (tip_V i x (fun p=>h (v.subset p)))

variable {N : Type*} [Fintype N] [LinearOrder N]
attribute [local instance] opCStarAlgebra
abbrev readerAction (N : Type*) [Fintype N] [LinearOrder N] : FC N →L[ℂ] Wave N →L[ℂ] Wave N := LinearMap.toContinuousLinearMap {
    toFun:= fun z=> acts z, map_add':= fun x y=> map_add (Matrix.toEuclideanCLM (n:=Finset N) (𝕜:=ℂ)) x y, map_smul':= fun x y=>map_smul (Matrix.toEuclideanCLM (n:=Finset N) (𝕜:=ℂ)) x y }

abbrev poseBeam (D : I→ FC N) (c : ℕ) (z:Key I) : FC N := ∑ i∈range (c+1),Liss.paper D i z
lemma beam_r (D:I→FC N)(c:ℕ) : River (poseBeam D c) := (tip_bank _ (fun i z=> Liss.paper D i z) (fun i _=> (paperH D i).riv)).1
lemma poseBeamTip (D:I→ FC N)(c:ℕ)(l:List I)(p:l.length ≤ c)(v:l.Nodup)(h:l.Pairwise (fun i j=> Commute (D i) (D j))) :
    tipI (poseBeam D c) l=(l.map D).prod := by
 unfold poseBeam; rw [(tip_bank (range (c+1)) (paper D) (fun i _=>(paperH D i).riv)).2, sum_eq_single_of_mem l.length (mem_range.mpr (Nat.lt_succ_of_le p)), Liss.paperTip D l v h]
 intro b u e; exact (Liss.paperH D b).skip l (Ne.symm e)

lemma legRecharge (f:Key I→ Wave N)(p : River f)(D:I→FC N)(c:ℕ)(l:List I)(g:l.length ≤ c)(v:l.Nodup)(h:l.Pairwise (fun i j=> Commute (D i) (D j))):
    tipI (fun z=>∑ k∈range (c+1),acts (Liss.paper D k z) (f z)) l=
        puzzleRecharge (fun x y=> acts (x.map D).prod (tipI f y)) l := by
 have he(z): ∑ k∈range (c+1),acts (Liss.paper D k z) (f z)=readerAction N (poseBeam D c z) (f z):=
    (show acts (poseBeam D c z) (f z)=_ from act_sum ..).symm
 rw [funext he,beam_on (readerAction N) (poseBeam D c) f (beam_r D c) p l v]; refine puzzleRechargeExt _ _ l (fun x y t _=>?_)
 rw [poseBeamTip D c x (t.length_le.trans g) (t.nodup v) (h.sublist t)] -- lhs beta?
 rfl
end YM.CF.Mew
#print axioms YM.CF.Mew.legRecharge
