import YM.CF.Eire.Boot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))
variable {r v:ℕ}
variable (H W: Ride S) (p:Disjoint (Stilo.bay H) (Stilo.bay W))
section
variable {ι n m:Type*}[LinearOrder n][Fintype n][DecidableEq ι]{S T:Set (Oboe n)}
private lemma rolls (X:FC n)(P:List (Oboe n))(u:∀ i∈ P,X*bell i= -(bell i*X))(h:Nat.ModEq 2 P.length 0): Commute X (rollC bell P):=by
 induction hx:P.length using Nat.strong_induction_on generalizing P with
 | h a ih=> cases P with
            | nil=> exact Commute.one_right _
            | cons i P=> cases P with
                        | nil=> unfold Nat.ModEq at h; simp at h
                        | cons j P=>
                           have he:=u i (by simp); have ht:= u j (by simp); have hw: Nat.ModEq 2 P.length 0:= by unfold Nat.ModEq at *; simp only [List.length_cons] at h; omega
                           change Commute X (bell i*(bell j*rollC bell P)); rw [←mul_assoc]; exact (show Commute _ (bell i*bell j) from by change X*_= _*_; rw [←mul_assoc,he,neg_mul,mul_assoc,ht,mul_neg,neg_neg,←mul_assoc]).mul_right (ih _ (by simp only [List.length_cons] at hx; omega) _ (fun i v=>u i (by simp [v])) hw rfl)
lemma priceK(h:∀ i∈S,∀ j∈T, i≠ revertP j)(X Y:FC n)(p:Pitch bell S 0 X)(g:Pitch bell T 0 Y): Commute X Y:=by
 induction p with
 | null=> exact Commute.zero_left _
 | add _ _ t z=> exact t.add_left z
 | stam z _ t=> exact t.smul_left z
 | term i t l=>
    induction g with
    | null=> exact Commute.zero_right _
    | add _ _ t z=>exact t.add_right z
    | stam z _ t=> exact t.smul_right z
    | term j k q=>
       suffices he: ∀ (i: List (Oboe n)), Fit S i → Commute (rollC bell i) (rollC bell j) from he _ l
       intro i v; induction i with
       | nil=> exact Commute.one_left _
       | cons a i ih=>
          change Commute (bell a*rollC bell i) _; apply Commute.mul_left _ (ih fun x t=> v x (List.mem_cons_of_mem a t)); refine rolls _ j ?_ k; intro x g; apply eq_neg_of_add_eq_zero_left; rw [show bell a*bell x+bell x*bell a=_ from orchestra a x, if_neg (h a (v a (by simp)) x (q x g))] -- tune
end
local notation "bay"=> Stilo.bay
open Rush Scroll Paige Vault Phase Acorn Spire
variable {L:Side}{j k:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e:ℝ}{q:Grasp Y B e}{Q:Lend P B e ∅}{V: ∀ A:Support (Domain P B),Lend P B e A}{I:Laic.Aim (mid P B)}{X:Tints P B e}{M:Male}{α K K' t a d:ℝ}
lemma rolled (O: Kite S r)(h: Vista q M I V k K ((Fintype.card Play:ℝ)*t) a d)(x:Castle P B e (danceL S O.1.val r))(T:Ids (mid P B))(p:ShiftD k K' K e (danceL S O.1.val r) T (Hive.chip (danceL S O.1.val r) T))(hp:frameP S O ⊆ bay H): Pitch bell (lipF (mintK S H)) 0 (stock e (danceL S O.1.val r) X V x T O.2):=by
 unfold Scion.stock; apply Pitch.stam; rw [hols]; apply Pitch.sum; intro i _; split; swap; · exact Pitch.null
 next w=>
    let Y:= sumW _ V _ T i; have he:= (swing_a _ V _ T p (dance_g S O.1) h).1 i; apply Pitch.stam; apply Pitch.term Y.2.1 _ _
    · exact Nat.even_iff.mp he.2.2.1
    intro j t; change mint S j.2∈ bay H; have ht:node j.2.1.1∈O.2.2:= mem_singleton.mp w ▸ he.2.2.2.1 j t
    exact hp (mem_union_right _ (mem_image_of_mem S.ratio.parent (mem_union_right _ ht)))
lemma priced (d:Disjoint (Stilo.bay H) (Stilo.bay W))(X Y:FC (Single (mid P B)))(g:Pitch bell (lipF (mintK S H)) 0 X)(h:Pitch bell (lipF (mintK S W)) 0 Y): Commute X Y:=priceK (fun i h j u p=> Finset.disjoint_left.mp d ((congrArg (fun i : Oboe _=> mint S i.2) p) ▸ (show mint S i.2∈ bay H from h)) (show mint S j.2∈bay W from u)) _ _ g h
end YM.CF.Eire
