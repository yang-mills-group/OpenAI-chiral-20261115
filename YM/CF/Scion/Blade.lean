import YM.CF.Scion.Mallet
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel

open Cour Acorn Atala Reef MeasureTheory Jet
variable {N B:Side} (D e:ℝ) (J:Pride (mid N B)) (X Y:Seal (Site (Domain N B)))
variable (V:Tints N B e)
variable (s: Sweep (mid N B))(x:Castle N B e X)(A:Ids (mid N B))(u:Seat (mid N B)→SU.E)
lemma stampU(h:X.Nonempty)(p:Injective (priorP A)): strokeC e (actS s X) (actS s Y) V (bun s A) (pullT s x) = cSignX (Hive.χ s) (strokeC e X Y V A x):=by
 let U:=actS s X; let W:=bun s A; let k:=Hive.chip X A; let t:=Hive.chip U W; have he: s*t=k:=by unfold t W U; rw [chipA X h A p, mul_inv_cancel_left];
 let v₀:= strideH X A x; let v₁:=strideH U W (pullT s x); have hh(i): actS t (actS s i)=actS k i:=by rw [←actG_s,he]
 have ht:v₁.val=v₀.val:=by funext i; change flashA t (Lattice.gauge (frameP W) (flashA s (x.val i)))=flashA k (gauge (frameP A) (x.val i)); unfold W; rw [boong, lights,he];
 change cSignX _ (V (actS t U) (actS t (actS s Y)) v₁) = cSignX (Hive.χ s) (cSignX (Hive.χ k) (V (actS k X) (actS k Y) v₀))
 have hy{R T:Seal (Seat (mid N B))}(x:Castle N B e R)(u:Castle N B e T)(h:R=T)(g:x.val=u.val)(c:Seal (Seat (mid N B))):V R c x=V T c u:=by subst T; rw [Subtype.ext g]; -- tune
 rw [hy v₁ v₀ (hh _) ht _, hh]; let Z:= V (actS k X) (actS k Y) v₀
 change cSignX (Hive.χ t) Z= cSignX (Hive.χ s) (cSignX (Hive.χ k) Z); have hz:Hive.χ k=(Hive.χ s).xor (Hive.χ t):=by rw [←he]; unfold Hive.χ; rw [show (s*t).charge=s.charge.xor t.charge from rfl,show (s*t).s=s.s*t.s from rfl,det_p]; cases hp:s.charge <;> cases hq:t.charge <;> cases hz:detX s.s <;> cases hy:detX t.s <;> rfl
 rw [hz]; cases hp:Hive.χ s <;> cases hr:Hive.χ t <;>simp [cSignX] -- tune
lemma stepC : strokeC e X Y V (threadG u A) (pullF X u x)=strokeC e X Y V A x:=by
 let A':= threadG u A; have hp:strideH X A' (pullF X u x)=strideH X A x:=by
    apply Subtype.ext; funext i; change flashA (Hive.chip X A') (gauge (frameP A') (gauge u (x.val i)))=_; rw [Skye.gauge_sq,show frameP A' * u= frameP A from ?_]; rfl; funext i; simp [A',frameP,threadG]
 change cSignX _ (V _ _ (strideH X A' (pullF X u x)))= _; exact congrArg _ (congrArg _ hp) -- tune
lemma earned_s(K:ℝ)(j:ℕ)(b d:ℝ)(h:Dyes D e J j V b d)(p:Grove (terr _) X)(G:Ids (mid N B))(w:∀ s,ShiftD j K D e X G s):∃ f: Seal (Seat (mid N B))→ℝ,(∀ Y, Pro (landX j K X e) Y (strokeC e X Y V G) (f Y) ∧ (f Y≠0 → X⊆Y))∧ ∑ Y, Acorn.cost b X Y*f Y ≤Real.exp (d*X.card):=by
 let t:=Hive.chip X G
 obtain ⟨C,q,l,z⟩:=h.arch _ (grove_t _ t p); refine ⟨C ∘ actS t, fun Y=>?_,?_⟩
 · have hv:= q (actS t Y); have hl:= pSign (Hive.χ t) _ (ferry G t (w t) hv.1); rw [actG_l] at hl -- dependent Q val?
   exact ⟨hl,fun u=>Finset.map_subset_map.mp (hv.2 u)⟩
 rw [show (∑ Y, Acorn.cost b X Y*(C∘actS t) Y) = (∑ Y, Acorn.cost b (actS t X) Y*C Y) from ?_]; swap
 · let U:Seal (Seat (mid N B))≃Seal (Seat (mid N B)):=Equiv.ofBijective (actS t) ((Finite.injective_iff_bijective).mp (actG_in _))
   apply Fintype.sum_equiv U _ _; intro i; exact congrArg (· * C (actS t i)) (show Acorn.cost b X i=Acorn.cost b (actS t X) (actS t i) by simp [Acorn.cost,Branch.rent, actS,←Finset.map_sdiff])
 rw [←show (actS t X).card=X.card from Finset.card_map _]
 exact l
end YM.CF.Scion
