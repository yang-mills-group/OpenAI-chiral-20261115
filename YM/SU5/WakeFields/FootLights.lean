import YM.SU5.WakeFields.MirrorSites
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
open Function Filter Metric Cube Lat Lattice Satin Fock Finset MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Classical
open Py Py.Rate LocalLimit FullBill Preparation Yoke Yoke.Shuttle
open Lifted EmberWind EmberWind.Staff EmberWind.MixedCards
open Papal (household)
open Tapestry Journey Heat -- `chime`
open Jewel -- remove
attribute [local instance] opCStarAlgebra
variable {J:Type*} (L:List J) (u:J→ Cover) (D:J→MixedCards.Ticket) (P:Spine)
variable (s r n k : ℕ) (ρ A:ℝ)

local notation "z" => (3:Axis)
local notation "Z" => P.calibration
local notation "θ" => (P.reflectTest 3)
local notation "F" i:max => (adjacent i Resolving.primary Spine.pairMood)
-- small dossier for all such locations.
def litProgram : Family Z := stampL P s r A ρ (fun i=> adjacent (u i) primary Spine.pairMood) D L -- order s r rho A
abbrev paperX : Finset Cover:= (L.map (fun i=> skyDeck (nodeC (u i)) (r+8))).foldr (·∪·) ∅
lemma paperBook (p:4≤r) : InTest Z true (paperX L u r) false (litProgram L u D P s r ρ A) ∧ CovCover Z (litProgram L u D P s r ρ A):= by
  induction L with
  | nil => exact ⟨.one,covariant_one _⟩
  | cons i L ih=>
    let F':=F (u i); let V(x):= household Z (scoreActor P s r A ρ (F (u i)) x)
    let S:= skyDeck (nodeC (u i)) (r+8)
    have a: F'.Pays r 0:= compRoom _ _ _ p; -- tune last argument p
    have hv (x : MixedCards.Ticket): InTest Z true S false (V x) ∧ CovCover Z (V x):=by
      cases x
      · exact ⟨.smul ((sPow P.par s A:ℂ)^5) (letterBudget F' ρ _ _ a),covariant_scale _ (Staff.registration F' _ _ _ a) _⟩
      rename_i b; let H:= matter_voice F' b; let y:Finset Cover:={F'.xo}; have he:y⊆S:= singleton_subset_iff.mpr (owns _ _);
      have h : InTest Z false y false (household Z (matter F' b)) := H.1.narrow _
      exact ⟨.smul ((sPow P.par s A:ℂ)^3) (h.widen.mono he), covariant_scale Z (A:=household Z (matter F' b)) (fun i=> H.2 _) _⟩
    exact ⟨((hv (D i)).1.mono subset_union_left).mul (ih.1.mono subset_union_right), (covariant_parts _ (hv _).2 ih.2).2⟩

lemma litReflect (x:Cover)(t:MixedCards.Ticket) (q:ℤ) : mirror Z 3 q (household Z (scoreActor P s r A ρ (F x) t))= household Z (scoreActor P s r A ρ (F ((plane z q).flee x)) t) :=by
  funext m y; let B:= Pressure.temp (Vale.hat P.par.R.L P.par.x s); let u:=MixedCards.actor (F x) t ρ r B
  let a:ℂ:=(sPow P.par s A:ℂ)^ (Receipt.volumeFee t); let U:=(carR 3 q (P.calibration.c m))
  change theta U (a • u _ _) = a • _; rw [theta_smul,show star a=a from by unfold a; simp]
  exact congrArg (a • ·) (congrFun (congrFun (Glare.wingMirror q ρ B x r t) (P.calibration.c m)) y)
lemma stampReflection (q:ℤ): mirror Z 3 q (litProgram L u D P s r ρ A)= litProgram L ((plane z q).flee ∘ u) D P s r ρ A:=by
  induction L with
  | nil=> exact mirror_unit ..
  | cons i l h=>
    let X:= household Z (scoreActor P s r A ρ (F (u i)) (D i)); let Y(v) := litProgram l v D P s r ρ A
    let w := (plane z q).flee ∘ u
    change mirror Z 3 q (X * Y u)=_ * Y w
    rw [mirror_times]; exact congrArg₂ (·*·) (litReflect ..) h
lemma stamp_roll (n:ℕ) : let q:=kroll P.par A n s; Tower.chime Z 3 (Heat.gaugeShift P.par.block q) (litProgram L u D P s r ρ A)=
          litProgram L (Yoke.Shuttle.forward u P.par A n s) D P s r ρ A:=by
  intro q; rw [Tower.chime, stampReflection, stampReflection]; exact congrArg (fun u=> litProgram L u D P s r ρ A) (funext fun i=> commute_f (u i) q P.par.block)
-- list products on family
lemma stamp_factors (L M:List J) : litProgram (L++M) u D P s r ρ A= litProgram L u D P s r ρ A * litProgram M u D P s r ρ A:=by unfold litProgram stampL; simp [List.prod_append]
lemma stamp_map {V:Type*}(q:V → J)(m:List V) : litProgram (m.map q) u D P s r ρ A=litProgram m (u ∘ q) (D∘q) P s r ρ A:=by unfold litProgram stampL; rw [List.map_map]; rfl

lemma mirror_set (n:ℕ) : let q:= kroll P.par A n s; let F':=Tower.chime Z 3 (Heat.gaugeShift P.par.block q) (litProgram L u D P s r ρ A)
    mirror Z 3 0 F'*F'= litProgram (twins L) (troupe u P.par A n s) (Sum.elim D D) P s r ρ A:=by
  intro q F'; unfold F' q; rw [stamp_roll,stampReflection]; exact (by unfold twins; rw [stamp_factors,stamp_map, stamp_map]; rfl)
lemma paper_room (h:∀ i∈L, P.calibration.ℓ+(r+8:ℕ)≤ nodeC (u i) z) : Tower.region z 0 P.calibration.ℓ (paperX L u r):=by
  induction L with
  | nil=> exact fun _ p=> False.elim (Finset.notMem_empty _ p)
  | cons i t ih=>
    intro x p; specialize ih (fun i v=> h i (List.mem_cons_of_mem _ v))
    let q:= skyDeck (nodeC (u i)) (r+8); rcases Finset.mem_union.mp (show x∈ q ∪ paperX t u r from p) with l | v; swap; · exact ih x v
    obtain ⟨B,p⟩:= pav_v .. |>.mp l z; specialize h i List.mem_cons_self; omega
variable {c I E:ℝ}
variable {u}
def letterTest (p:4≤r) (u:J→ Cover) : P.Test:= P.art (litProgram L u D P s r ρ A) (aux_test (paperBook L u D P s r ρ A p).1)
abbrev studioR (t:ℕ) (f:P.Test) := P.E t f.val
lemma letter_roll (p:4≤r)(u:J→ Cover) : let q:= kroll P.par A n s; P.halfShift 3 q (letterTest L D P s r ρ A p u)= letterTest L D P s r ρ A p (forward u P.par A n s):= Subtype.ext (stamp_roll ..) -- let reducible
lemma letter_revenue (p:4≤r)(u:J→ Cover) : studioR P s (P.halfShift 3 k (letterTest L D P s r ρ A p u))= studioR P s (letterTest L D P s r ρ A p u):=by
  exact SWay P.run P.large P.law s z (k:ℤ) ((marque ..).1 (letterTest L D P s r ρ A p u).property)
-- use star for all labels
lemma mirror_phase(s:ℕ)(f:P.Test):studioR P s (P.reflectTest 3 f) = star (studioR P s f):=by
 unfold studioR; rw [←P.occupied z,←P.occupied z,←P.reflected];
 let ω:=P.groundZero z; let Q:=P.compressed z s f; change inner ℂ ω (ContinuousLinearMap.adjoint Q ω) = _; rw [ContinuousLinearMap.adjoint_inner_right]; exact inner_conj_symm _ _ |>.symm -- tune

-- broad Poll variance, no travel-step comparison on hard gates. projection already on all Test.
lemma reimburse(s:ℕ) (f : P.Test) (S : Finset Cover) (p:InTest Z true S false f.val)(u:Tower.region z 0 P.calibration.ℓ S):
    (∫ x,‖P.singleState z s x f‖^2 ∂(P.pillars z)) ≤ ‖P.E s (P.reflectTest z f * f).val‖:=by
  let V := P.positiveVox z s _ f ((Tapestry.locates ..).2 p) u
  simp_rw [P.single_state,P.pillar_]; rw [P.at_label];
  let E:=P.piece z s V; change ‖(P.compressed z s (P.voxTest z s V)) (P.groundZero z)‖^2 ≤ ‖P.E s (mirror Z z 0 V.val * V.val)‖
  rw [←P.seed_pairing,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),P.seed]; exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_orthogonalProjectionOnto_apply_le ..) 2

#print axioms letterTest
#print axioms letter_roll
#print axioms mirror_phase
#print axioms mirror_set
#print axioms reimburse
#print axioms paper_room
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
