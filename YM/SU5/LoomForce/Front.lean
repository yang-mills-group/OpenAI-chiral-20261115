import YM.SU5.LoomForce.Migrate
/-!
# Through the full-state comparison of the indicated mirror sector. Turns on the
trajectory of every Layout; here at axis three.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option maxRecDepth 3300
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Morn Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey Heat
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Jewel Shuttle
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical
variable {I : Type*}
variable (P:Spine) (A:ℝ) (tag:I→ Sewer) {r:ℕ} (h:4≤r) (β:ℕ→ℝ) {o: Cover}
local notation "Λ" => P.par
local notation "Γ" => P.run
local notation "⊠" => P.calibration
local notation "F₀" => Prototype.goldF

def shellCover (r:ℕ)(u:I→ Cover)(L:List I):= wholeSky (feather (fun _=>F₀) (fun _ => pairMood) u) r L
-- buy on P.Test including supports and parity and Cov, for projection and phase.
lemma fitWords (s:ℕ)(x:I→ Cover) (L:List I) (p:4≤r) : InTest ⊠ true (shellCover r x L) false
    (household ⊠ (blockVisit P tag A s β r x L)) := living_support _ A _ _ tag L p x s β

def onWord (s:ℕ)(x:I→ Cover)(L:List I) : P.Test := P.art _ (aux_test (fitWords P A tag β s x L h))

-- reduce physical translations to reuse of same assignment. Authorized inside
-- the Mast; reflected earlier with actual anti-winding Fock stencil.
local notation "χ" s:max x:max L:max=> onWord P A tag h β s x L
lemma onWord_slide (s:ℕ)(x:I→ Cover)(L:List I) : P.reflectTest 3 (χ s x L) =χ s (fun i=> Shuttle.flip (x i)) L := by
  apply Subtype.ext; let F:= blockVisit P tag A s β r x L
  change household ⊠ (fluent 3 0 F) = household ⊠ _; unfold F; rw [block_flown]; rfl

lemma onWord_tower (n s:ℕ)(x:I→ Cover)(L:List I) : P.halfShift 3 (kroll Λ A n s) (χ s x L)= χ s (forward x Λ A n s) L:= by
  apply Subtype.ext; let F:= blockVisit P tag A s β r x L
  let c:= Heat.gaugeShift P.par.block (kroll Λ A n s)
  let G:= fluent 3 c (fluent 3 0 F); change household ⊠ G= household ⊠ _; unfold G F; rw [block_flown,block_flown]; simp_rw [show ∀ i, (plane 3 c).flee ((plane 3 0).flee (x i))= forward x Λ A n s i from fun i=> commute_f ..]; rfl


lemma twoRoll (s:ℕ)(x:I→ Cover)(L:List I):
    P.reflectTest 3 (onWord P A tag h β s x L) * onWord P A tag h β s x L =
      onWord P A (Sum.elim tag tag) h β s (Sum.elim (Shuttle.flip ∘ x) x) (Shuttle.twins L) := by
  rw [onWord_slide]; apply Subtype.ext
  let F:= blockVisit P tag A s β r (Shuttle.flip ∘ x) L; let G:= blockVisit P tag A s β r x L
  change household ⊠ (F*G)= household ⊠ (blockVisit P (Sum.elim tag tag) A s β r (Sum.elim (Shuttle.flip ∘ x) x) (Shuttle.twins L))
  apply congrArg (household ⊠); unfold F G blockVisit carpet threadRoll Shuttle.twins; rw [List.map_append,List.prod_append,List.map_map,List.map_map]; rfl

lemma supportedWord (s:ℕ) (u:I→ Cover)(L:List I):χ s u L ∈ bay P.calibration (shellCover r u L) true:=(Tapestry.locates ..).2 (fitWords P A tag β s u L h)

/-! Actual sector comparison prior to new purchase; the lemma for any
positive-side WORD, no requirement of `Voice`-narrow even at discontinuous Mark. -/
def residualx (_s:ℕ)(c:ℂ)(Y:P.Test) : P.Test := Y-c • (1:P.Test)
lemma errF (s:ℕ)(Y:P.Test)(c:ℂ)(x:P.Spectrum0 3): P.singleState 3 s x (residualx P s c Y)=P.singleState 3 s x Y-c:=by
  unfold residualx; rw [map_sub,map_smul,show P.singleState 3 s x 1=1 by simp [single_state]]; simp

lemma halfAt (s:ℕ)(Y:P.Test)(t:ℤ)(x:P.Spectrum0 3) : P.singleState 3 s x (P.halfShift 3 t Y)=P.singleState 3 s x Y := by rw [P.single_state,P.single_state,P.halfReads]

local notation "Eₛ" s:max => P.eReadL s
lemma world_half (s:ℕ)(Y:P.Test)(t:ℤ) : (Eₛ s) (P.halfShift 3 t Y)=(Eₛ s) Y := by
  have he:=congrArg (fun x:P.Ensemble 3=>inner ℂ (P.groundZero 3) (x.val (P.groundZero 3))) (P.halfReads 3 s t Y)
  change P.E s _=P.E s _; exact ((P.occupied 3 s (P.halfShift 3 t Y)).symm.trans he).trans (P.occupied 3 s Y)
lemma world_mirror (s:ℕ)(Y:P.Test) : (Eₛ s) (P.reflectTest 3 Y) = star ((Eₛ s) Y) := by
  change P.E s _=star (P.E s _)
  rw [← P.occupied 3 s Y, ←P.occupied 3 s (P.reflectTest 3 Y),← P.reflected]; let φ:= P.groundZero 3; let G:= P.compressed 3 s Y
  change inner ℂ φ (ContinuousLinearMap.adjoint G φ)= star (inner ℂ φ (G φ))
  rw [ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm (𝕜:=ℂ) _ _).symm

lemma reTest (s:ℕ)(Y:P.Test)(c:ℂ): (Eₛ s) (P.reflectTest 3 (residualx P s c Y)*residualx P s c Y) =
    (Eₛ s) (P.reflectTest 3 Y*Y)- star c*((Eₛ s) Y) - c*star ((Eₛ s) Y)+c*star c:=by
  let E:=Eₛ s; let f:=P.reflectTest 3 Y; have he: P.reflectTest 3 (residualx P s c Y)= f-star c • (1:P.Test):= by
     unfold residualx; -- as negative scalar add
     rw [sub_eq_add_neg,← neg_smul, P.sum_mirror,P.scale_mirror,star_neg, neg_smul,show P.reflectTest 3 1=1 from aureoleUnit ..]; rfl
  rw [he]; unfold residualx; rw [mul_sub, sub_mul, sub_mul]; simp_rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, one_mul,mul_one,map_sub, map_smul, show (Eₛ s) 1=1 from Tower.E_unit P.run P.large P.law s,smul_eq_mul, mul_one]; unfold f; rw [world_mirror]; ring

lemma sectorCost (s:ℕ)(c:ℂ)(F:P.Test) {S:Finset Cover}(h:F∈bay P.calibration S true)(v:Tower.region 3 0 P.calibration.ℓ S):
    (∫ x, ‖P.singleState 3 s x F-c‖^2∂(P.pillars 3)) ≤ ‖(Eₛ s) (P.reflectTest 3 (residualx P s c F)*residualx P s c F)‖ := by
  let d:=residualx P s c F; let V:= P.positiveVox 3 s S d
    ((bay ⊠ S true).sub_mem h ((bay ⊠ S true).smul_mem (bay ⊠ S true|>.one_mem) _)) v
  simp_rw [← errF P]; exact P.rosaryV 3 s d ⟨V,rfl⟩ -- check implicit proof

omit h
lemma permit_words (hL:0<A)(L:List I)(t:I→Gaia)(u:ℕ→ I→ Cover)
    (p:∀ i,Appoint P.par A (fun s=>u s i) (t i))(v:∀ i,0 < t i 3) :
    ∀ᶠ s in atTop, Tower.region 3 0 P.calibration.ℓ (shellCover r (u s) L) :=by
  let k : ℕ:=P.calibration.ℓ; let b:ℕ:=r+8
  filter_upwards [(eventually_all_finset L.toFinset).mpr (fun i _=> xfront hL (p i) (v i) (k+b))] with s g x w
  obtain ⟨i,u',v⟩:= mem_biUnion.mp w; have he:= g i u'; have hf:= ((pav_v (nodeC (u s i)) x b).1 v 3).1
  rw [zero_add]; change (↑k:ℤ) ≤ _; change ((↑(k+b):ℤ))≤_ at he; omega
#print axioms onWord_tower
#print axioms sectorCost
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
