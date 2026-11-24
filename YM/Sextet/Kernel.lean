import YM.Sextet.GridMoment
import YM.SU5.Voyager.Shine
 
/-!
# Lemma `eq:exactS2`, kernel identification

The projected poses need not equal raw ones for just time-separated points;
actual smears and points in Plenum cost these kernels.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine

lemma transportWidth_pos (P:Spine) (s n:ℕ) (j:Axis) : 0<P.transportWidth s n j :=
  Apron.real_width_pos P j (P.macroBody (default) s n)

section Engine
variable (P:Spine) {a:Axis} (x:P.Spectrum0 a) (j:Axis) (D:P.Apron)
local notation "ξ"=>P.advocate a x j
local notation "S"=>P.seasons j ξ

lemma width_heat :
    Real.toNNReal (D.realWidth P j)=whenly (timeMesh P.par) D.s (D.u j) := by
  ext; rw [Real.coe_toNNReal _ (D.real_width_pos P j).le]; simp [Apron.realWidth,bell,whenly]

lemma flash_birth (f:P.birthF j D.s D.F) :
    flashY x D j=(S).E (Real.toNNReal (D.realWidth P j))
      (P.wealth j ξ (P.viewF j ξ D.s f)) := by
  let t:=D.u j; let p:=P.passesLater j D.s t f
  have h:=((P.engine_view j ξ D).trans (P.identical_F j ξ D.s _ p (D.card_price P j))).trans
    (P.releasedLater j ξ D.s t f)
  unfold flashY; rw [h,P.width_heat]
  exact P.bankHeat j ξ _ _
end Engine

private lemma combine_widths {H:Hilbert}{j:Axis} (S:OS.Semigroup H j) (U:H.Op)
    (h:∀r,U.comp (S.E r)=(S.E r).comp U)
    {w t:ℝ} (p:0≤w) (g:w+w≤t)
    (v v':H) :
    inner ℂ (S.E w.toNNReal v) (S.E (t-(w+w)).toNNReal (U (S.E w.toNNReal v'))) =
      inner ℂ v (U (S.E t.toNNReal v')) := by
  have e:w.toNNReal+((t-(w+w)).toNNReal+w.toNNReal)=t.toNNReal := by
    ext
    rw [NNReal.coe_add,NNReal.coe_add,Real.coe_toNNReal _ p,Real.coe_toNNReal _ (sub_nonneg.mpr g),
        Real.coe_toNNReal _ ((add_nonneg p p).trans g)]
    ring
  simp only [S.swing,←ContinuousLinearMap.comp_apply U,h]
  rw [←e,S.time _ (_+_),S.time _ w.toNNReal]
  rfl

section Pricing
variable (P:Spine) (x:P.Spectrum0 3) (s n:ℕ)
local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "w"=>P.transportWidth s n
local notation "v" Z:max=>P.macroVector x Z s n

def responseList (Z Y:Lead.Clan) :=
  usher ((P.macroBody Z s n).kiss P 3) (P.macroBody Y s n)

lemma pair_order (Z Y:Lead.Clan) {y z:Vantage} (j:Axis) (h:w j+w j<z j-y j) :
    P.Turnstile j (P.responseList s n Z Y) [false,true] (usher y z) :=
  List.pairwise_pair.mpr (show y j+w j<z j-w j from by linarith)

/-- Response to continuously positioned body labels after *holding* both resolution `s` and
length parameter `n`. Argument relative center, axis three opposed mark on first index.
Only used at time displacements `>2*w 3`; outside use the clamped motion as an extension,
with no assertion of actual readings there. Lexicographic encoding irrelevant: the row/column
set is the literal chiral slot-family indexing. -/
def kernel6 (r:Vantage) : Matrix Lead.Clan Lead.Clan ℂ := fun Z Y=>
  inner ℂ (v Z) (P.cartage 3 ξ r ((S).E (Real.toNNReal (r 3)) (v Y)))

lemma kernel6_start (J:P.Ellis 3 x) (Z Y:Lead.Clan) {r:Vantage} (h:w 3+w 3<r 3) :
    P.commonWell 3 x (P.responseList s n Z Y) (usher 0 r) [false,true]=
      P.kernel6 x s n r Z Y := by
  let B:=P.macroBody Z s n
  let D:=P.macroBody Y s n
  unfold responseList kernel6
  rw [avail_cross x (B.kiss P 3) D 3 r J h,flashY_glare,
    P.flash_birth x 3 B (P.timeDifference_birth ..),P.flash_birth x 3 D (P.timeDifference_birth ..)]
  apply combine_widths (S) _ _ (P.transportWidth_pos ..).le h.le (v Z) (v Y)
  intro t
  exact ContinuousLinearMap.ext fun y=>(P.warm_drive 3 ξ r t y).symm

theorem kernel6_price (J:P.Ellis 3 x) (Z Y:Lead.Clan) {y z:Vantage} (h:w 3+w 3<z 3-y 3) :
    P.commonWell 3 x (P.responseList s n Z Y) (usher y z) [false,true]=
      P.kernel6 x s n (z-y) Z Y := by
  let A:=P.responseList s n Z Y
  let L:List Bool:=[false,true]
  have f:usher y z ∈ P.Federation A L:=
    ⟨3,_,.refl _,P.pair_order s n Z Y 3 h⟩
  have k:= (P.common_shift 3 x A (usher y z) L J f (-y)).2
  have e:settler (usher y z) (-y)=usher 0 (z-y) := by
    funext b; cases b
    · exact neg_add_cancel y
    exact (add_comm (-y) z).trans (sub_eq_add_neg z y).symm
  rw [e] at k
  exact k.symm.trans (P.kernel6_start x s n J Z Y h)

/-- Continuity globally using motion, not claiming unprojected continuity off `Plenum`. -/
lemma kernel6_cont : Continuous (P.kernel6 x s n) := by
  refine continuous_matrix fun Z Y=>?_ ; unfold kernel6
  have k:=continuous_real_toNNReal.comp (continuous_apply (A:=fun _:Axis=>ℝ) 3)
  let y:Vantage→ _ :=fun r=>(S).E (Real.toNNReal (r 3)) (v Y)
  have hy:Continuous y:= ((S).continuousE _).comp k
  exact (continuous_const (y:=v Z)).inner (P.caravan 3 ξ id y continuous_id hy)

def vectorWall (Z:Lead.Clan) (c:ℝ) (r:Vantage) :=
  P.cartage 3 ξ r ((S).E (toWall c (r 3)) (v Z))

lemma vectorWall_cont (Z:Lead.Clan) :
    Continuous (fun cr:ℝ×Vantage=>P.vectorWall x s n Z cr.1 cr.2) := by
  have k:=toWallCont.comp (continuous_fst.prodMk ((continuous_apply (A:=fun _:Axis=>ℝ) 3).comp continuous_snd))
  have h:= ((S).continuousE (v Z)).comp k
  exact P.caravan 3 ξ Prod.snd _ continuous_snd h

lemma vectorWall_turn (Z:Lead.Clan) (r:Vantage) :
    P.vectorWall x s n Z 0 (mirrorΩ 3 r)=P.vectorWall x s n Z 0 r := by
  unfold vectorWall
  rw [of_slideP x 3 _ r (by intro i h; simp [mirrorΩ,h])]
  simp only [mirrorΩ,↓reduceIte,toWall_turn]

local notation "U"=>P.cartage 3 ξ
/-- Wall factoring uses the same vectors for *before* and *after*;
a before reading is always of an **opposed** increment. The absolute value in `toWall`
imposes no semantics when the wall is on the wrong side. -/
theorem kernel6_wall (Z Y:Lead.Clan) {y z:Vantage} {c:ℝ} (p:y 3≤c) (q:c≤z 3) :
    P.kernel6 x s n (z-y) Z Y=
      inner ℂ (P.vectorWall x s n Z c y) (P.vectorWall x s n Y c z) := by
  have u:= (show U z= (U y).comp (U (z-y)) from
    by rw [←P.cart_paves,add_sub_cancel])
  have h (r:Vantage) (t:ℝ≥0) : (U r).comp ((S).E t)=((S).E t).comp (U r):=
    ContinuousLinearMap.ext fun _=>(P.warm_drive ..).symm
  unfold kernel6 vectorWall
  rw [heat_wall (S) _ _ (h y) (h z) (v Z) (v Y) p q, u,ContinuousLinearMap.comp_apply,P.inner_pay]
  rfl

end Pricing
section GridMatching
variable (P:Spine) (x:P.Spectrum0 3) (J:P.Ellis 3 x)
include J
lemma scroll_charge (t:ℕ) {I:Type*} (L:List I) (A:I→P.Apron) (p:I → Cover)
    (h:∀i∈L,(A i).s≤t)
    (o:P.Turnstile 3 A L (P.grid t ∘ p)) (u:P.Plenum A L (P.grid t ∘ p)) :
    P.commonWell 3 x A (P.grid t ∘ p) L = P.singleState 3 t x (P.fullScroll t A p L) := by
  rw [P.common_cult 3 x A _ _ J (.refl _) o,←P.single_agrees 3 3 x]
  refine (P.entirely_now 3 x A L J 3 (P.vtile t ∘ p) o u).symm.trans ?_
  exact P.turn_purchase 3 _ A p t L o h

theorem singleton_price (A:P.Apron) (r:Vantage) :
    P.commonWell 3 x (fun _:Unit=>A) (fun _=>r) [()] = P.singleState 3 A.s x A.F := by
  let B:Unit→P.Apron:= fun _=>A
  let p:Unit → Cover:=fun _=> 0
  have e: P.grid A.s ∘ p=(0:Unit→Vantage) := by
    funext z i; unfold p Function.comp; rw [P.grid_eq]; simp
  have h (j:Axis) : P.Turnstile j B [()] (P.grid A.s ∘ p) := List.pairwise_singleton ..
  have t := P.scroll_charge x J A.s [()] B p (fun _ _=>le_rfl) (h 3)
    ⟨fun j=>⟨_,List.Perm.refl _,h j⟩⟩
  have g:P.grid A.s ∘ p ∈ P.Federation B [()] := ⟨3,_,.refl _,h 3⟩
  have f: settler (P.grid A.s ∘ p) r=(fun _=>r) := by funext; rw [e]; exact add_zero _
  rw [←f,(P.common_shift 3 x B _ _ J g r).2,t,fullScroll]
  simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]
  exact P.selected_aim 3 x A A.s le_rfl 0

variable (s n:ℕ) (Z Y:Lead.Clan)
local notation "w"=>P.transportWidth s n
local notation "L₀"=>([false,true]:List Bool)
local notation "L₁"=>([true,false]:List Bool)
local notation "A"=>P.responseList s n Z Y

omit J in
lemma pair_reverse {y z:Vantage} (j:Axis) (h:w j+w j<y j-z j) :
    P.Turnstile j A L₁ (usher y z) :=
  List.pairwise_pair.mpr (show z j+w j<y j-w j from by linarith)

omit J in
lemma pair_plenum {y z:Vantage} (h:∀j,w j+w j < |z j-y j|) :
    P.Plenum A L₀ (usher y z) := by
  constructor; intro j
  rcases lt_abs.mp (h j) with g|g
  · exact ⟨_,List.Perm.refl _,P.pair_order s n Z Y j g⟩
  exact ⟨_,List.Perm.swap true false [],P.pair_reverse s n Z Y j (by linarith)⟩

theorem grid_plenum (t:ℕ) (p q:Cover) (ht:s≤t)
    (h:w 3+w 3<P.grid t q 3-P.grid t p 3)
    (f:∀j, w j+w j < |P.grid t q j-P.grid t p j|) :
    P.kernel6 x s n (P.grid t q-P.grid t p) Z Y=
      P.singleState 3 t x
        (P.aimMark ((P.macroBody Z s n).kiss P 3) t p*P.aimMark (P.macroBody Y s n) t q) := by
  have r:P.grid t ∘ (usher p q) =usher (P.grid t p) (P.grid t q) := by funext b; cases b <;> rfl
  have g:=P.scroll_charge x J t L₀ A (usher p q)
    (by rintro (_|_) _ <;> exact ht) (r.symm ▸ P.pair_order s n Z Y 3 h)
    (r.symm ▸ P.pair_plenum s n Z Y f)
  rw [r,P.kernel6_price x s n J Z Y h] at g
  rw [g,fullScroll]
  simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]
  rfl
end GridMatching
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
