import ExactRunning.Mode.Select
import ExactRunning.Step.Reduction
/-!
# Coarse-cell packing templates for a fixed ratio

`rolled` includes fine offsets in an internal cell coordinate. `Barrel` contains
also coarse frame tangents; `Hold` also coarse links. `Du` is for external inputs.
`atJoint` puts them through the linear bridge, keeping e.g. the coarse links
independent of the lifted fine background. `turns` uses a Fourier map
(`eye`, also periodic analytic by `fresh`) for the result as read by the stencils.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


set_option synthInstance.maxSize 1024
open Pairing
variable (X)

abbrev Front (G : Gauge) := Crate.simple (Entry G)
abbrev Loom (G : Gauge) := Crate.simple (Foot G)

abbrev rolled (k : ℕ) : Crate where
  tile := Co X.L (Loc G k)
  key m := Lines G (X.up m) k
  pack m := unitSplit G (X.S m) k

abbrev Scroll := X.rolled 1
abbrev Fid := X.rolled 0
abbrev Barrel := X.Scroll.pair (Loom G)
abbrev Hold := X.Barrel.pair (Front G)

lemma barrel_clothe (m) : X.Barrel.pack m = clothe G (X.S m) := rfl

lemma carries_rolled (k : ℕ) (x : (X.rolled k).key m) (r : ℝ) :
    let e := (X.rolled k).pack m
    e ((X.back r).shift _ (Loc G k) x) = (ridge r).shift m _ (e x) := by
  intro e
  obtain ⟨⟨i,j,w⟩,rfl⟩ := e.symm.surjective x
  apply e.symm.injective
  rw [e.symm_apply_apply, e.apply_symm_apply]
  apply Prod.ext
  · change ((X.S m).ratio.embed i+ wrap _ (lift j)) + X.L.val • Lattice.step 3 =
      (X.S m).ratio.embed (i + 1 • (Lattice.step 3)) + _
    rw [one_smul,(X.S m).ratio.embed_leap]
    exact add_right_comm ..
  · rfl

lemma rolled_cut (r m k) :
    ((X.back r).cut (X.up m) (Loc G k)).Carries
      ((ridge r).cut m (X.rolled k).tile) ((X.rolled k).pack m) :=
  Latitude.carries (D:=X.back r) (E:=ridge r) rfl _ (fun x => X.carries_rolled k x r)

lemma barrel_cut (r m) :
    (X.bCut r m).Carries
      ((ridge r).cut m X.Barrel.tile) (X.Barrel.pack m) :=
  Crate.pair_carry (Q:=Loom G) (X.rolled_cut ..) (.refl _)

lemma hold_cut (r m) :
    (X.together r m).Carries
      ((ridge r).cut m X.Hold.tile) (X.Hold.pack m) :=
  Crate.pair_carry (P:=X.Barrel) (Q:=Front G) (X.barrel_cut ..) (.refl _)

abbrev Du (G : Gauge) := Duet (Entry G)
abbrev Box (G : Gauge) (m : Side) := Corn (Co m (Du G))

abbrev outer (G : Gauge) (m : Side) : Box G m →L[ℝ] Link G m := first m _
abbrev inner (G : Gauge) (m : Side) : Box G m →L[ℝ] Link G m := second m _
abbrev strap (G : Gauge) (m : Side) : Link G m × Link G m →L[ℝ] Box G m := zipper m _ _

abbrev atlasSeed (G : Gauge) {m n : Side} (W : Matrix (Body 1 n) (Body 1 m) ℝ) : Link G m→L[ℝ] Bang G m n :=
  (saluteLe W).prod 0

/-- eye for independent coarse and lifted input -/
def eye : Eye (Du G) (Acts G X.patch) :=
  Eyes.lhalf (arriving 0) (Entry G) +
   (Eyes.rhalf (arriving X.Phi) (Entry G) - Eyes.rhalf (arriving 0) (Entry G))

def atJoint (m : Side) : Box G m →L[ℝ] Bang G m (X.up m) :=
  (atlasSeed _ 0).comp (outer G m) +
  ((atlasSeed _ (X.W m)).comp (inner G m) - (atlasSeed _ 0).comp (inner G m))

@[simp] lemma endorse_zero_at {g : Gauge} {c f : Side}
    (w : Link g c) : endorse (G:=g) (0:Matrix (Body 1 f) (Body 1 c) ℝ) w = 0 := by
  ext i
  · change (0 *ᵥ _) _ = (0:ℝ)
    rw [zero_mulVec, Pi.zero_apply]
  rfl

lemma joint_fst (z : Box G m) :
    (X.atJoint m z).1 =
      (outer G m z, endorse (X.W m) (inner G m z)) := by
  change (saluteLe 0 _+ (saluteLe (X.W m) _ - saluteLe 0 _)) = _
  simp [saluteLe]

lemma joint_snd (z : Box G m) : (X.atJoint m z).2 = 0 := by
  change 0+(0-0) = (0:Vault G m _ × Link G m); simp

lemma joint_head (z : Box G m) :
    headOn (X.S m) (X.choice m) true (X.atJoint m z) = X.lead m (inner G m z) := by
  rw [headOn, X.joint_fst]; rfl

lemma turns (m) : Turns X.eye (billZ (X.S m) (X.atJoint m)) := by
  let S := X.S m
  have i : Turns (arriving (G:=G) 0) (atlasQ S 0) := atlas_photo S ?_
  let h := Eyes.turns_add (Eyes.turnsL i (Entry G)) (Eyes.turns_sub
      (Eyes.turnsR (atlas_photo S (X.via m)) (Entry G))
      (Eyes.turnsR i (Entry G)))
  suffices he : billZ (X.S m) (X.atJoint m) =
    (atlasQ (G:=G) S 0).comp (outer G m) + ((atlasQ (G:=G) S (X.W m)).comp (inner G m) -
        (atlasQ (G:=G) S 0).comp (inner G m)) from he.symm ▸ h
  ext1 z; simp only [billZ, atlasQ, atJoint,ContinuousLinearMap.comp_apply,
    _root_.add_apply, _root_.sub_apply, map_add,map_sub];rfl

  have he : patron G (0:Matrix (Body 1 (X.up m)) (Body 1 m) ℝ)=0 := by
    apply Matrix.ext_of_mulVec_single;intro j; rw [zero_mulVec,patron_fee]
    exact congr_arg Prod.fst (endorse_zero_at _)
  unfold Premise
  rw [he,show approached (repackM (unitSplit G S 1) (Equiv.refl _) (0:Matrix _ _ ℝ)) = 0 by ext; simp [repackM,approached]]
  exact Jaunt.zero _

lemma fresh : Fresh X.eye X.η := by
  let h := Fresh.enter (X.bridge.1)
  let e := Fresh.enter (G:=G) (P:=X.patch) (Φ:=0) (σ:=X.η) (Poster.web _)
  exact Eyes.fresh_add (Eyes.freshL e (Entry G)) (Eyes.fresh_sub (Eyes.freshR h (Entry G)) (Eyes.freshR e (Entry G)))

end BlockTie
end ExactRunning
