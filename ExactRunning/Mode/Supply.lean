import ExactRunning.Mode.Pipeline
/-!
# Coarse-cell packing for a fixed ratio: supplying the input films

In addition to ordinary mail on coarse and fine links, gives:

* `charters` - linearized prediction
* `blow`, `clears` - gauge regulator (not the mode cut) for high Hessian
* `sweet` - fine classical left Hessian on rolled indices.

For the latter spend the base's absolute analyticity supplies with no
demand for uniform rates or bounds; just shrink the strip as necessary.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing
variable (X)

abbrev Fill (P Q : Crate) := Filling (Du G) P Q
abbrev fg_bg (m : Side) (z : Box G m) : Joint G m (X.up m) :=
  X.lead m (inner G m z)
abbrev co_bg (G : Gauge) (m : Side) (z : Box G m) := input G m (outer G m z)

abbrev Tray (G : Gauge) := Tub (Du G)

def belle (G : Gauge) :
    Tray G (Front G) (Loom G) (fun m z => mail (co_bg G m z)) where
  film := segue (Sum.elim some (fun _=>none)) (matina G)
  fit_strip := ⟨1,zero_lt_one,segue.green matina_green _⟩
  ticket _ := selectL pelt_ticket

lemma greenSector : Play (sectorMail _ X.eye) X.η :=
  (Play.current (areaNice ..)).plus
    ((Dapper.green X.fresh).pay (Play.current (startNice.shares (areaNice ..))))

def fineMail :
    Tray G X.Scroll X.Fid (fun m z => mail (X.fg_bg m z).1) where
  film := sectorMail _ X.eye
  fit_strip := ⟨_,X.hη,X.greenSector⟩
  ticket m := (mail_for _ _ (X.turns m) (X.choice m) true).foreign (by simp_rw [X.joint_head]; rfl)

def charters :
    Tray G (Front G) X.Barrel (fun m z => X.prospectus (X.fg_bg m z)) where
  film := CharterR true X.eye
  fit_strip := ⟨_,X.hη,CharterR.green _ X.fresh⟩
  ticket m :=
    (issued_one _ (X.choice m) true X.branches (X.atJoint m)
      (fun i => congr_arg Prod.fst (X.joint_snd i)) (X.turns m)).foreign (by
      simp_rw [X.joint_head]; rfl)

lemma greenTon : Play (tonFilm X.eye) X.η :=
  X.greenSector.rear.pay X.greenSector

lemma greenCannon :
    ∃ w : ℝ, 0<w ∧ w ≤ X.η ∧ Play (cannonFilm X.eye) w := by
  obtain ⟨u,A,r,l,n,g⟩ := amasses G
  let w := min X.η u
  have h : Play (amFilm X.eye) w :=
    (X.greenTon.mono (min_le_left ..)).plus (Play.current (Poster.web _))
  have e : Play (pebFilm X.eye) w := by
    exact (h.back (fun z k => by rw [amc_ground _ k]; exact
      (g X.L w (min_le_right ..)).period _ k)).weight _
  exact ⟨w,lt_min X.hη r,min_le_left ..,(triple_paid _ (triple_paid _ e)).weight _⟩

def blow :
    Tray G X.Fid X.Fid (fun m z => grenade X.μ (X.fg_bg m z).1) where
  film := grenadeFilm X.eye
  fit_strip := by
    obtain ⟨w,a,b,c⟩ := X.greenCannon
    exact ⟨w,a,(X.greenTon.mono b).plus c⟩
  ticket m :=
    (shipGren _ (X.choice m) true _ (X.turns m)).foreign (by simp_rw [headingF,X.joint_head];rfl)


def clears :
    Tray G X.Fid X.Barrel (fun m z => X.restored (X.fg_bg m z)) where
  film := CanonR X.eye true
  fit_strip := by
    obtain ⟨w,a,b,c⟩ := X.greenCannon
    exact ⟨w,a,((X.greenSector.rear.mono b).pay (Play.current (Poster.web _))).plus
      (c.pay ((Chromatic.green _ X.fresh).mono b))⟩
  ticket m := (regulator_tour _ (X.choice m) true (X.atJoint m) (X.turns m) X.branches
    (fun i => congr_arg Prod.fst (X.joint_snd i))).foreign (by simp_rw [X.joint_head]; rfl)

abbrev Cane := Tray G X.Scroll X.Scroll (fun m z => flare E.p E.r (X.fg_bg m z).1)

lemma drink : Nonempty X.Cane := by
  obtain ⟨η,K,hη,hK,Q⟩ :=
    tideMark G E.σ E.C E.ε E.p.direct E.τ E.A E.house E.cap E.p.quadratic_pos.le E.hτ E.bound
  obtain ⟨U,h,hq⟩ :=
    Q walent walentes E.p E.r E.B E.Λ le_rfl E.paths E.attached E.floor (fun i=> E.sworn _) E.strip

  let w := min X.η (min η 1)
  have a : 0<w := lt_min X.hη (lt_min hη zero_lt_one)
  have hx : w ≤ X.η := min_le_left ..
  have g := fruit_mono h (show X.μ*w ≤ η from ((mul_le_of_le_one_left a.le (inch_le X.L)).trans
    ((min_le_right _ _).trans (min_le_left ..)))) le_rfl

  have c := X.bridge
  have cw : Cruise X.Phi 1 w X.drift :=
    ⟨((Play.current (ι:=Entry G) c.1).mono hx).tab,c.2.1,fun _ he _ hp => c.2.2 _ (by omega) _ (fun _ => (hp _).trans_le hx)⟩

  have hb (m : Side) :
      ∀ n, n≤2 → Bitter (melon n) (U n) (creme n) (intended (m:=m) E.p E.r) := by
    have hv : walent (m.val-1)=m := PNat.eq ((Nat.sub_add_cancel (show 1 ≤ m.val from m.2)))
    rw [← hv]
    exact hq _

  let s := RippleF U X.Phi
  have hs : Play s w := (cooking cw ((min_le_right _ _).trans (min_le_right ..)) a hK g).covered

  exact ⟨⟨_,⟨_,a,segue.green hs _⟩,fun m =>
    selectR (ι:=Entry G) (ticket_glide (X.via m) E.paths g (hb _) a)⟩⟩

def sweet : X.Cane := X.drink.some

end BlockTie
end ExactRunning
