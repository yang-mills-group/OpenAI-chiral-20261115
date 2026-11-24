import ExactRunning.Endpoints.Total
import YM.Next.STATIONARY.Films.TraceDifference
/-!
# Coarse-cell packing, film calculus

Simplify expressions with spectral vacuum witnesses, cut conditions and cost Hessians by
incorporating reindexing into constructors; finite operators can live on their native indices
(`Crate.key m`). The reusable unit is `Tub`, indexed by a finite operator recipe itself,
ensuring combinators automatically account for translation and jets.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix


structure Crate where
  tile : Type
  [finite : Fintype tile]
  [distinct : DecidableEq tile]
  key : Side → Type
  [whole : ∀ m,Fintype (key m)]
  [separates : ∀ m,DecidableEq (key m)]
  pack : ∀ m : Side, key m ≃ Co m tile

attribute [instance] Crate.finite Crate.whole Crate.distinct Crate.separates

namespace Crate

abbrev simple (α : Type) [Fintype α] [DecidableEq α] : Crate where
  tile := α
  key m := Co m α
  pack _ := Equiv.refl _

abbrev pair (P Q : Crate) : Crate where
  tile := P.tile ⊕ Q.tile
  key m := P.key m ⊕ Q.key m
  pack m := ((P.pack m).sumCongr (Q.pack m)).trans (Equiv.prodSumDistrib _ _ _).symm

lemma pair_carry {P Q : Crate} {D : Latitude} {m : Side}
    {A : ModeCut (P.key m)} {B : ModeCut (Q.key m)}
    (h : A.Carries (D.cut m P.tile) (P.pack m)) (k : B.Carries (D.cut m Q.tile) (Q.pack m)) :
    (A.direct B).Carries (D.cut m (P.tile ⊕ Q.tile)) ((P.pair Q).pack m) :=
  (h.direct k).trans (D.direct_carries ..)

end Crate

abbrev Filling (ι : Type) (P Q : Crate) :=
  (m : Side) → Corn (Co m ι) → Matrix (P.key m) (Q.key m) ℝ

structure Tub (ι : Type) [Fintype ι] [DecidableEq ι] (P Q : Crate)
    (U : Filling ι P Q) where
  film : Film ι P.tile Q.tile
  fit_strip : ∃ a : ℝ, 0<a ∧ Play film a
  ticket m : Ticket film (fun x => repackM (P.pack m) (Q.pack m) (U m x))

namespace Tub

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R : Crate}
variable {u v : Filling ι P Q} {w : Filling ι Q R}

/-- Momentum symbol at zero background. -/
def symb (T : Tub ι P Q u) := T.film.tab

variable {m : Side}
lemma fit {A : ModeCut (P.key m)} {B : ModeCut (Q.key m)}
    {D : Latitude} (h : A.Carries (D.cut m P.tile) (P.pack m))
    (k : B.Carries (D.cut m Q.tile) (Q.pack m))
    (T : Tub ι P Q u)
    {z : ℝ → Corn (Co m ι)} (hz : z 0 = 0)
    (hd : DifferentiableAt ℝ z 0) (l : D.repeats (deriv z 0)) :
    Fit A B (fun t => u m (z t)) :=
  (D.ticket_fit (T.ticket m) hz hd l).unpack h k

section square
variable {x : Filling ι P P} {T : Tub ι P P x} {D : Latitude}

/-- Vacuum symbol has no singularities on real safe modes. -/
def Steady (T : Tub ι P P x) (D : Latitude) :=
  ∀ q, star q = q → D.safe q → IsUnit (T.symb q).det

lemma Steady.unit {A : ModeCut (P.key m)}
    (h : T.Steady D) (k : A.Carries (D.cut m P.tile) (P.pack m)) :
    IsUnit (A.cutdet (x m 0)) := by
  rw [← k.det]
  have hy := D.cut_unit (T.ticket m) (fun q hq hg => h q hq hg.safe)
  exact hy

lemma Steady.echo (h : T.Steady D)
    {A : ModeCut (P.key m)} (k : A.Carries (D.cut m P.tile) (P.pack m)) :
    Resonance D (D.play m (tableau T.film)) (fun z => A.cutlog (x m z)) := by
  have hy := D.cut_unit (T.ticket m) (fun q hq hg => h q hq hg.safe)
  have y := D.resonance (T.ticket m) hy
  simp_rw [← k.log]
  exact y

lemma Steady.medium (h : T.Steady D) : D.Medium (tableau T.film) := by
  obtain ⟨i,r,s⟩ := T.fit_strip
  exact D.tableau_Medium s r h
end square

def plus (T : Tub ι P Q u) (S : Tub ι P Q v) :
    Tub ι P Q (fun m z => u m z + v m z) where
  film := T.film.plus S.film
  fit_strip := by
    obtain ⟨i,r,s⟩ := T.fit_strip
    obtain ⟨j,t,l⟩ := S.fit_strip
    exact ⟨_,lt_min r t,(s.mono (min_le_left ..)).plus (l.mono (min_le_right ..))⟩
  ticket m := (T.ticket m).plus (S.ticket m)

def mul (T : Tub ι P Q u) (S : Tub ι Q R w) :
    Tub ι P R (fun m z => u m z * w m z) where
  film := T.film.pay S.film
  fit_strip := by
    obtain ⟨i,r,s⟩ := T.fit_strip
    obtain ⟨j,t,l⟩ := S.fit_strip
    exact ⟨_,lt_min r t,(s.mono (min_le_left ..)).pay (l.mono (min_le_right ..))⟩
  ticket m := ((T.ticket m).pay (S.ticket m)).foreign <| Eventually.of_forall fun _ =>
    (repack_multiply _ (Q.pack m) ..).symm

def tr (T : Tub ι P Q u) : Tub ι Q P (fun m z => (u m z)ᵀ) where
  film := T.film.rear
  fit_strip := by obtain ⟨i,r,s⟩ := T.fit_strip; exact ⟨_,r,s.rear⟩
  ticket m := (T.ticket m).rear

def scale (T : Tub ι P Q u) (a : ℝ) : Tub ι P Q (fun m z => a • u m z) where
  film := T.film.weight a
  fit_strip := by obtain ⟨i,r,s⟩ := T.fit_strip; exact ⟨_,r,s.weight _⟩
  ticket m := (T.ticket m).weight a

/-- Index by a recipe with the same germ. -/
def shift (T : Tub ι P Q u) (h : ∀m, u m =ᶠ[𝓝 0] v m) :
    Tub ι P Q v where
  film := T.film
  fit_strip := T.fit_strip
  ticket m := (T.ticket m).foreign <| (h m).mono fun _ hx => congr_arg _ hx

@[simp] lemma shift_symb (T : Tub ι P Q u) (h : ∀m, u m =ᶠ[𝓝 0] v m) :
    (T.shift h).symb = T.symb := rfl

variable (T : Tub ι P Q u) (S : Tub ι P Q v)
variable {p : Momentum}

lemma rails (m : Side) :
    Jaunt (approached (repackM (P.pack m) (Q.pack m) (u m 0))) T.symb 0 :=
  (T.ticket m).tab

lemma reverse (hp : star p=p) : (T.tr.symb p) = (T.symb p)ᴴ := by
  obtain ⟨i,r,s⟩ := T.fit_strip
  exact judge walentes (fun j => T.rails (walent j)) s.tab r hp

/-- Agrees on all real q by continuity and frequency meshes. -/
lemma align (h : ∀m, u m 0 = v m 0) (hp : star p=p) : T.symb p = S.symb p := by
  obtain ⟨i,r,s⟩ := T.fit_strip
  obtain ⟨j,t,l⟩ := S.fit_strip
  refine Poster.renew (s.mono (min_le_left ..)).tab (l.mono (min_le_right ..)).tab
    (lt_min r t) walentes (fun m => ⟨_,T.rails _,?_⟩) (Work.F07.realStrip _ (lt_min r t) hp)
  rw [h];exact S.rails _

@[simp] lemma plus_symb (p : Momentum) : (T.plus S).symb p = T.symb p + S.symb p := rfl
@[simp] lemma mul_symb (V : Tub ι Q R w) (p : Momentum) :
    (T.mul V).symb p = T.symb p * V.symb p := rfl
@[simp] lemma scale_symb (a : ℝ) (p : Momentum) :
    (T.scale a).symb p = (a:ℂ) • T.symb p := rfl

variable (ι P Q)
def stock (X : (m:Side) → Matrix (P.key m) (Q.key m) ℝ)
    (A : Momentum → CompM P.tile Q.tile) (hp : ∃ i : ℝ, 0 < i ∧ Poster i A)
    (ht : ∀m, Jaunt (approached (repackM (P.pack m) (Q.pack m) (X m))) A 0) :
    Tub ι P Q (fun m _ => X m) where
  film := Film.cardF A
  fit_strip := hp.imp fun _ h => ⟨h.1,Play.current h.2⟩
  ticket m := Ticket.current _ _ (ht m)

@[simp]
lemma stock_symb (X : (m:Side) → Matrix (P.key m) (Q.key m) ℝ)
    (A : Momentum → CompM P.tile Q.tile) (hp ht) :
    (stock ι P Q X A hp ht).symb = A := rfl

def ident : Tub ι P P (fun _ _ => 1) :=
  stock ι P P (fun _=>1) (fun _=>1) ⟨1,zero_lt_one,Poster.web _⟩
    (by
      intro m
      rw [repack_unit, show approached (1 : Funds (Co m P.tile)) = 1 by
        ext i j; simp [approached, one_apply, apply_ite]]
      exact Jaunt.noop)

@[simp] lemma ident_symb (p : Momentum) : (ident ι P).symb p = 1 := rfl

variable {ι P Q}
def freeze : Tub ι P Q (fun m _ => u m 0) :=
  stock ι P Q _ T.symb (T.fit_strip.imp fun _ h => ⟨h.1,h.2.tab⟩) T.rails

@[simp] lemma freeze_symb : T.freeze.symb = T.symb := rfl

variable {x : Filling ι P P} (U : Tub ι P P x)
/-- Inverse at vacuum, with jets constant. -/
def reverse0 (g : ∀ q, star q = q → IsUnit (U.symb q).det)
    (f : ∀ m, IsUnit (x m 0).det) :
    Tub ι P P (fun m _ => (x m 0)⁻¹) where
  film := U.freeze.film.back
  fit_strip := by
    obtain ⟨_,t,l⟩ := U.freeze.fit_strip
    obtain ⟨_,a,b,c⟩ := gardenGate t l.tab g
    exact ⟨_,a,(l.mono b).back c⟩
  ticket m :=
    have h : IsUnit (repackM (P.pack m) (P.pack m) (x m 0)).det :=
      (repack_det (P.pack m) (x m 0)).symm ▸ f m
    ((U.freeze.ticket m).back h).foreign <| Eventually.of_forall fun _ =>
      (repack_scale_inv _ _ (f m)).symm

@[simp] lemma reverse0_symb (g f) (p : Momentum) : (U.reverse0 g f).symb p = (U.symb p)⁻¹ := rfl

end Tub
end ExactRunning
