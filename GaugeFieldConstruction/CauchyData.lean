import GaugeFieldConstruction.Labels
import Mathlib.Analysis.Complex.Basic

/-!
# U1: Spatial Cauchy data of the letter jets

An implementation of the certificate not tied to a polynomial library's
concrete encoding. Keep spatial derivatives only, eliminate t derivatives
by the free equations for a *single* leg in (62). The exterior letter additionally
has spatial divergence constraints jet electric and magnetic fields. There will be no
loss in the pivot test by executing in these coordinates (Chart comparison theorem).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function
open scoped BigOperators
namespace Cauchy
variable {α β : Type*}

/-- Module of jets with spatial Cauchy coordinate index set α. -/
abbrev J (α : Type*) := α →₀ ℂ
def ket (a : α) : J α := Finsupp.single a 1
abbrev jet [AddCommGroup β] [Module ℂ β] (f : α → β) : J α →ₗ[ℂ] β :=
  Finsupp.linearCombination ℂ f
@[simp] theorem on_ket [AddCommGroup β] [Module ℂ β] (f : α → β) (a : α) : jet f (ket a)=f a := by
  simp [ket, jet, Finsupp.linearCombination_single]
lemma ket_ext [AddCommGroup β] [Module ℂ β] {a b : J α →ₗ[ℂ] β}
    (h : ∀ i, a (ket i) = b (ket i)) : a=b := Finsupp.lhom_ext fun i c => by
  rw [show Finsupp.single i c=c • ket i by simp [ket],map_smul,map_smul,h]

abbrev MI := ℕ × ℕ × ℕ
abbrev τ : Axis := 3
abbrev S3 := SpaceAxis
abbrev Spin := Fin 2
abbrev FIndex := Spin × MI
abbrev CJet := J FIndex
abbrev P4 := Axis → ℂ
abbrev Sp := S3 → ℂ
abbrev plusSpin := Fin 2
/-- b=true if this is R. false for C. -/
def Hij : Axis → Spin → Spin → ℂ :=
  ![![![0,-Complex.I], ![-Complex.I, 0]], ![![0,-1],![1,0]],
    ![![-Complex.I,0],![0,Complex.I]], ![![1,0],![0,1]]]

def coeffCR (b : Bool) (i : Axis) (a c : Spin) : ℂ := if b then Hij i a c else Hij i c a

/-- p∈C⁴, u row for C, column for R. The shell equations read:
 ∀ a, ∑ ic, p_i u_c H_i[c,a] = 0 (column-R uses H_i[a,c]). -/
structure Weyl (b : Bool) where
  p : P4
  u : Spin → ℂ
  chiral (a : Spin) : ∑ i : Axis, ∑ c : Spin, p i * u c * coeffCR b i a c=0

/-- Spatial monomials; can use momentum itself as a derivative, no i in this test. -/
def power (p : P4) (a : MI) := p 0 ^ a.1 * p 1 ^ a.2.1 * p 2 ^ a.2.2
def bump (i : S3) (x : MI) : MI :=
  if i=0 then (x.1+1, x.2) else if i=1 then (x.1,x.2.1+1,x.2.2) else (x.1,x.2.1,x.2.2+1)
lemma power_bump (i : S3) (p : P4) (x : MI) : power p (bump i x) = p i.castSucc * power p x := by
  fin_cases i <;> norm_num [bump,power,pow_succ] <;> try (change _ = p 2 * power p x; unfold power)
  all_goals ring

/-- shorthand for spatial derivatives. -/
def C (a : Spin) (n : MI) : CJet := ket (a,n)
def Cshift (k : S3) : CJet →ₗ[ℂ] CJet := jet fun j : FIndex => C j.1 (bump k j.2)
def Ctime (b : Bool) : CJet →ₗ[ℂ] CJet := jet fun j : FIndex =>
  -(∑ k:S3, ∑ c:Spin, coeffCR b k.castSucc j.1 c • C c (bump k j.2))
def Cder (b : Bool) (i : Axis) : CJet →ₗ[ℂ] CJet :=
  Fin.lastCases (motive:=fun _ => _) (Ctime b) Cshift i

@[simp] lemma Cspace (b : Bool) (s : S3) : Cder b s.castSucc=Cshift s := by simp [Cder]
@[simp] lemma Clast (b : Bool) : Cder b τ = Ctime b := by
  have he : τ=Fin.last 3 := rfl; rw [he, Cder,Fin.lastCases_last]

/-- plane-wave test. -/
def Weyl.read {b : Bool} (w : Weyl b) : CJet →ₗ[ℂ] ℂ := jet fun i : FIndex => w.u i.1 * power w.p i.2
@[simp] lemma Weyl.read_C {b : Bool} (w : Weyl b) (a : Spin) (n) : w.read (C a n)=w.u a * power w.p n := by
  unfold C; exact on_ket ..
private lemma chiral_time {b : Bool} (w : Weyl b) (a : Spin) :
    w.p τ * w.u a = - (∑ k : S3, ∑ c : Spin, w.p k.castSucc * w.u c * coeffCR b k.castSucc a c) := by
  apply eq_neg_iff_add_eq_zero.mpr
  have he (j : Spin) : ∑ c : Spin, w.p τ * w.u c * coeffCR b τ j c = w.p τ * w.u j := by
    unfold coeffCR; cases b <;> fin_cases j <;> simp [Fin.sum_univ_succ, Hij,τ]
  rw [add_comm,← he,← w.chiral a]
  exact (Fin.sum_univ_castSucc (f:=fun i : Axis => ∑ c : Spin, w.p i * w.u c * coeffCR b i a c)).symm

lemma Weyl.frequency {b : Bool} (w : Weyl b) (i : Axis) :
    w.read ∘ₗ Cder b i=w.p i • w.read := by
  apply ket_ext
  intro j
  refine Fin.lastCases (i:=i) ?_ ?_
  · change w.read (Cder _ τ _) = w.p τ * w.read (C j.1 j.2)
    rw [Clast, Ctime,on_ket,map_neg,map_sum]
    simp_rw [map_sum, map_smul, smul_eq_mul,Weyl.read_C, power_bump]
    rw [← mul_assoc (w.p τ), chiral_time, neg_mul, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by ring
  intro j'
  change w.read (Cder _ _ _) = w.p _ * w.read (C j.1 j.2)
  rw [Cspace, Cshift, on_ket]
  simp [power_bump]; ring

/-- Spatial transverse data. `mask=true` means magnetic,
 false means electric. Component 2 has no ∂₂ slot. -/
abbrev Trans := {i : S3 × MI // i.1 = 2 → i.2.2.2 = 0}
abbrev GIndex := Bool × Trans
abbrev GJet := J GIndex

def strip (z : MI) : MI := (z.1,z.2.1,z.2.2-1)
def G (mask : Bool) (a : S3) (z : MI) : GJet :=
  if h : a=2 → z.2.2=0 then ket (mask,⟨(a,z), h⟩) else
    -(ket (mask,⟨(0,bump 0 (strip z)),by intro he; exact (by decide : (0:S3) ≠ 2) he |>.elim⟩) +
      ket (mask,⟨(1,bump 1 (strip z)),by intro he; exact (by decide : (1:S3) ≠ 2) he |>.elim⟩))

@[simp] lemma picked_G (i : GIndex) : G i.1 i.2.val.1 i.2.val.2 = ket i := dif_pos i.2.property

def cw (k : S3) : S3 := k+1
def ccw (k : S3) : S3 := k+2

def Gshift (k : S3) : GJet →ₗ[ℂ] GJet := jet fun j : GIndex => G j.1 j.2.val.1 (bump k j.2.val.2)
def Gtime : GJet →ₗ[ℂ] GJet := jet fun j : GIndex =>
  let a := cw j.2.val.1; let b := ccw j.2.val.1
  G (!j.1) b (bump a j.2.val.2) - G (!j.1) a (bump b j.2.val.2)
def Gder (i : Axis) : GJet →ₗ[ℂ] GJet := Fin.lastCases (motive:=fun _ => _) Gtime Gshift i

@[simp] lemma Gspace (s : S3) : Gder s.castSucc = Gshift s := by simp [Gder]
@[simp] lemma Glast : Gder τ=Gtime := by
  have he : τ = Fin.last 3 := rfl; rw [he, Gder,Fin.lastCases_last]

def spinfield (x : Bool → Sp) (i j : Axis) := Fin.lastCases (motive:=fun _ => _)
   (Fin.lastCases (motive:=fun _ => ℂ) 0 (fun a=>x false a) j)
   (fun a => Fin.lastCases (motive:=fun _ => ℂ) (-x false a)
     (fun b => if a=b then 0 else if b=cw a then x true (ccw a) else -x true (ccw b)) j) i
/-- F_ij (without Color) via E_i=F_{3i}; e.g. B0=F12. -/
def F (i j : Axis) (z : MI := 0) : GJet := Fin.lastCases (motive:=fun _ => _)
   (Fin.lastCases (motive:=fun _ => GJet) 0 (fun a=>G false a z) j)
   (fun a => Fin.lastCases (motive:=fun _ => GJet) (-G false a z)
     (fun b => if a=b then 0 else if b=cw a then G true (ccw a) z else -G true (ccw b) z) j) i

structure Maxwell where
  p : P4
  a : Bool → Sp
  charge (mask : Bool) : ∑ k : S3, p k.castSucc * a mask k = 0
  curl (mask : Bool) (i : S3) : p τ * a mask i =
    p (cw i).castSucc * a (!mask) (ccw i) - p (ccw i).castSucc * a (!mask) (cw i)

namespace Maxwell
def read (w : Maxwell) : GJet →ₗ[ℂ] ℂ := jet fun i : GIndex => w.a i.1 i.2.val.1 * power w.p i.2.val.2
@[simp] lemma read_G (w : Maxwell) (mask : Bool) (i : S3) (z : MI) : w.read (G mask i z)=w.a mask i * power w.p z := by
  unfold G; split_ifs with h
  · unfold read; exact on_ket ..
  simp only [map_neg,map_add,read,on_ket,power_bump]
  push Not at h; rcases h with ⟨rfl,h⟩
  conv_rhs =>
    rw [show z = bump 2 (strip z) from Prod.ext rfl (Prod.ext rfl <| by
      change z.2.2=z.2.2-1+1; omega), power_bump]
  have he := w.charge mask; simp [Fin.sum_univ_succ] at he
  norm_num
  rw [show Fin.castSucc (2:Fin 3)=2 from rfl]
  linear_combination -(power w.p (strip z)) * he

lemma frequency (w : Maxwell) (i : Axis) : w.read ∘ₗ Gder i=w.p i • w.read := by
  apply ket_ext
  intro j
  refine Fin.lastCases (i:=i) ?_ ?_
  · change w.read (Gder τ (ket j)) = w.p τ * w.read _
    rw [Glast, Gtime,on_ket]
    dsimp only
    rw [map_sub, read_G, read_G,power_bump,power_bump,← picked_G j,read_G]
    rw [← mul_assoc (w.p τ), w.curl]
    ring
  intro j'
  change w.read (Gder _ (ket j)) = w.p _ * w.read _
  rw [Gspace, Gshift, on_ket, read_G, power_bump,← picked_G j,read_G]; ring

lemma read_F (w : Maxwell) (i j : Axis) (z : MI) : w.read (F i j z) = spinfield w.a i j * power w.p z := by
  refine Fin.lastCases (i:=i) ?_ fun i' => ?_
  all_goals refine Fin.lastCases (i:=j) ?_ fun j' => ?_
  all_goals simp only [F, spinfield, Fin.lastCases_castSucc, Fin.lastCases_last]
  · simp
  · simp
  · simp
  split_ifs <;> simp
end Maxwell
end Cauchy
end YM.GaugeFieldConstruction
