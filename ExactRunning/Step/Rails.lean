import ExactRunning.Step.Rivals

/-!
# Restricted families passing a first-order cut

Bundle the `Fit` conditions needed for cutdet algebra on repeating
probes. `X.Railings` required along `lead` (from translation properties,
proved by machinery in ExactRunning/Mode); transfer to actual saddle (`Test.rail`)
for Schur calculation.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree


namespace Fit
variable {m n u : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype u] [DecidableEq u]
variable (P : ModeCut m) (Q : ModeCut n)

lemma clip :
    Fit P (P.direct Q) (fun _ => fromCols (1:Funds _) (0:Matrix m n ℝ)) :=
  (one P).cols (zero _ _)

lemma clip' :
    Fit Q (P.direct Q) (fun _ => fromCols (0:Matrix n m ℝ) (1:Funds n)) :=
  (zero _ _).cols (one Q)
lemma coin (c : ℝ) : Fit P P (fun _ => c • (1:Funds _)) := Fit.const (by simp)
lemma coin_unit {c : ℝ} (h : 0<c) : IsUnit (P.cutdet (c • (1:Funds _))) :=
  (Det.cutdet_nz (by simp) ((PosDef.one.smul h).det_pos.ne')).isUnit
variable {P Q}

lemma pick11 {A : ℝ → Funds (m ⊕ n)}
    (h : Fit (P.direct Q) (P.direct Q) A) :
    Fit P P (fun t => (A t).toBlocks₁₁) := by
  refine (((clip P Q).mul h).mul (clip _ _).tr).congr ?_
  filter_upwards with t
  nth_rw 1 [← fromBlocks_toBlocks (A t)]
  simp [fromCols_mul_fromBlocks,transpose_fromCols,fromCols_mul_fromRows]

lemma pick12 {A : ℝ → Funds (m ⊕ n)}
    (h : Fit (P.direct Q) (P.direct Q) A) :
    Fit P Q (fun t => (A t).toBlocks₁₂) := by
  refine (((clip P Q).mul h).mul (clip' _ _).tr).congr ?_
  filter_upwards with t
  nth_rw 1 [← fromBlocks_toBlocks (A t)]
  simp [fromCols_mul_fromBlocks,transpose_fromCols,fromCols_mul_fromRows]

lemma pick22 {A : ℝ → Funds (m ⊕ n)}
    (h : Fit (P.direct Q) (P.direct Q) A) :
    Fit Q Q (fun t => (A t).toBlocks₂₂) := by
  refine (((clip' P Q).mul h).mul (clip' _ _).tr).congr ?_
  filter_upwards with t
  nth_rw 1 [← fromBlocks_toBlocks (A t)]
  simp [fromCols_mul_fromBlocks,transpose_fromCols,fromCols_mul_fromRows]

end Fit

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} (X : BlockTie E I) (r : ℝ)

/-- Fixed one-parameter b/V profiles. -/
structure Rail (b : ℝ → Joint G m (X.up m)) (v : ℝ → Config G m) : Prop where
  full : Fit (X.together r m) (X.together r m) (fun t => X.full (b t) (v t))
  front : Fit ((ridge r).cut m (Entry G)) ((ridge r).cut m (Foot G)) (fun t => mail (v t))
  fine : Fit ((X.back r).cut (X.up m) (Entry G)) ((X.back r).cut (X.up m) (Foot G))
    (fun t => mail (b t).1)
  fix : Fit ((X.back r).cut (X.up m) (Foot G)) (X.bCut r m) (fun t => X.restored (b t))
  faddeev :
    Fit ((X.back r).cut (X.up m) (Foot G)) ((X.back r).cut (X.up m) (Foot G))
      (fun t => grenade X.μ (b t).1)

def Railings (m : Side) : Prop :=
    ∀ {x : Link G m} {z : ℝ → Link G m}, (ridge r).repeats x →
      z 0 = 0 → DifferentiableAt ℝ z 0 → (ridge r).repeats (deriv z 0) →
      X.Rail r (fun t => X.lead m (t • x)) (fun t => input G m (z t))

lemma fix_memo : Memo (fun z => X.restored (X.B0 (m:=m) z)) 0 := by
  let K (p : Point G m (X.up m)×Vault G m (X.up m)) := Stationary.extend p.2 * X.B0 p.1
  let W (p : Point G m (X.up m)×Vault G m (X.up m)) := X.B0 p.1
  have he : Thaw W 0 := (X.B0_lit (m:=m)).comp (x:=(0:Point G m (X.up m)×Vault G m (X.up m))) (w:=Prod.fst) contDiffAt_fst
  have ho : W 0=1 := X.B0_one
  have ho' : K 0=W 0 := by simp [K,W]
  have hh : Thaw K 0 := (Thaw.through contDiffAt_snd).mul he
  have hg := ((he.shields X.branches (X.choice m) (by rw [ho];rfl)).inv.mul
     (hh.shields X.branches (X.choice m) (by rw [ho', ho];rfl))).logG (by rw [ho',inv_mul_cancel])
  obtain ⟨l,n,_⟩ := memo_flash X.hμ (X.B0_lit (m:=m)).1
  exact (l.spot.cross (Memo.raw _ _)).twice (n.cross (memo_rate _ _ (F:=fun p => rocket (X.S m) (X.choice m)
    1 (X.B0 p)) (hg.neg.congr_of_eventuallyEq <| Eventually.of_forall fun _ => by simp only [Function.uncurry, rocket, atire,dress_one,W,K])))

variable {X r}
lemma Test.rail (T : X.Test m) {k : ℝ → Link G m} (hk : ContDiffAt ℝ ω k 0) (h0 : k 0=0)
    (h : X.Rail r (fun s => X.lead m (k s)) (fun s => input G m (k s))) :
    X.Rail r (fun s => T.B (k s)) (fun s => input G m (k s)) := by
  have he := memo_flash X.hμ (X.B0_lit (m:=m)).1
  exact ⟨T.travel_fit (C:=X.full) (X.full_memo X.B0_lit X.B0_fine X.V0_lit) hk h0 h.full,h.front,
    T.travel_fit (C:=fun b _=> mail b.1) he.1 hk h0 h.fine,
    T.travel_fit (C:=fun b _=> X.restored b) (X.fix_memo) hk h0 h.fix,
    T.travel_fit (C:=fun b _=> grenade X.μ b.1) he.2.2 hk h0 h.faddeev⟩

namespace Rail
variable {b : ℝ → Joint G m (X.up m)} {v : ℝ → Config G m} (h : X.Rail r b v)
include h
lemma settings : Fit ((X.back r).cut (X.up m) (Foot G)) (X.bCut r m) (fun t=>X.settings (b t)) := by
  unfold BlockTie.settings; rw [X.rear_place]; exact h.fine.tr.mul (Fit.clip _ _)

lemma throat : Fit ((ridge r).cut m (Entry G)) ((ridge r).cut m (Entry G)) (fun t=> X.throat (b t) (v t)) :=
  h.full.pick22.add (h.front.mul h.front.tr)
lemma thick (ha : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ ω (X.sitting (b t) (v t)) 0) :
    Fit (X.bCut r m) (X.bCut r m) (fun t=> X.thick (b t) (v t)) :=
  h.full.pick11.congr (ha.mono fun _ hc=> X.full_up hc)

/-- Recover verticals from completed data on shell, no separate Film needed. -/
lemma standing
    (ha : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ ω (X.sitting (b t) (v t)) 0)
    (hs : ∀ᶠ t in 𝓝 0, X.Stable (b t) (v t))
    (hp : ∀ᶠ t in 𝓝 0, Explosives (X.S m) (X.choice m) 1 (b t))
    (hu : ∀ᶠ t in 𝓝 0, IsUnit (X.high (b t) (v t)).det) :
    Fit (X.bCut r m) ((X.back r).cut (X.up m) (Foot G)) (fun t => stood (X.S m) (b t)) := by
  refine (((h.thick ha).add (h.fix.tr.mul h.fix)).inv hu.self_of_nhds.ne_zero |>.mul
     (h.fix.tr.mul h.faddeev)).congr ?_
  filter_upwards [ha,hs,hp,hu] with t hg hs ht hh
  change (X.high (b t) (v t))⁻¹ * ((X.restored (b t))ᵀ * grenade _ _)=_
  have hd : (X.high (b t) (v t)) * stood (X.S m) (b t) =
      (X.restored (b t))ᵀ * grenade X.μ (b t).1 := by
    rw [high, Matrix.add_mul, (X.wort hg hs).1, zero_add, Matrix.mul_assoc, X.restored_stood ht]
  rw [← hd, ← Matrix.mul_assoc, nonsing_inv_mul _ hh,Matrix.one_mul]

end Rail
end BlockTie
end ExactRunning
