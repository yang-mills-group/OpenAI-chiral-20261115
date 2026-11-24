import YM.SU5.Relativistic.Footprints

/-!
# Go from any resolution to the ACTUAL cutoff, including with fixed
physical separation

Slab geometric bookkeeping needn't be at fixed number of successor steps (as
in `Tone`-type norm estimates). To identify a finite insertion with an insertion
in the physical bare regulator even for the effective observations in `E(s,f)`
for a fixed s,f, we must be able to keep localization all the way up AS the bare
cutoff moves.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction

open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open SU Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark
open Journey
open Push.SectorMeasure
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L" => Λ.R.L.val
variable {S T : Finset Cover} (s : ℕ) (i k : ℕ)
local notation "host" => Host Y H i s
local notation "W" n:max S:max => volumeAround Λ l n S
local notation "N" n:max => side Y i (s+n)

lemma read_train (p : (Y.voyage i).kick ≤ k) (q : Host Y H i s S) (n : ℕ) (u : s+n ≤ Y.uv k)
    {x : Family K} (h : InTest K true S false x) :
    sharp Y H (s+n) i k (Tower.train Y H s n i k S x) = sharp Y H s i k x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [train_step, ← Nat.add_assoc s]
    have hn : legalAt Y (s+n) i k := ⟨p,by omega⟩
    exact (upper_coupling Y H (s+n) (W n S) i k hn (prepared_train Y H s S n i k h)
      (by rw [Nat.add_assoc s]; exact q.usable (n+1))).trans (ih (by omega))

lemma neutral_train (p : (Y.voyage i).kick ≤ k) (n : ℕ) (u : s+n ≤ Y.uv k)
    {x : Family K} (h : x∈ observ K S true) :
    Tower.train Y H s n i k S x∈ observ K (volumeAround Λ l n S) true := by
  induction n with
  | zero=> exact h
  | succ n ih=>
    rw [train_step]
    exact lifts_native Y H (s+n) (ih (by omega)) i k ⟨p,by omega⟩

-- port the actual chorus comparison to a quantitative hosting budget (original proof pays fixed step only)
set_option maxHeartbeats 700000 in
private lemma at_step (n : ℕ) (p : Detached Λ l S T) (q : Host Y H i s (S∪T))
    (h : legalAt Y (s+n) i k) {f g : Family K}
    (a : InTest K true (W n S) false f) (b : InTest K true (W n T) false g) :
    block Y H (s+n) i k (volumeAround Λ l n (S∪T)) (f*g) =
      block Y H (s+n) i k (volumeAround Λ l n S) f * block Y H (s+n) i k (volumeAround Λ l n T) g := by
  let x := block Y H (s+n) i k (W n S) f
  let y := block Y H (s+n) i k (W n T) g
  let z := block Y H (s+n) i k (W n (S∪T)) (f*g)
  let NS:= W n S; let NT:= W n T; let sU:= s+n; let U:= W n (S∪T); let U':= W (n+1) (S∪T)
  have hx: InTest K true U' false x:=
    (booked ..).mono (around_mono Λ l subset_union_left (n+1))
  have hy: InTest K true U' false y:=
    (booked ..).mono (around_mono Λ l subset_union_right (n+1))
  have hv: InTest K true U false (f*g) :=
    (a.mono (around_mono Λ l subset_union_left n)).mul (b.mono (around_mono Λ l subset_union_right n))
  have ht {S : Finset Cover} (w : Host Y H i s S) : Tivoli (W (n+1) S) ((K).c (momentm Y i (sU+1))) := by
    unfold sU; rw [Nat.add_assoc]; exact w.usable _
  apply stationary_ext Y H (sU+1) U' i (ht q).hosp (booked Y H sU i k U _) (hx.mul hy)
  change distribute Y H _ i z=distribute Y H _ i (x*y)
  rw [(distribute_arith Y H (sU+1) i x y 0).2.1, show distribute Y H _ _ z=aboveD Y H _ _ _ _ from reserved Y H sU U i k h hv (ht q)]
  unfold x y; rw [reserved Y H sU (W n S) i k h a (ht (Host.shrink Y H subset_union_left q)),reserved Y H sU (W n T) i k h b (ht (Host.shrink Y H subset_union_right q))]
  unfold aboveD; rw [(distribute_arith Y H sU i f g 0).2.1]; unfold nextMark
  let Q:=((Y.voyage i).X (Y.uv k)).gram; let A:= ((Y.voyage i).X (Y.uv k)).wave
  let K₁:= steps Λ.V (Y.ir i) Λ.block (Y.uv k); let Y':= (Y.voyage i).CapeT
  let G:= (Vale.apt (Y.ir i) Λ.block Λ.R.L sU); let t:= (fullness Y i k h.1).cap_grant
  obtain ⟨t'⟩:= t.grant sU h.2; obtain ⟨u',v,ax,F0,j⟩:= t'.cap
  exact separated_mult G (K₁ sU) Λ.K.j ((A sU).val) (Q (sU+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Q (sU+1)).beta (Y' sU) (R:=aliasLaw Λ) (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) F0.bill (t.branch sU h.2) t'.legal.1 t'.legal.2 _ _ (stationed Y H sU (W n S) i a) (stationed Y H sU (W n T) i b) (tissue Y i sU) (Host.far Y H p q n)

lemma through_product (p : Detached Λ l S T) (q : Host Y H i s (S∪T)) (h : (Y.voyage i).kick ≤ k)
    {f g:Family K} (a : InTest K true S false f) (b : InTest K true T false g) (n : ℕ)
    (u : s+n ≤ Y.uv k) : Tower.train Y H s n i k (S∪T) (f*g) = Tower.train Y H s n i k S f * Tower.train Y H s n i k T g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [train_step,train_step,train_step,ih (by omega)]
    exact at_step Y H s i k n p q ⟨h,by omega⟩ (prepared_train Y H s S n i k a)
      (prepared_train Y H s T n i k b)

-- general proof of support-independence on refining system at every step.
lemma support_grow (p : S ⊆ T) (q : Host Y H i s T) (h : (Y.voyage i).kick ≤ k)
    {f : Family K} (a : InTest K true S false f) (n : ℕ) (u : s+n ≤ Y.uv k) :
    Tower.train Y H s n i k S f=Tower.train Y H s n i k T f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [train_step,train_step,← ih (by omega)]
    refine (upper_overlap Y H _ _ i k ⟨h,by omega⟩ (prepared_train Y H s S n i k a)
      (around_mono Λ l p _) ?_).symm
    rw [Nat.add_assoc s]; exact q.usable (n+1)
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.through_product
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.read_train
