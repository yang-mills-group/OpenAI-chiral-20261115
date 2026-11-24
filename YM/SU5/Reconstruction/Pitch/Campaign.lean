import YM.SU5.Reconstruction.Pitch.Sequel
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i qc : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i qc I E)
  (G : GroundExtension (i := i) (k := qc) (E := E) Y H)
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

variable (a:Axis) (c : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
local notation "τ"=> marks (loomD Λ)
local notation "Δ"=> Atlas Λ
local notation "A"=> Warden Y H V G a c
local notation "H₀" x:max=> indoor Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S₀" x:max=> ride Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "X₀" x:max=> OSvector Y H V G j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "I₀"=> flank j 0
local notation "F"=> Domain Y H G false (flank j 0)
local notation "V₀" x:max=> osValue Y H V G a (c a) x
local notation "W" p:max x:max=> leader Y H V G a c p x
variable (p:Atlas Λ) (x y: Warden Y H V G a c) (k:0≤ p j) (h:leader Y H V G a c p x=y)
local notation "px" p:max=> pitches Λ j p
local notation "κ" p:max=> constellation p K
open ConePrice SelectionAnalysis
local notation "Pf" p:max k:max x:max=> promenadeFront Y H G j p x k
local notation "T"=> transportT Y H V G a c j p x y k h
open OS.Semigroup
-- In-product closures comparing at SAME clock, but opposite center observers. Actual discrimination using Joint origin (commuting filtered pricing in CStar reps). Key: produce any PAIR of VACUUM amplitudes via the dense precursor data at all future τ stamps, w/out Full.
open SelectionAnalysis
variable (r:ℝ)(u:0≤r)
local notation "FF"=> Domain Y H G true (flank j r)
local notation "Vf" x:max=> displacement Y H V G.history G.clipped a false (c a) x j (c j)
local notation "ρ" x:max=> procession Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
local notation "S"=>driveAlgebra Y H V G.history G.clipped j false (c j)
local notation "B"=>traveller Y H V G.history G.clipped j false (c j)
local notation "b"=> (SelectionAnalysis.concord (traveller Y H V G.history G.clipped j false (c j)))
local notation "Hp"=> ((H₀ x).space × (H₀ y).space)
local notation "Wf" x:max=> joint (B) (ρ x)
local notation "Jp" x:max=>(Wf x).starProjection
-- for any singlet f in `FF`, attainable in both. This is linear on common space.
include u in
noncomputable def nearer : Domain Y H G true (flank j r) →ₗ[ℂ] Domain Y H G false (flank j 0) := Submodule.inclusion (le_trans (domain_loose Y H G _) (domain_mono Y H G (TimeMesh.flank_mono j u)))
include u
noncomputable def acquit : Domain Y H G true (flank j r) →ₗ[ℂ] (H₀ x).space×(H₀ y).space:= LinearMap.prod ((X₀ x).comp (nearer Y H G j r u)) ((X₀ y).comp (nearer Y H G j r u))
lemma support_stamps (i:ℕ)(f:FF) : ∃ g:FF,∀ x:A, (ρ x) ((traveller Y H V G.history G.clipped j false (c j)) i) ((X₀ x) (nearer Y H G j r u f))=(X₀ x) (nearer Y H G j r u g):=by
 cases h: rolodex j i with
 | inl v=>
   let p:= finerNow Λ (notch (timeMesh Λ) v.1 (v.2:ℤ)); let t:=whenly (timeMesh Λ) v.1 v.2; have θ:(p:ℝ)= t:= natural_time ..
   have ht:0≤(p:ℝ):=θ.symm ▸ t.property;
   let f': FF:=⟨stride K j p f.val, relax_shape Y H G j p r r (by linarith) f.val f.property⟩
   refine ⟨f',fun x=>?_⟩; rw [traveller, Function.comp_apply,h]; change (S₀ x).E t ((X₀ x) (nearer Y H G j r u f))=_; rw [show t=Real.toNNReal (p:ℝ) from (by rw [θ,Real.toNNReal_coe])]; exact time_even Y H V G a c x j p ht _
 | inr v=>
   let s:= v.1; let p:= notch (timeMesh Λ) v.2.1 v.2.2; let v':= finerNow Λ p; let f': FF:= ⟨_,spectator_play Y H G (accept Λ v') j s.val s.property.symm _ _ f.property⟩; refine ⟨f',fun x=>?_⟩; rw [traveller,Function.comp_apply,h]; let op:= ((turnstile Y H V G.history G.clipped j false (c j) (Vf x)).crew s).play p; change (( (turnstile Y H V G.history G.clipped j false (c j) (Vf x)).crew s).play p) _ = _; rw [← older_stride Y H V G a c x j s p, owns_play]; apply congrArg (X₀ x); exact Subtype.ext (DFunLike.congr_fun (advance_even s.val v') f.val).symm

local notation "P" => (LinearMap.range (acquit Y H V G a c j x y r u)).topologicalClosure
-- stage | ghost.
noncomputable def dressing : Submodule ℂ ((H₀ x).space × (H₀ y).space) := (LinearMap.range (acquit Y H V G a c j x y r u)).topologicalClosure
local notation "P'"=> dressing Y H V G a c j x y r u
local notation "Ds"=> acquit Y H V G a c j x y r u
private lemma stamp_act (i:ℕ) (g:Hp)(q:g∈ P'):(((ρ x) (B i) g.1),((ρ y) (B i)) g.2)∈ P':=by
 let F': Hp → Hp:=fun g=>(((ρ x) (B i) g.1),((ρ y) (B i)) g.2); have he: Continuous F':= ((( (ρ x) (B i)).continuous).comp continuous_fst).prodMk ((((ρ y) (B i)).continuous).comp continuous_snd)
 refine closure_minimal (t:=F' ⁻¹' (↑P:Set ((H₀ x).space × (H₀ y).space))) ?_ ((Submodule.isClosed_topologicalClosure _).preimage he) q
 rintro g ⟨v,rfl⟩; obtain ⟨g,t⟩:=support_stamps Y H V G a c j r u i v; exact Submodule.le_topologicalClosure _ (show F' (Ds v)∈LinearMap.range Ds from ⟨g,Prod.ext (t x).symm (t y).symm⟩)
private lemma scope_act (g:Hp)(q:g∈ P'): ((ρ x) b g.1,(ρ y) b g.2)∈ P':=by
 refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (((place_sum B (travellers Y H V G.history G.clipped j false (c j)) (ρ x) g.1).prodMk (place_sum B (travellers Y H V G.history G.clipped j false (c j)) (ρ y) g.2))) ?_ -- tune explicit isClosed arg
 filter_upwards [] with i
 exact (P).sum_mem (fun i _=> (P).smul_mem ((SelectionAnalysis.weight i :ℝ):ℂ) (stamp_act Y H V G a c j x y r u i g q))
private lemma bin_act (n:ℕ)(g:Hp)(q:g∈ P'): ((ρ x) (probe b n) g.1,(ρ y) (probe b n) g.2)∈ P':=by
 have he(n): ((ρ x) (b^n) g.1, (ρ y) (b^n) g.2)∈ P' :=by
    induction n with
    | zero=> simp only [pow_zero,map_one]; exact q
    | succ n ih=>simp only [pow_succ',map_mul]; exact scope_act Y H V G a c j x y r u _ ih
 let k:ℂ:= ((n:ℂ)+1)⁻¹
 have hz: _ := (P).smul_mem k ((P).sum_mem (t:=Finset.range (n+1)) (f:=fun i : ℕ=> ((ρ x) (b^i) g.1,(ρ y) (b^i) g.2)) (fun i _=> he i))
 simp only [probe,map_smul,map_sum,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
 rw [← prod_mk_sum] at hz -- not name
 exact hz
lemma project_act (g:Hp) (q:g∈ P'): ((Jp x) g.1,(Jp y) g.2)∈ P':=by
 have he(x:A)(u:H₀ x):= SelectionAnalysis.emerges (ρ x) u B (travellers Y H V G.history G.clipped j false (c j))
 exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ((he x g.1).prodMk_nhds (he y g.2)) (Eventually.of_forall fun i:ℕ=> bin_act Y H V G a c j x y r u i g q)
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
