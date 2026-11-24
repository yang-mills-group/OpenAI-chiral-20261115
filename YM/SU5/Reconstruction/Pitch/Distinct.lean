import YM.SU5.Reconstruction.Pitch.Campaign
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
local notation "bv"=> Domain Y H G false Set.univ
-- a different character in this room affects genuine future even singlets only, no need arbitrarily moved queries. Proof using local neutrality fill of prior.
private lemma sames (p : ∀ f:FF,(V₀ x) (Submodule.inclusion (domain_le_lawDomain Y H G (q:=true) _) f)= (V₀ y) (Submodule.inclusion (domain_le_lawDomain Y H G _ ) f)) : y=x:=by
 apply ward_unique; ext1 f; obtain ⟨s,f,rfl⟩:= (eventually_enclosed Y H G f).exists
 obtain ⟨T0,q⟩:=((marque ..).1 f.val.property).paid
 obtain ⟨m,k,eq⟩:=cap_in_common Y H V s G.history G.clipped (asLoose K f.val) q
 let z:Dome (tent Y H):= fromStrict m; let i:= ticket Y H G (s+1) z
 have ht :(asLoose K z)= bosonLabel K m:= Subtype.ext rfl
 have he:i∈Domain Y H G true Set.univ:=by apply ticket_mem; rw [insideAt_univ_singlet]; exact (marksSpec ..).2 rfl -- m
 obtain ⟨U,d,g,v⟩:= (compact_domain Y H G).1 he
 obtain ⟨z₀,z₁,x',v'⟩:= Schedule.shutters (daylight (dainty Λ)) j d
 obtain ⟨e,pe⟩:= Schedule.very_late (a:=r-(z₀:ℝ)) (daylight (dainty Λ))
 have hp : stride K j e i∈Domain Y H G true (flank j r):= relax_shape Y H G j e (z₀:ℝ) r (by linarith only [pe]) i (domain_mono Y H G (fun t hb=> (show (z₀:ℝ)< t j from (v' t hb).1).le) v)
 have hv:= domain_le_lawDomain Y H G _ he; let z' : bv:= ⟨i,hv⟩; let W₁:= (⟨_,hp⟩: Domain Y H G true (flank j r)); let g':=eq a (c a)
 have h (x:A) : (V₀ x) (Submodule.inclusion (domain_le_lawDomain Y H G (q:=true) _) W₁)= (V₀ x) (enclose Y H G Set.univ false s f):=by
    calc
     _ = (V₀ x) z' := column_cost Y H V G a c x j e z'
     _ = _:= by unfold z' i; rw [os_ticket_val,os_enclose, oneAt_reads,oneAt_reads,ht]; exact congrArg x g'
 rw [←h x,←h y]; exact p W₁
variable (v : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))) (d : Victory Y H V G.history G.clipped false j (c j) (displacement Y H V G.history G.clipped a false (c a) y j (c j)))
lemma discerns (g:x≠y): ∃ (f: FF),(V₀ x) (Submodule.inclusion (domain_le_lawDomain Y H G _ ) f)≠ (V₀ y) (Submodule.inclusion (domain_le_lawDomain Y H G _ ) f):=by
 by_contra! v; exact g (sames Y H V G a c j x y r v).symm
local notation "P'"=> dressing Y H V G a c j x y r u
local notation "Ds"=> acquit Y H V G a c j x y r u
local notation "Qf" x:max=> (Wf x).starProjection
local notation "Ω" x:max=>doorstep Y H V G.history G.clipped j false (c j) (displacement Y H V G.history G.clipped a false (c a) x j (c j))
lemma beam_pure : ‖Ω x‖=1:=fibre_vacuum (atCharacter Y H V G.history G.clipped j false (c j) (Vf x)) (setupState Y H V G.history G.clipped j false (c j) _).unit_norm
local notation "uY" f:max=> Submodule.inclusion (domain_le_lawDomain Y H G (q:=true) (flank j r)) f
include v u
lemma inOval (f:FF): (Jp x) ((X₀ x) (nearer Y H G j r u f))=(V₀ x) (uY f) • (Ω x) := by
 let z := (X₀ x) (nearer Y H G j r u f); let g:= (Jp x) z
 obtain ⟨v',t⟩:= firm_door Y H V G.history G.clipped j false (c j) (Vf x) v g ((Wf x).starProjection_apply_mem z)
 have he: inner ℂ (Ω x) g= (V₀ x) (uY f) := by
    unfold g; rw [←Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr (above_door ..)]
    unfold z; rw [expectation,os_across]; rfl
 rw [←t,inner_smul_right,inner_self_eq_norm_sq_to_K,beam_pure] at he
 change v' * (((1:ℝ):ℂ)^2:ℂ)=_ at he
 simp only [one_pow, Complex.ofReal_one,mul_one] at he
 rw [←he]; exact t.symm
include d
omit v d u in
private lemma branchPair {J H':Hilbert} (W'':Submodule ℂ (J.space × H'.space))(ωx:J)(ωy:H')(X Y' a' b':ℂ)(p:X≠Y')(h1:(ωx,ωy)∈ W'')(h₁':(X • ωx,Y' • ωy)∈ W''):
    (a' • ωx,b' • ωy)∈ W'':=by
 let δ' :=(a'-b')/(X-Y')
 have hp : a' - δ'*X+δ'*Y'=b':=by
    unfold δ'; field_simp [show X-Y'≠0 from sub_ne_zero.mpr p]; ring
 have h:= (W'').add_mem ((W'').smul_mem (a'-δ'*X) h1) ((W'').smul_mem δ' h₁'); change ((a'-δ'*X) • ωx + δ' • X • ωx, (a'-δ'*X) • ωy+ δ' • Y' • ωy)∈W'' at h
 rwa [smul_smul,smul_smul,←add_smul,←add_smul,hp,sub_add_cancel] at h
set_option maxHeartbeats 550000 in
lemma separate_already (g:x≠y) (a' b':ℂ) : (a' • (Ω x), b' • (Ω y))∈ dressing Y H V G a c j x y r u:=by
 let l:= LinearMap.range Ds; let ωx:= Ω x; let ωy:= Ω y
 let f1 : FF:= ⟨1,domain_one ..⟩
 have h1:(ωx,ωy)∈ P' := by
    change (ωx,ωy)∈ (LinearMap.range Ds).topologicalClosure; apply Submodule.le_topologicalClosure; use f1; exact Prod.ext (vacuum_ticket Y H V G j (c j) (Vf x)) (vacuum_ticket Y H V G j (c j) (Vf y))
 obtain ⟨f,p⟩:=discerns Y H V G a c j x y r g; let F1: bv:= uY f; let X:= (V₀ x) F1; let Y':= (V₀ y) F1
 have h₁': (X • ωx,Y' • ωy)∈ P':=by rw [show X • ωx=(Qf x) ((Ds f).1) from (inOval Y H V G a c j x r u v f).symm, show Y' • ωy=(Qf y) ((Ds f).2) from (inOval Y H V G a c j y r u d f).symm]; exact project_act Y H V G a c j x y r u (Ds f) (Submodule.le_topologicalClosure (LinearMap.range Ds) (LinearMap.mem_range_self Ds f))
 refine branchPair (J:=H₀ x) (H':=H₀ y) (dressing Y H V G a c j x y r u) (Ω x) (Ω y) (X:ℂ) Y' a' b' p h1 h₁'
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
