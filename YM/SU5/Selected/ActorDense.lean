import YM.SU5.Selected.Voices

/-! Reaches from the whole same tower in selected representation. ALL levels,
including pollen and SEPARABILITY statement with no Hilbert axiom. The proof
slides finite translations to the right from *representation-independent* normal
form (Algebra.valve). It does not rely on clustering on the *smaller* neutral
space implicitly, so can be used strict=false too. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open MeshClock Set
local notation "A₁"=> stationC Y H V G j strict C
local notation "T₀"=> slabPolynomials Y H V G j strict C
local notation "Bk"=> boxes Y H V G j strict C
local notation "Uk"=> shifts Y H V G j strict C

lemma poly_dense : Dense {x:A₁| x.val∈ T₀} := by
  intro x
  refine Metric.mem_closure_iff.mpr fun ε hp => ?_
  obtain ⟨y,hy,v⟩:= (Metric.mem_closure_iff.mp (show x.val ∈ closure ((T₀) : Set (A→L[ℂ] A)) from x.property)) ε hp
  exact ⟨(⟨y,station_poly Y H V G j strict C hy⟩:A₁),hy,v⟩

namespace Acting
variable (T:Acting Y H V G j strict C)
local notation "Ω₀"=>T.ground
local notation "X"=>T.space.space
local notation "PS"=>T.showL
local notation "γ" s:max=>voice Y H V G j strict C T s
local notation "Q"=>boxElement Y H V G j strict C
noncomputable def citizens : Set T.space.space:= ⋃ s:ℕ, Set.range (voice Y H V G j strict C T s)
local notation "S"=> T.citizens Y H V G j strict C
local notation "RM" s:max=> (LinearMap.range (γ s))
local notation "R∞"=> ⨆ i:ℕ, RM i
lemma all_citizens : ((⨆ i:ℕ, LinearMap.range (voice Y H V G j strict C T i) : Submodule ℂ (X)) : Set T.space)= citizens Y H V G j strict C T := by
  have hm:Monotone (fun s:ℕ=>LinearMap.range (γ s)):=by
    rintro x y i _ ⟨a,rfl⟩
    exact ⟨Raise Y H G.history.circuit j 0 strict x y i a, climbs Y H V G j strict C T x a y i⟩
  exact Submodule.coe_iSup_of_directed _ hm.directed_le
include T
private lemma harbor {x:A₁} (h:x.val∈Submonoid.closure (Bk ∪ Uk)) : PS x Ω₀∈ (⨆ i:ℕ, LinearMap.range (voice Y H V G j strict C T i)) := by
  rcases valve Y H V G j strict C h with e|⟨y,⟨s,u,v,p,rfl⟩,t,q,a⟩
  · rw [still_engine Y H V G j strict C T e]; exact (le_iSup (fun i=> RM i) 0)
      (show Ω₀∈LinearMap.range (γ 0) from ⟨_,T.unison Y H V G j strict C 0⟩)
  have ht:t∈A₁:= Submonoid.closure_le.mpr (fun i p=> station_U Y H V G j strict C p) q -- tune
  let r:A₁:=⟨t,ht⟩
  rw [show x=(Q s u v p)*r from Subtype.ext a, map_mul]
  change PS (Q s u v p) (PS r Ω₀) ∈_
  rw [still_engine Y H V G j strict C T q] -- implicit r
  exact (le_iSup (fun i=>RM i) s) (show (PS (Q s u v p)) Ω₀∈ RM s from ⟨v.val,T.notes Y H V G j strict C s p v⟩)

lemma densely : Dense (citizens Y H V G j strict C T) := by
  intro x; apply closure_minimal (s:=Set.range fun i=> T.showL i Ω₀) _ (isClosed_closure) (T.sees x)
  rintro y ⟨v,rfl⟩
  let M:=T₀; let f (v:A₁):= PS v Ω₀
  have hf: Continuous f := Continuous.clm_apply (show Continuous T.showL from map_continuous _) continuous_const
  apply (hf.continuousAt (x:=v)).continuousWithinAt.mem_closure (s:={v:A₁|v.val∈M}) (poly_dense Y H V G j strict C v)
  rw [←all_citizens]; intro v hv
  change PS v Ω₀∈ (⨆ i:ℕ, LinearMap.range (voice Y H V G j strict C T i))
  rcases v with ⟨v,h⟩; change v∈ (T₀).toSubalgebra.toSubmodule at hv
  rw [poly_span] at hv; clear x
  have mono : Submodule.span ℂ (Submonoid.closure (Bk∪Uk) : Set (A →L[ℂ] A)) ≤ (A₁).toSubalgebra.toSubmodule:= by rw [← poly_span]; exact fun x p=>station_poly Y H V G j strict C p
  revert h; induction hv using Submodule.span_induction with
  | mem a p=> intro h; exact harbor Y H V G j strict C T (x:=⟨a,h⟩) p
  | zero=> intro _; change f 0 ∈ R∞; unfold f; rw [map_zero]; exact Submodule.zero_mem _
  | add x y h k p q=>
    intro hx; let x':A₁:=⟨x,mono h⟩; let y':A₁:=⟨y,mono k⟩; change f (x'+y') ∈ R∞; unfold f; rw [map_add]; exact (show f x'+f y'∈ R∞ from Submodule.add_mem _ (p (mono h)) (q (mono k)))
  | smul a x h p=> intro e; let x':A₁:=⟨x,mono h⟩; change f (a • x')∈ R∞; unfold f; rw [map_smul]; exact Submodule.smul_mem _ a (p (mono h))
end Acting
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.densely
