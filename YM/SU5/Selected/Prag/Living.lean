import YM.SU5.Selected.Prag.Light
import YM.SU5.Selected.Time.Pace
import YM.SU5.Selected.Prag.Pr
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (C : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
namespace Summer
open Germ
variable (j v:Axis)
local notation "θ" j:max=>mirror K j 0
local notation "T" v:max x:max=> relocate K v x
local notation "Y₀"=> timeMesh Λ
local notation "R" s:max r:max k:max=> Raise Y H Q.circuit k 0 false s r
local notation "Ξ" s:max r:max=> stream Y H D s (r-s)
local notation "W" j:max u:max=> Tower.Field Y H u j 0 false
local notation "M₀" s:max r:max=> castor Y₀ s r
local notation "B₀"=> (Λ.R.L.val:ℤ)
variable (s:ℕ)
variable (χ:CapCharacter Y H V Q Qc 3 false (C 3)) -- primary. Can generalize to arbitrary meeting Leg.
variable (qv:v≠j)
local notation "Λ₀" v:max=> escort Y H V Q Qc 3 false (C 3) v (C v) χ
variable (F: Birthplace Y H V Q Qc j false (C j) (escort Y H V Q Qc 3 false (C 3) j (C j) χ))
variable (P: Birthplace Y H V Q Qc v false (C v) (escort Y H V Q Qc 3 false (C 3) v (C v) χ))
local notation "V₀"=> Summer.Polaris Y H V Q Qc j false (C j) F
local notation "U₀" a:max=> (((V₀).crew a).play)
local notation "Π" a:max F:max=> Diary.jetTime Y H V Q Qc a false (C a) F
local notation "ρ" v:max F:max=> markedActor Y H V Q Qc v false (C v) F
namespace Refracts
variable {z m:ℤ}{x y: Tower.Field Y H s j 0 false}{X Y': Tower.Field Y H s v 0 false}
   (u:Refracts Y H s v j z m x y X Y')
local notation "Ψ"=> (notch (timeMesh Λ) s)
local notation "Δ" x:max=> ((U₀ (⟨v,qv⟩:Trans j)) x)
local notation "δ" t:max w:max=> whenly (timeMesh Λ) t w
local notation "ω" j:max x:max a:max=> (bornTest Y H j false s x a)
local notation "Λ'" x:max => ((Π v P).E x)
local notation "L" F:max s:max=> (ρ j F) s
local notation "Ξv" F:max s:max=> (ρ v F) s
lemma notch_bigger (M:Mesh)(s:ℕ)(q:marks M):∃ t≥s,∃ i, notch M t i=q:=by obtain ⟨v,i,rfl⟩:= notch_exists M q; exact ⟨_,le_max_left s v,_,notch_up M v _ (le_max_right s v) i⟩
lemma fountCover (M:Mesh)(s t:ℕ)(e:s≤t)(m n:ℤ)(q : 0≤ bell M t n + bell M s m): ∃ i:ℕ, n+castor M s t m=(i:ℤ) ∧ Real.toNNReal (bell M t n + bell M s m)= whenly M t i:=by
 let b:= n+castor M s t m; have he:bell M t n + bell M s m=bell M t b:=by unfold b; rw [bell_add, refineZ M s t e]
 have hp: 0≤ b:= (bell_le M t 0 b).mp (by rw [←he]; exact (show bell M t 0=0 by simp [bell]).trans_le q); let i:=b.toNat; have h:b=(i:ℤ):=(Int.toNat_of_nonneg hp).symm; refine ⟨i,h,?_⟩; rw [he,h,natural_time]; exact Real.toNNReal_coe
lemma loom_h (M:Mesh)(s t:ℕ)(m:ℤ)(p:0 < m):0<castor M s t m:= by unfold castor; have ht:0<M.L:=zero_lt_one.trans_le (by have h:=M.Llarge; omega); positivity -- name
lemma bell_p (M:Mesh)(s:ℕ)(m:ℤ)(p:0 < m):0< bell M s m:=by unfold bell; have hp:0<(mill M s).val:= mill_pos M s; positivity
local notation "Γ"=> marks Y₀
local notation "α" i:max=> (((i:Γ):ℝ)+bell (timeMesh Λ) s m)
local notation "Ε₀" t:max b:max=>Raise Y H Q.circuit b 0 false s t
private lemma hasBy {H H':Hilbert}{D:Mesh}{s:ℕ}{m:ℤ} (x y:H)(X Y:H') (S:marks D→ H.Op)(T':ℝ≥0→H'.Op) (p:∀ t≥s,∀ (a:ℤ)(i:ℕ), a+castor D s t m=(i:ℤ) → inner ℂ x (S (notch D t a) y)=inner ℂ X (T' (whenly D t i) Y)) (i:marks D) (z:0≤ (i:ℝ)+ bell D s m): inner ℂ x (S i y)=inner ℂ X (T' (Real.toNNReal ((i:ℝ)+bell D s m)) Y):=by
 obtain ⟨t,h,a,rfl⟩:= notch_bigger D s i; obtain ⟨i,t0,e⟩:= fountCover D s t h m a z; exact (p t h a i t0).trans (congrArg (fun t=> inner ℂ X (T' t Y)) e.symm)
include V Q Qc C F P u qv
lemma BellCross (i:marks (timeMesh Λ))(p: 0≤ α i): inner ℂ ((L F s) x) ((Δ i) ((L F s) y))= inner ℂ ((Ξv P s) X) ((Λ' ((α i).toNNReal)) ((Ξv P s) Y')):=by
 refine hasBy (H:=F.H) (H':=P.H) (D:=timeMesh Λ) _ _ _ _ (U₀ ⟨v,qv⟩) ((Π v P).E) ?_ i p; intro t h i' a b
 have he:= ICross Y H V Q Qc C j v t χ qv F P (u.escalates Y H V Q s t h) i' a b
 exact (congrArg₂ (inner ℂ) (path Y H V Q Qc j false (C j) F s t h x).symm (congrArg (Δ (notch (timeMesh Λ) t i')) (path Y H V Q Qc j false (C j) F s t h y).symm)).trans (he.trans (congrArg₂ (inner ℂ) (path Y H V Q Qc v false (C v) P s t h X) (congrArg (Λ' (δ t a)) (path Y H V Q Qc v false (C v) P s t h Y')))) 
lemma aliveC (i:Γ)(p:0 < α i) : ContinuousAt (fun k:Γ=> inner ℂ ((L F s) x) ((Δ k) ((L F s) y))) i:=by
 let V': Γ→ℝ:=fun k=> α k; let f(k:Γ):= inner ℂ ((Ξv P s) X) ((Λ' (Real.toNNReal (V' k))) ((Ξv P s) Y')); have hf:Continuous V':= continuous_subtype_val.add continuous_const
 have hv :Continuous f:= continuous_const.inner (((Π v P).continuousE ((Ξv P s) Y')).comp (continuous_real_toNNReal.comp hf)); exact hv.continuousAt.congr ((hf.continuousAt.eventually (lt_mem_nhds p)).mono (fun t ht=> (BellCross Y H V Q Qc C j v s χ qv F P u t (show 0≤ α t from ht.le)).symm)) -- tune congr direction
end Refracts
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Refracts
#print axioms BellCross
#print axioms aliveC
#print axioms loom_h
