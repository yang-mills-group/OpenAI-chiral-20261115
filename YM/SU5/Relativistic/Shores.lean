import YM.SU5.Relativistic.FermiStep
import YM.SU5.Relativistic.Branches
import YM.SU5.Relativistic.Aisles
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
local notation "W"=>wingspan Λ l

variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(u:ℕ→ℕ)(p: StrictMono u)
local notation "ℑ" r:max=>i (a (u r))
local notation "B" r:max=>k (b (u r))
local notation "L₁" r:max s:max S:max b':max => moveUp Y H s (i (a (u r))) (k (b (u r))) S b'
local notation "Σ₀"=>Bedside Y H (i:=i) (k:=k) (a:=a) (b:=b)
-- Banach estimates for support implementation. Normalized unit ball -> any scale
section shore
variable (s:ℕ)(S:Finset Cover){b':Bool}
variable (m:Side)(v:Tivoli (wingspan Λ l S) ((tent Y H).c m)) (x: Bedside Y H (i:=i) (k:=k) (a:=a) (b:=b) s b' S m u)
include Q x v V p
lemma shore : ∃ (c:ℝ) (F : Rough b' (tent Y H) S → Family (tent Y H)), 0<c ∧ (∀ z,InTest K true (wingspan Λ l S) b' (F z) ∧ pay (F z) c) ∧ ∀ e:ℝ,0<e→∀ᶠ r:ℕ in atTop,∀ f:Rough b' K S, pay ((L₁ r s S b') f.val) c ∧ pay ((L₁ r s S b') f.val-F f) e:=by
 obtain ⟨⟨C,q,r⟩,Φ,h⟩:=x
 let I':=W S; let L:=K; let G(f:Rough b' K S)(V:Fields ((K).c m)):= Φ (f,V)
 have ht(f): AtSupport b' (Satin.region I' ((K).c m)) (G f):= firmS (C:=C) (P:=fun n=>(moveUp Y H s (ℑ n) (B n) S b' f.val m)) (fun i=>(stay ..).support m) (r.mono fun i t x=>t (f,x)) (fun x=> sights h (f,x)) -- G notation shadows
 have X0(f):∃ a:Family K, InTest K true I' b' a∧ a m=G f:= by cases b' <;> first | exact ⟨Tower.extendAtlas _ _ m v _,Tower.dictionary _ _ m v _ (ht f),Tower.native _ _ m v _ (ht f)⟩| exact ⟨FermionSlab.extendAtlas _ _ m v _,OddList _ _ m v _ (ht f),refunded _ _ m v _ (ht f)⟩
 choose F F' wh using X0
 let S₀:= coverCharge I' b'; have hv:0≤ S₀:=by unfold S₀ coverCharge; split<;> positivity
 let R:= S₀*C+1
 have he {x:Family (tent Y H)}{a b:ℝ}(t:pay x a)(u:a≤b): pay x b:=fun i v=>(t ..).trans u
 refine ⟨R,F, show 0<R from by unfold R; positivity, fun f=> ⟨F' f,he (cover_pays I' (F' f) v.hosp (C:=C) ?_) (le_add_of_nonneg_right zero_le_one)⟩,fun e t=>?_⟩
 · intro z; rw [wh]; exact le_of_tendsto (sights h (f,z)).norm (r.mono fun i t=> t (f,z))
 let d:= e/(1+S₀); have hd:0<d:=by unfold d; positivity
 filter_upwards [h _ hd,r] with t1 k' r f
 let g:= moveUp Y H s (ℑ t1) (B t1) S b' f.val
 have vg: InTest L true I' b' g:= stay Y H s _ _ S _ _
 have hp:S₀*d≤ e:= by have he: d*(1+S₀)=e:= div_mul_cancel₀ _ (by linarith); nlinarith
 refine ⟨he (cover_pays I' vg v.hosp (C:=C) ?_) (le_add_of_nonneg_right zero_le_one),he (cover_pays I' (inLess vg (F' f)) v.hosp (C:=d) ?_) hp⟩
 · intro x; exact r (f,x)
 intro x; rw [Pi.sub_apply,Pi.sub_apply, wh]; exact k' (f,x)
-- cases b' to lift causing dependency on V/Q binder include error, use where lemmas
end shore
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
