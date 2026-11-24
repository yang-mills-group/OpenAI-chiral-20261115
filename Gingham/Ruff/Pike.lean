import Gingham.Ruff.Ore
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Shells Fan
variable {n:ℕ}{a c e ρ b:ℝ} (X:Rialto n e ρ b)
    {A:Fob N e}
   {y:Site N}{u:Side}
variable (B:Plastron y u e (a/4) c A)
variable {t:ℝ}
namespace Pike

/-- One can use tail on the unmasked domain, with this price. -/
def waist (a c:ℝ)(r:ℕ):=Real.exp (-(a/4-a/8)*r)*c


variable {A₁ A₂:Fob N e}
include X
lemma fish {c₁ c₂:ℝ}
   (g:Gallery 3 (hum X A) c)(z:fderiv ℝ (hum X A) 0=0)
   (g₁:Gallery 3 (hum X A₁) c₁)(z₁:fderiv ℝ (hum X A₁) 0=0)
   (g₂:Gallery 3 (hum X A₂) c₂)(z₂:fderiv ℝ (hum X A₂) 0=0)
   (p:∀ q,A q=A₁ q+A₂ q)(v:Doub N):
 quadraticChi (hum X A) v=quadraticChi (hum X A₁) v+quadraticChi (hum X A₂) v:=by
  apply tendsto_nhds_unique (quadraticChi_pressure g z _)


  refine ((quadraticChi_pressure g₁ z₁ v).add (quadraticChi_pressure g₂ z₂ v)).congr ?_
  intro t; unfold hum; simp only [p, Matrix.trace_add]; module


structure Hem (v:Doub N)(t a c:ℝ)(u:Side)(m:ℕ)
          (f g:Doub N→ℂ):Prop where
   cutK:‖quadraticChi g v‖ ≤ Interest u (a/4) c 2*t^2
   restK:‖quadraticChi g v - quadraticChi f v‖ ≤
                     Interest u (a/8) (waist a c m) 2*t^2
   diff:‖g 0 - f 0‖≤waist a c m

lemma bobbin (m:ℕ)(l:0<a)(j:3≤n){v:Doub N}(g:sprays (bouton y) v t):
 Hem v t a c u m (hum X A) (hum X (B.light m)) :=by
  have ll:0<a/4:=by positivity
  have lm:0<a/8:=by positivity
  let B₁:=B.lightP m
  let B₂:=B.flightP m (show a/8≤a/4 by linarith)
  refine ⟨?_,?_,?_⟩
  · exact by simpa only [one_mul] using incision X B₁ (fun _ h=>h.1) ll j g


  · rw [fish X ((sing X B ll.le).sub 3 j) (sing_flat X B ll.le (by omega))
       ((sing X B₁ ll.le).sub 3 j) (sing_flat X B₁ ll.le (by omega))
       ((sing X B₂ lm.le).sub 3 j) (sing_flat X B₂ lm.le (by omega))
       (split_m B m) v, sub_add_cancel_left, norm_neg]
    exact incision X B₂ (fun _ h=>h.1) lm j g
  unfold hum; rw [B.split_m m _, Matrix.trace_add,sub_add_cancel_left,norm_neg]
  exact ((sing X B₂ lm.le) 0 (by simp)).value

/-- C³ sale (for pressure probes). -/
lemma spin (m:ℕ)(l:0<a)(j:3≤n){v:Doub N}(p:‖v‖<1):
 let f:=hum X (B.light m)
 ‖f v - f 0 - quadraticChi f v‖ ≤ c*‖v‖^3:=by
 intro f
 let B₁:=B.lightP m
 have g:= sing X B₁ (by positivity:a/4≥0)
 have z:=sing_flat X B₁ (by positivity:a/4≥0) (show 1≤n from by omega)
 exact by simpa only [one_mul,f,quadraticChi] using (g.sub 3 j).cubic z p

#print axioms spin

