import Velour.Gathers.Turnover
import Velour.Quilt.Sleek
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

open SatinJets OS.Semigroup
variable (P:Spine)(x:P.Spectrum0 3)
local notation "K"=>P.calibration
local notation "θ₀"=> (3:Axis)
local notation "𝒞"=> P.ColorHil θ₀ x
local notation "σ"=> P.physicalEnergy θ₀ x
local notation "τ"=>P.macroStep
local notation "m"=> timeMesh P.par
local notation "κ"=> P.shifts θ₀
local notation "β"=> bell (timeMesh P.par)


variable (Q:P.Apron)
local notation "X" => Q.dye P θ₀ x
local notation "w"=> Q.realWidth P θ₀
local notation "Δ"=>τ Q.s
local notation "g"=> duration (whenly m Q.s 1)

lemma knit_at {t b:ℝ}(p:0<b)
    (y:w+Δ≤t-b/4):
   quilt (σ) (fun _=>whenly m Q.s 1)
      (fun _ _=>X (t-b/4) (t-b/4-Δ)) b 0 =g⁻¹ • (X (t+Δ) (t-Δ) - X t t):=by
 have h:=P.macroStep_pos Q.s
 have a:w≤t-b/4:=by linarith only [y,h]
 have b':w≤t-b/4-Δ:=by linarith only [y]
 rw [quilt_turned _ _ _ _ _ p,P.quilt_speed]
 have Y:= Q.dye_twice P θ₀ x a b' (show t-b/4 ≤ t+Δ from by linarith only [p,h]) (show t-b/4-Δ ≤ t-Δ by linarith only [p])
 have Y':= Q.dye_twice P θ₀ x a b' (show t-b/4≤t by linarith only [p]) (show t-b/4-Δ≤t by linarith only [p,h])
 rw [show t+Δ-(t-b/4)=b/4+Δ by ring, show t-Δ-(t-b/4-Δ)=b/4 by ring] at Y
 rw [show t-(t-b/4)=b/4 by ring,show t-(t-b/4-Δ)=b/4+Δ by ring] at Y'
 rw [Y,Y']




end Spine
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

open SatinJets OS.Semigroup
variable (P:Spine)(x:P.Spectrum0 3)
local notation "K"=>P.calibration
local notation "θ₀"=> (3:Axis)
local notation "𝒞"=> P.ColorHil θ₀ x
local notation "σ"=> P.physicalEnergy θ₀ x
local notation "τ"=>P.macroStep
local notation "m"=> timeMesh P.par
local notation "κ"=> P.shifts θ₀
local notation "β"=> bell (timeMesh P.par)


namespace Totty
variable {P x}{T D:ℕ→P.Apron}
lemma cash (h:P.Totty θ₀ x T)
    (a:∀i,(D i).s=(T i).s)
    (b:∀i,(D i).realWidth P θ₀≥(T i).realWidth P θ₀ + τ (T i).s)
    (v:∀i,(D i).F=(duration (whenly m (T i).s 1))⁻¹ • (κ 1 (T i).F - (T i).F)):
    P.Totty θ₀ x D:=by
 let t(k i:ℕ):=(D i).realWidth P θ₀ + τ k
 let l(k i:ℕ):=t k i - τ k/4
 let r(k i:ℕ):=l k i - τ (T i).s
 have u:=h.capdyes l r
   (fun k i=>by
    unfold l t
    linarith only [P.halvesClock k,P.macroStep_pos k,b i,P.macroStep_pos (T i).s])
   (fun k i=>by
    unfold r l t
    linarith only [P.halvesClock k,P.macroStep_pos k,b i])


 have h':1≤P.par.R.L.val:=by have :=P.par.V.tallX; omega
 have B:=turnover_quilt (σ) τ (L:=(P.par.R.L.val:ℝ))
   P.macroStep_pos (by exact_mod_cast h') (fun k=> by
     simpa only [Nat.sub_zero] using P.daysF k 0 (Nat.zero_le _))
   (fun i=>whenly m (T i).s 1) _ u
 refine B.agree fun k i=>?_
 have e: (D i).realWidth P θ₀ ≤ t k i :=
    le_add_of_nonneg_right (P.macroStep_pos k).le
 have y: (T i).realWidth P θ₀ + τ (T i).s≤ t k i- τ k/4:=by
    unfold t;linarith only [P.macroStep_pos k,b i]
 exact (P.knit_at x (T i) (P.macroStep_pos k) y).trans
         (P.quilt_price x (T i) (D i) (a i) (b i) (v i) e).symm
#check cash


lemma plush {ι:Type*}{s:Finset ι}{Q:ι→ℕ→P.Apron}
   (z:ι→ℂ)(u:∀j∈s,P.Totty θ₀ x (Q j))
   (b:∀i,∀j∈s,(Q j i).s=(D i).s ∧ (Q j i).realWidth P θ₀+τ (D i).s≤(D i).realWidth P θ₀)
   (r:∀i,(D i).F=κ 1 (∑j∈s,z j • (Q j i).F)):
    P.Totty θ₀ x D:=by
 let t(k i:ℕ):=(D i).realWidth P θ₀+τ k
 let l(k i:ℕ):=t k i+τ (D i).s
 let g(k i:ℕ):=t k i-τ (D i).s
 have h(j:ι)(a:j∈s):= (u j a).capdyes l g
     (fun k i=>by
        unfold l t
        linarith only [P.halvesClock k,P.macroStep_pos k,(b i j a).2,P.macroStep_pos (D i).s])
     (fun k i=>by
        unfold g t
        linarith only [P.halvesClock k,P.macroStep_pos k,(b i j a).2])
 refine (Costly.sum s (fun j a=>(h j a).smul (z j))).agree fun k i=> ?_
 exact (P.plush_price x (D i) (fun j=>Q j i) z s (b i) (r i)
              (le_add_of_nonneg_right (P.macroStep_pos k).le)).symm


lemma textures (h:P.Totty θ₀ x T)(n:ℕ):
    P.Totty θ₀ x (fun i=>P.textured (T i) n):=by
 induction n with
 | zero=>exact h
 | succ n ih=>
   refine ih.cash (fun _=>rfl) ?_ (fun _=>rfl)
   intro i
   rw [P.texture_width,P.texture_width]
   change _ ≥ _ + τ (T i).s
   push_cast; exact le_of_eq (by ring)

lemma crop (h:P.Totty θ₀ x T)(W:Prism):
    P.Totty θ₀ x (fun i=>P.aTuba W (T i)):=by
 refine plush (Q:=fun j i=>P.textured (T i) (j+1)) W (fun j _=>h.textures (j+1)) (fun i j y=>⟨rfl,?_⟩) (fun _=>rfl)
 rw [P.texture_width,P.tuba_width]
 have e:(j+1:ℕ) ≤ lastTuba W:= Finset.le_sup (f:=fun i=>i+1) y
 have r:(j+1:ℝ) ≤ lastTuba W:=by exact_mod_cast e
 simp only [aTuba]
 push_cast at * -- only
 linarith only [mul_le_mul_of_nonneg_right r (P.macroStep_pos (T i).s|>.le)]


end Totty
#print axioms Totty.crop
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
