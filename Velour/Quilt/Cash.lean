import Velour.Quilt.Edging

/-!
# Using priced Aprons in backward & forward jets
-/
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

variable (s:ℕ)

lemma quilt_bell (a b:ℤ): β s (a+b)=β s a+β s b:=by
 unfold bell; rw [Int.cast_add, add_mul]
lemma quilt_dead (u:ℕ): β s ((u+u:ℕ):ℤ) - β s u = β s u:=by
 rw [Nat.cast_add,P.quilt_bell,add_sub_cancel_left]
lemma quilt_speed : ((whenly m s 1):ℝ)=τ s:=by
 rw [whenly,macroStep,Nat.cast_one,one_mul]
variable (Q:P.Apron)

lemma thread_mid (u:ℕ)(e:Q.realWidth P 3≤ β Q.s u):
    P.ThreadOp 3 x Q.s (u+u) (κ u Q.F)
       (Q.dye P 3 x (β Q.s u) (β Q.s u)):=
  Q.dyedHere P θ₀ x (w:=u+u) u _ _ rfl (P.quilt_dead Q.s u) e e
lemma thread_mid' : P.ThreadOp 3 x Q.s (Q.u θ₀ + Q.u θ₀)
          (κ (Q.u θ₀) Q.F) (Q.velour P θ₀ x (Q.realWidth P θ₀)):=
   thread_mid P x Q _ (le_refl (Q.realWidth P θ₀))
lemma thread_tick (u:ℕ)(e:Q.realWidth P θ₀ + τ Q.s≤ β Q.s u):
    P.ThreadOp θ₀ x Q.s (u+u) (κ u (κ 1 Q.F))
       (Q.dye P θ₀ x (β Q.s u + τ Q.s) (β Q.s u - τ Q.s)):=by
 have h:=P.macroStep_pos Q.s
 rw [P.shifts_sum]

 refine Q.dyedHere P θ₀ x (w:=u+u) _ _ _ ?_ ?_ (by linarith only [e,h]) (by linarith only [e])
 · rw [P.quilt_bell]
   simp only [bell,macroStep,Int.cast_one,one_mul]
   <;> try rfl
 linarith only [P.quilt_dead Q.s u]

local notation "X" => Q.dye P θ₀ x
local notation "w"=> Q.realWidth P θ₀
local notation "Δ"=>τ Q.s
lemma dye_tick {t d:ℝ}(p:w+Δ≤d)(q:d≤t):
   (σ).pad (t-d) (t-d) (X (d+Δ) (d-Δ))=X (t+Δ) (t-Δ):=by
 suffices (σ).pad (t+Δ-(d+Δ)) (t-Δ-(d-Δ)) (X (d+Δ) (d-Δ))=X (t+Δ) (t-Δ) by
   rwa [show t+Δ-(d+Δ)=t-d from by ring,
        show t-Δ-(d-Δ)=t-d from by ring] at this
 have h:=P.macroStep_pos Q.s
 exact Q.dye_twice P θ₀ x (by linarith only [p,h]) (by linarith only [p]) (add_le_add_left q _) (sub_le_sub_right q _)

-- Apron reached after stepping:
variable (D:P.Apron)
local notation "δ"=>D.realWidth P θ₀
local notation "g"=>duration (whenly m Q.s 1)

lemma quilt_price (h:D.s=Q.s)(b:w+Δ≤δ)
      (e:D.F=g⁻¹ • (κ 1 Q.F - Q.F)){t:ℝ}(p:δ≤t):
   D.velour P θ₀ x t=g⁻¹ • (X (t+Δ) (t-Δ) - X t t):=by
 let u:=D.u θ₀
 have z:β Q.s u = δ:= h ▸ rfl


 have hw:w≤δ:= (le_add_of_nonneg_right (P.macroStep_pos _|>.le)).trans b
 have a:=P.thread_mid x Q u (hw.trans_eq z.symm)
 have a':=P.thread_tick x Q u (b.trans_eq z.symm)
 rw [z] at a' a
 have r:= P.thread_mid' x D
 rw [e,h,map_smul,map_sub] at r
 have f:= r.unique ((a'.sub a).smul g⁻¹)
 rw [D.velour_twice P θ₀ x le_rfl p,f,map_smul,map_sub,
      P.dye_tick x Q b p,Q.dye_twice P θ₀ x hw hw p p]


lemma plush_price {ι:Type*}(B:ι→P.Apron)(C:ι→ℂ)(L:Finset ι)
     (h:∀i∈L,(B i).s=D.s ∧ (B i).realWidth P θ₀ + τ D.s≤ δ)
     (e:D.F=κ 1 (∑i∈L,C i • (B i).F)){t:ℝ}(p:δ≤t):
   D.velour P θ₀ x t = ∑i∈L,C i • (B i).dye P θ₀ x (t+τ D.s) (t-τ D.s):=by
 let u:=D.u θ₀
 let c(a:ℝ)(i:ι):= (B i).dye P θ₀ x (a+τ D.s) (a-τ D.s)
 have q(i:ι)(k':i∈L):
      P.ThreadOp θ₀ x D.s (u+u) (C i • (κ u (κ 1 (B i).F))) (C i • (c δ i)):=by
    obtain ⟨r,k⟩:=h i k'
    have a:(B i).realWidth P θ₀ + τ (B i).s ≤ β (B i).s u:=by rw [r]; exact k
    have t:= (P.thread_tick x _ u a).smul (C i); rw [r] at t
    exact t
 have r:=P.thread_mid' x D
 rw [e,map_sum,map_sum] at r
 simp_rw [map_smul] at r
 have f:=r.unique (ThreadOp.sum r.pos L q)
 rw [D.velour_twice P θ₀ x le_rfl p,f,map_sum]
 refine Finset.sum_congr rfl fun i l=>?_
 obtain ⟨r,k⟩:=h i l


 rw [←r] at k
 have H:=P.dye_tick x (B i) k p
 rw [r] at H
 dsimp only [c]
 rw [map_smul,H]

lemma knit_price {t:ℝ}(p:0<t)
    (y:w+Δ≤t-t/4):
   quilt (σ) (fun _=>whenly m Q.s 1)
      (fun d _=>X (d-d/4) (d-d/4-Δ)) t 0 =g⁻¹ • (X (t+Δ) (t-Δ) - X t t):=by
 have h:=P.macroStep_pos Q.s
 have a:w≤t-t/4:=by linarith only [y,h]
 have b:w≤t-t/4-Δ:=by linarith only [y]
 rw [quilt_turned _ _ _ _ _ p,P.quilt_speed]
 have Y:= Q.dye_twice P θ₀ x a b (show t-t/4 ≤ t+Δ from by linarith only [p,h]) (show t-t/4-Δ ≤ t-Δ by linarith only [p])
 have Y':= Q.dye_twice P θ₀ x a b (show t-t/4≤t by linarith only [p]) (show t-t/4-Δ≤t by linarith only [p,h])
 rw [show t+Δ-(t-t/4)=t/4+Δ by ring, show t-Δ-(t-t/4-Δ)=t/4 by ring] at Y
 rw [show t-(t-t/4)=t/4 by ring,show t-(t-t/4-Δ)=t/4+Δ by ring] at Y'
 rw [Y,Y']


end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
