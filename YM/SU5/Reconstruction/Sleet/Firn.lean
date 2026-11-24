import YM.SU5.Reconstruction.Sleet.Outlet
/-! # Honest one-ray momentum grant and continuation in this selected reading. Here already buy the Wick angle from a,b even grid, with NO further Momentum price -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5200
set_option synthInstance.maxSize 33000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers LightBudget Storm
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
local notation "W" => placement Λ
local notation "L" j:max=> lowland j 0
local notation "N" j:max=> flank j 0
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
variable (j b:Axis)(p:b≠j)
variable {x y:Sky (tent Y H)}

structure Thermal (j:Axis) (x y:Sky (tent Y H)) : Prop where
  cloud: x∈Domain Y H G false (lowland j 0)
  pupil: y∈Domain Y H G false (flank j 0)
variable (h:Thermal Y H G j x y)
include h
lemma Thermal.holefront: flipMark j (tent Y H) x∈Domain Y H G false (flank j 0):=reversed_fit Y H G j false 0 (by simpa only [neg_zero] using h.cloud)
omit h

-- unshifted program. €
noncomputable def ridgeLine (j b:Axis) (x y:Sky (tent Y H)) (v t:marks (timeMesh Λ)):=x * move (tent Y H) (terrainK j b v t) y
include h p V in
lemma Thermal.outgo (v t:Gt)(e:0≤ v.val):ridgeLine Y H j b x y v t∈ D univ:=time_ordered Y H V G j (Thermal.holefront Y H G j h) h.pupil _ (by rw [terrain_time p]; exact e)
local notation "Y₀" s:max k:max=>whiff Y H V G C a χ (ridgeLine Y H j b x y s k)
noncomputable def maxFare : ℝ:= ‖OSvector Y H V G j (C j) (wk j) ⟨_,Thermal.holefront Y H G j h⟩‖*‖OSvector Y H V G j (C j) (wk j) ⟨_,h.pupil⟩‖
include h p V
lemma progress_heat (C':ℝ)(t: maxFare Y H V G C a χ j (x:=x) h≤ C')(s:Gt): Voucher thermal (fun v:Shard Gt=>whiff Y H V G C a χ (ridgeLine Y H j b x y v.val s)) C' := by
 let z:= OSvector Y H V G j (C j) (wk j) ⟨_, (Thermal.holefront Y H G j h)⟩; let y':=(Os j) ⟨y,h.pupil⟩; let j':Trans j:=⟨b,p⟩; let Y':=( (U₀ j).track.crew j').play s y'
 refine (Voucher.rename thermal C' (by funext v; exact (measure_dials Y H V G C a χ j (Thermal.holefront Y H G j h) h.pupil p v.val s (thermal_pos v).le).symm) (timeEarn thermal (fun v=> (thermal_pos v).le) (A₀ j) z Y' C' ?_)) -- syntax Binder
 unfold Y'; rw [Players.wins]; exact t

include p
lemma weather_tag (k:Thermal Y H G b x y)(B:ℝ)(s:maxFare Y H V G C a χ j h≤B)(t:maxFare Y H V G C a χ b k≤ B):∃ (F:ℝ→ℂ→ℂ)(G':ℂ→ℝ→ℂ), Squall B F G' ∧ ∀ s t: Shard Gt, F (thermal s) (thermal t)=whiff Y H V G C a χ (ridgeLine Y H j b x y s.val t.val)∧ G' (thermal s) (thermal t)=whiff Y H V G C a χ (ridgeLine Y H j b x y s.val t.val):= by
 apply preordained (thermal_course (daylight (timeMesh Λ))) _ _ (fun i=>progress_heat Y H V G C a χ j b p h B s (i:↥Gt)); intro i
 simp_rw [ridgeLine,terrain_reverse p]; exact progress_heat Y H V G C a χ b j (Ne.symm p) k B t (i:↥Gt)

/-- already accounting these Eu motions along this tube. Can use ports on z=τ. -/
lemma snow_circle (k:Thermal Y H G b x y)(r:Shard Gt):
    let R:ℝ:=thermal r
    ∃ F:ℂ→ℂ,AnalyticOnNhd ℂ F (Metric.ball 0 R)∧ (∀ z∈ Metric.ball 0 R,‖F z‖≤ max (maxFare Y H V G C a χ j h) (maxFare Y H V G C a χ b k)) ∧ ∀ z:Gt, |(z:ℝ)| < R→ F (↑(z:ℝ))=whiff Y H V G C a χ (ridgeLine Y H j b x y (r.val+z) (r.val-z)):= by
 intro R
 obtain ⟨F,X₁,hx,c⟩:= weather_tag Y H V G C a χ j b p h k _ (le_max_left ..) (le_max_right ..)
 let f(z:ℂ):=(R:ℂ)+z; let g(z:ℂ):=(R:ℂ)-z
 have hp(z:ℂ)(t:z∈ Metric.ball 0 R): Towerbound (f z) (g z):= deck (by rw [← dist_zero_right z]; exact Metric.mem_ball.mp t)
 refine ⟨fun z=>sally F (f z) (g z), accountCurve hx Metric.isOpen_ball hp (fun i _=> by unfold f;fun_prop) (fun i _=>by unfold g;fun_prop),fun z v=> rocket hx (hp z v),fun z v=>?_⟩
 obtain ⟨e,t⟩:=abs_lt.mp v; change -(r.val:ℝ)< _ at e; change _ < (r.val:ℝ) at t
 let u:Shard Gt:=⟨r.val+z,by rw [AddSubgroup.coe_add]; linarith⟩; let t':Shard Gt:=⟨r.val-z,by rw [AddSubgroup.coe_sub]; linarith⟩
 simp only
 rw [show f (↑(z:ℝ))=↑(thermal u) from ?_, show g (↑(z:ℝ))=↑(thermal t') from ?_, sally_land hx _ (thermal_pos u) _ (assigned_ground (thermal_pos t'))]; exact (c u t').1 -- tune
 all_goals first| simp only [f,R, u,t', g,thermal]  <;> push_cast <;> rfl
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
