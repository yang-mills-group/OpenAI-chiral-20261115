import YM.SU5.Reconstruction.AnglePath.Framing
/-! # angular prices on this law CP. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
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
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (P:Ramp)(e:RPos Y H V G P C a χ)(B:BoostBacking Y H V G C a χ)(W:Chat Y H V G P C a χ)
open CrossedFrame.Cardio _root_.YM.ConePrice.Storm.StepVoucher
local notation "S"=> SpinOn Y H V G C a χ P e
local notation "G₁" => Domain Y H G false (aperture P)
local notation "H₀" => Domain Y H G false (northD P)
local notation "U"=> audition Y H V G C a χ P P.a (stocks_a P)
local notation "Z"=> audition Y H V G C a χ P P.b (stocks_b P)
local notation "M"=> motor Y H V G C a χ B S (Oriented.rotateAB P)
local notation "R"=> retina Y H V G C a χ P e B
local notation "K₁"=> profile Y H V G C a χ P W
open Schedule OS.Semigroup
open CrossedFrame.Cardio.Bank
-- coordinate purchase. ALL calendar spacings of real Mark in this calibration. Coordinate frame at Clock v with original a,b.
noncomputable def cruise (P:Ramp)(u:ℝ)(x:RSpace): RSpace:= fun i=> if i=P.a then Bank.tau (x P.a) (x P.b) u else if i=P.b then Bank.xi (x P.a) (x P.b) u else x i
lemma cruise_left (u:ℝ)(x:RSpace): cruise P u x P.a= Bank.tau (x P.a) (x P.b) u:=by simp [cruise]
lemma cruise_right (u:ℝ)(x:RSpace): cruise P u x P.b= Bank.xi (x P.a) (x P.b) u:=by simp [cruise,P.cross]
lemma cruise_else (u:ℝ)(x:RSpace)(i:Axis)(v:i≠P.a)(w:i≠P.b): cruise P u x i=x i:=by simp [cruise,v,w]
lemma cruise_add (u:ℝ)(x y:RSpace): cruise P u (x+y)=cruise P u x+cruise P u y:=by
 ext1 i; by_cases v:i=P.a; · subst i; simp [cruise,tau]; ring
 by_cases w:i=P.b; · subst i; simp [cruise,xi,v]; ring
 simp[cruise,v,w]
-- syntax columns! fix
noncomputable def asteroid(x:RSpace): E4:= Picket.lee P.a P.b (WithLp.toLp 2 x)
lemma wake(x:RSpace): asteroid P x P.a=0∧ asteroid P x P.b=0:=Picket.lees P.cross (WithLp.toLp 2 x)
abbrev peer (x:RSpace): OS.Cross P.a:= ⟨asteroid P x,(wake P x).1⟩
lemma capCast (x:RSpace)(u:ℝ): diameter (a:=P.a) (cruise P u x)= peer P x+(xi (x P.a) (x P.b) u) • Picket.cross P.a P.b P.cross:= by
 apply Subtype.ext; ext1 i; by_cases a:i=P.a
 · subst i; have h(X: OS.Cross P.a): X.val P.a=0:= X.property; rw [h (diameter _),h]
 rw [diameter_at _ _ a]
 by_cases b:i=P.b
 · subst i; rw [cruise_right]; change _=(asteroid P x P.b)+ _ * basis P.b P.b; rw [(wake P x).2]; simp
 rw [cruise_else _ _ _ _ a b]; change _= asteroid P x i+ _* basis P.b i; simp [asteroid,Picket.lee,Picket.head,a,b]
-- analytic identity.Rotation Θ_diag expands by REAL sqrt2.
lemma mid_rate(x:RSpace): cruise P (1/2) x P.a = (Real.sqrt 2/2)*(x P.a+x P.b) :=by
 rw [cruise_left]; unfold Bank.tau Bank.cs Bank.sn; rw[show Real.pi * (1/2)/2=Real.pi/4 by ring, Real.sin_pi_div_four, Real.cos_pi_div_four]; ring
-- robust for any clock. Add shoulder.
lemma route_now {H':Hilbert}(S':OS.Semigroup H' P.a)(x:RSpace)(u:ℝ): Schedule.route S' (cruise P u x)= Organ.chart S' P.cross (x P.a) (x P.b) (asteroid P x) u:= by
 unfold Schedule.route Organ.chart; rw [cruise_left, capCast,S'.independent,S'.space]
 rw [show Picket.trans S' (asteroid P x)= S'.U (peer P x) from translation S' (peer P x)]; exact ContinuousLinearMap.comp_assoc _ _ _
lemma cruise_zero(x:RSpace): cruise P 0 x=x:=by
 ext i; by_cases h:i=P.a; · simp [cruise,h,Bank.tau,Bank.cs,Bank.sn]
 by_cases e:i=P.b; · subst i; simp [cruise,h,Bank.xi,Bank.cs,Bank.sn]
 simp [cruise,h,e]
lemma joint_routes {X:Hilbert}(Q:OS.Semigroup X P.a)(u v:RSpace)(x:0≤ u P.a)(z:0≤ v P.a) : Schedule.route Q (u+v)=Schedule.route Q u * Schedule.route Q v:=by
 have ht: @diameter P.a (u+v)= (diameter u)+(diameter v):=by apply map_add (OS.Semigroup.SEP P.a) (WithLp.toLp 2 u) (WithLp.toLp 2 v)
 ext1 b; change route Q _ b=route Q u (route Q v b); simp only [Schedule.route, Pi.add_apply, Real.toNNReal_add x z, ht, Q.space, Q.time, ContinuousLinearMap.comp_apply]; exact congrArg (Q.E ((u P.a).toNNReal)) (DFunLike.congr_fun (Q.independent ((v P.a).toNNReal) (diameter u)) (Q.U (diameter v) b))
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
