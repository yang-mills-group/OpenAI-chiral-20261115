import ExactRunning.Dyne.Cursor
/-!
# Projecting the joint profiles

Default melody for diagonal variations on the lifted fine+frame,
coarse via plain input. Also one using instead the predicted field
(at first order) for the coarse links.
`z_guard` transports the Ward identity `thrust` in a form holding
even against the cross leg (vary the coarse link independently).
Hence `z_deviation`: second Taylor coefficients in momentum of joint
cost Melodies invariant under the switch from default to predicted.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def accompany (A : Phase ι →ₗ[ℂ] Phase ι) : Phase ι→ₗ[ℂ] Phase (Duet ι) :=
  mix.comp (A.prod LinearMap.id)

def withLeg (L : Corn (Co m ι) →L[ℝ] Corn (Co m ι)) : 
    Corn (Co m ι) →L[ℝ] Corn (Co m (Duet ι)) :=
  (zipper _ _ _).comp (L.prod (ContinuousLinearMap.id ℝ _))

lemma accompany_turns {A : Eye ι ι} {W : Corn (Co m ι) →L[ℝ] Corn (Co m ι)}
    (h : Turns A W) :
    Turns (accompany ∘ A) (withLeg W) := by
  obtain ⟨J,a,b⟩ := h.basis
  refine ⟨tie.comp (J.prod LinearMap.id), ?_, ?_⟩
  · intro v
    change tie (J (axes v),axes v) = axes (tie (W v,v))
    rw [axes_tie,a]
  intro i q p v
  change tie (J (tune i v), tune i v) = tune i (mix (A q v,v))
  rw [tune_mix,b i q p]

abbrev defaultArm (G : Gauge) :=
  accompany (LinearMap.id (R:=ℂ) (M:=Phase (Entry G)))

namespace BlockTie
variable (X)

abbrev expected (p : Momentum) := accompany (Matrix.toLin' (X.result p))
abbrev both (G : Gauge) (m : Side) :=
  withLeg (ContinuousLinearMap.id ℝ (Link G m))

variable {r : ℝ}

def zK (r : ℝ) := (ridge r).run X.zScene
def highK (r : ℝ) := (ridge r).run X.hScene
def zPaid (r : ℝ) := wind (fun _=> defaultArm G) (X.zK r)
def zNext (r : ℝ) := wind X.expected (X.zK r)
def hPaid (r : ℝ) := wind (fun _=> defaultArm G) (X.highK r)
def hValue (r : ℝ) (i) := rQuad (X.hPaid r i)

def zPlays (h : 0<r) : Playing (ridge r) (X.zCook r) (X.zK r) :=
  Playing.through (X.z_scenes h) (X.z_data h)
def hPlays (r : ℝ) : Playing (ridge r) (X.hCook r) (X.highK r) :=
  Playing.through (X.h_scenes r) (X.h_data r)

theorem z_song (h : 0<r) (i) : Melody X.lo i (fun m => X.zLaw m r) (X.zPaid r i) :=
  (X.zPlays h).windy (L:=both G) (A:=fun _=> defaultArm G) (fun _ _ => accompany_turns (turns_id ..))
    i contDiff_const

theorem h_song (r : ℝ) (i) : Melody X.lo i (fun m => X.hiLaw m r) (X.hPaid r i) :=
  (X.hPlays r).windy (L:=both G) (A:=fun _=> defaultArm G) (fun _ _ => accompany_turns (turns_id ..))
    i contDiff_const

theorem z_reprise (h : 0<r) (i) : Melody X.lo i (fun m => X.zFore m r) (X.zNext r i) := by
  exact (X.zPlays h).windy (L:=fun m=>withLeg (X.castLow m)) (A:=X.expected)
    (fun m _ => accompany_turns (X.predicts _))
    i
    (((Pairing.mix (α:=Entry G) (β:=Entry G) (R:=ℂ)).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      ((Play.smmul (ode_poster X.runup I.house (Ode.magnetic (ridge r)))
         (contDiff_const (c:=Pi.single (stripe i) 1))).prodMk (contDiff_const (c:=Pi.single (stripe i) 1))))

theorem z_guard (h : 0<r) : 
    Lateral (ridge r) (X.zK r) (defaultArm G) := by
  refine (X.zPlays h).lateral (lo:=X.lo) (L:=both G) (fun _ _=>accompany_turns (turns_id ..)) ?_
  intro m hm z hz
  obtain ⟨T⟩ := X.test hm
  let x := gradientA G m z
  let y := (fderiv ℝ X.plait 0) x
  have he := X.thrust X.stable_zero T.high_unit (X.z_safe h _) _ hz y
      (by
        unfold y
        rw [X.plait_fine]
        exact X.send_high ((Latitude.preserves _).mpr hz))
      (T.plait_legal x)
  let f (v : Box G m) := (outer _ _ v,X.plait (inner _ _ v))
  have hx := X.read_flex r (outer G m) (inner G m) (inner _ _).continuous.continuousAt (map_zero _)
  have hf : X.zCook r m =ᶠ[𝓝 0] X.zEnergy r ∘ f := hx.symm
  have hp : ContDiffAt ℝ ω X.plait (inner G m 0) := by rw [map_zero];exact X.plait_analytic
  have ha : HasFDerivAt f ((outer G m).prod ((fderiv ℝ X.plait 0).comp (inner G m))) 0 := by
    simpa only [map_zero] using!
      ((outer G m).hasFDerivAt.prodMk
        ((hp.differentiableAt (by simp)).hasFDerivAt.comp 0 (inner G m).hasFDerivAt))
  have ha' := (X.z_flat (X.z_safe h m)).bend
    (show ContDiffAt ℝ ω f 0 from (outer G m).contDiff.contDiffAt.prodMk
      (hp.comp _ (inner G m).contDiff.contDiffAt))
    (by simp [f,X.plait_zero])
  intro u
  rw [Work.F05.bend_congr hf, ha',ha',ha.fderiv]
  exact he _

lemma result_change (i : G.ColorIndex) (y : Track) (j) :
    Cost (fun t=> ((X.result (axes (t•y))) *ᵥ Pi.single (stripe i) 1 -
                       (Pi.single (stripe i) 1:Phase (Entry G))) j) := by
  simp only [result,sub_mulVec,one_mulVec,smul_mulVec,
    sub_right_comm (_:Phase (Entry G)),sub_self,zero_sub,← smul_neg,Pi.smul_apply]
  exact (tax_ray I.B I.strip I.house (stripe i) j y).const_smul_left X.kernel.penalty⁻¹

lemma arm_change (i : G.ColorIndex) (y : Track) (j : Du G) :
    Cost (fun t=> (X.expected (axes (t•y)) (Pi.single (stripe i) 1) -
                 defaultArm G (Pi.single (stripe i) 1)) j) := by
  cases j with
  | inl j => exact X.result_change i y _
  | inr j =>
    change Cost (fun _ => _ - _)
    exact Asymptotics.isBigO_zero .. |>.congr_left fun _ => (sub_self _).symm

theorem z_deviation (h : 0<r) (i) : 
    Touch (X.zNext r i) (X.zPaid r i) := by
  refine Touch.on_cut (X.z_reprise h i).smooth.continuous.continuousAt
    (X.z_song h i).smooth.continuous.continuousAt ?_
  have q := X.zPlays h
  let K := X.zK r
  let e : Phase (Entry G) := Pi.single (stripe i) 1
  let x := defaultArm G e
  let f t := X.expected (tilt 0 t) e
  let g t := X.expected (-tilt 0 t) e
  have hx : Inert K (tilt 0 0) x x := tilt_zero 0 |>.symm ▸ Lateral.zero (X.z_guard h) q.score i
  have s := q.score (Ode.magnetic _)
  refine (shake (x:=fun _=>x) (y:=fun _=>x) (u:=fun t=>g t - x) (v:=fun t=> f t-x)
    ?_ tendsto_const_nhds tendsto_const_nhds ?_ (X.arm_change i _) hx).congr_left ?_

  · exact continuousAt_pi.mpr fun i=>continuousAt_pi.mpr fun j=>(s i j).continuous.continuousAt
  · intro k
    simpa only [smul_neg,axes_flip] using! X.arm_change i (-(Lattice.step (0:Axis))) k
  · intro t; rw [add_sub_cancel,add_sub_cancel]
    rfl

end BlockTie
end ExactRunning
