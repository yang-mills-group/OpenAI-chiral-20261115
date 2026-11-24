import ExactRunning.Endpoints.Data
import ExactRunning.Scenes.Regular

/-!
# Sending mass to zero pointwise

With fixed real internal momentum (shade positive), derivative in the external parameter
depends continuously on mass at zero. This lets us read off the
singular estimates quite directly on punctured zones.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
variable {G : Gauge} {R : PathData G} {p : Clip} {m : Side} {F : KindF G}


def relaxed (μ : ℝ) (F : KindF G) : Scene (Entry G) :=
  (↑((1:ℝ)/2):ℂ) • tableau (massif G μ F) - tableau (coring G μ)

section
variable (G)
lemma coring_zero : coring G 0 = quarry G := by
  simp [coring,Film.plus,chisel,Film.weight]

variable {ι α β : Type}
private def Dead (K : Film ι α β) := K.tab = 0 ∧ K.spot = 0 ∧ K.arch = 0

private lemma stony_dead (i : Axis) :
    Dead (stony G 0 i) := by
  simp [Dead,stony,chisel,Film.weight,Film.pay]

  exact ⟨rfl,rfl,rfl⟩

private lemma granite_dead : Dead (graniteF G 0) := by
  unfold graniteF
  generalize List.finRange 4 = l
  induction l with
  | nil => rw [chore]; exact ⟨rfl,rfl,rfl⟩
  | cons i l ih =>
    simp [chore, Dead, Film.plus,(stony_dead G i).1, (stony_dead G i).2.1,
          (stony_dead G i).2.2, ih.1, ih.2.1, ih.2.2]

variable {G}
lemma massif_zero (F : KindF G) : massif G 0 F = granary G F := by
  simp [massif, Film.plus,(granite_dead G).1, (granite_dead G).2.1, (granite_dead G).2.2]

lemma relaxed_zero (F : KindF G) : relaxed 0 F = epScene F := by
  simp only [epScene, relaxed, massif_zero, coring_zero]

end

section
local notation "Y" => ℝ × ℝ  -- mass, external
variable {r : Momentum}

private lemma weight_live :
    ContDiffAt ℝ ω (fun y : Y => ((y.1^2:ℝ):ℂ)) 0 := by
  apply ContDiffAt.comp (g:=Complex.ofRealCLM) 0
  · exact Complex.ofRealCLM.contDiff.contDiffAt
  change ContDiffAt ℝ ω (fun y : Y => y.1^2) 0
  fun_prop
private lemma chisel_live (G : Gauge) (hr : star r=r) (hv : 0<shadeK r) :
    Livens (fun y : Y => chisel G y.1) 0 r := by
  have ha : Livens (fun y:Y => cinder G y.1) 0 r :=
    (Livens.of_play quarry_p zero_lt_one hr).plus
     (Livens.simple ((Memobic.park 1 _).scale weight_live))
  have he : IsUnit ((cinder G (0:Y).1).tab r).det := by
    simp only [cinder, Prod.fst_zero, Film.plus, Film.cardF,Pi.add_apply]
    rw [show (0:ℝ)^2=0 by norm_num,Complex.ofReal_zero,zero_smul,add_zero]
    exact quarry_unit r hr hv
  have hb : Livens (fun y : Y => chert G y.1) 0 r := (ha.back he).weight weight_live
  have hc := (hb.pay hb).pay hb
  exact ((hc.pay hc).pay hc).weight weight_live

private lemma granite_live (G : Gauge) (hr : star r=r) (hv : 0<shadeK r) :
    Livens (fun y : Y => graniteF G y.1) 0 r := by
  unfold graniteF
  generalize List.finRange 4 = l
  induction l with
  | nil =>
    simp only [chore]
    exact ⟨fun _ => Memobic.park 0 _, fun _ _ _ => Memobic.park 0 _, fun _ _ _ _ _ => Memobic.park 0 _⟩
  | cons i l ih =>
    have a := Livens.of_play (x:=(0:Y))
      (Play.current (ι:=Entry G) (Poster.web (dasher G i))) zero_lt_one hr
    have b := Livens.of_play (x:=(0:Y))
      (Play.rear (Play.current (ι:=Entry G) (Poster.web (dasher G i)))) zero_lt_one hr
    simp only [chore]
    exact ((b.pay (chisel_live G hr hv)).pay a).plus ih

lemma Endpoint.curve_stable (s : Endpoint p R F) (hr : star r=r) (hv : 0<shadeK r) (i j) :
    ContDiffAt ℝ ω (fun y : Y => relaxed y.1 F (tilt 0 y.2) r i j) 0 := by
  obtain ⟨σ,hσ,hp⟩ := s.played
  have a := Livens.of_play (x:=(0:Y)) (granary_green hp) hσ hr
  have a : Livens (fun y : Y => massif G y.1 F) 0 r := a.plus (granite_live _ hr hv)
  have b : Livens (fun y : Y => coring G y.1) 0 r :=
    (Livens.of_play quarry_p hσ hr).plus (chisel_live _ hr hv)
  have u : IsUnit ((massif G (0:Y).1 F).tab r).det := by
    rw [Prod.fst_zero,massif_zero]; exact s.floor _ hr hv
  have v : IsUnit ((coring G (0:Y).1).tab r).det := by
    rw [Prod.fst_zero,coring_zero]; exact quarry_unit _ hr hv
  let w : Slide (0:Y) 0 := ⟨fun y=>tilt 0 y.2, (tilt_smooth 0).contDiffAt.comp _ contDiffAt_snd, by simp⟩
  let z : Slide (0:Y) r := ⟨fun _ => r,contDiffAt_const,rfl⟩
  exact ((a.figure u i j w z).const_smul (↑((1:ℝ)/2):ℂ)).sub (b.figure v i j w z)

end

section
lemma param_deriv {g : ℝ × ℝ → ℂ} {x} (h : ContDiffAt ℝ ω g x) :
    ContDiffAt ℝ ω (fun w : ℝ × ℝ => deriv (fun t => g (w.1,t)) w.2) x := by
  refine ((h.fderiv_right (m:=ω) (by simp)).clm_apply (contDiffAt_const (c:=((0,1):ℝ × ℝ)))).congr_of_eventuallyEq ?_
  filter_upwards [h.eventually (by simp)] with w hw
  apply HasDerivAt.deriv
  have hx : HasFDerivAt g (fderiv ℝ g w) ((fun t => (w.1, t)) w.2) := (hw.differentiableAt (by simp)).hasFDerivAt
  exact hx.comp_hasDerivAt (f:=fun t => (w.1,t)) _ ((hasDerivAt_const ..).prodMk (hasDerivAt_id w.2))

lemma param_quad {g : ℝ × ℝ → ℂ} (h : ContDiffAt ℝ ω g 0) :
    ContDiffAt ℝ ω (fun μ => quad (fun t=>g (μ,t))) 0 := by
  change ContDiffAt ℝ ω (fun μ => (2⁻¹:ℝ) • flareY 2 (fun t=> g (μ,t))) _
  simp_rw [plunge_dive]
  exact ((param_deriv (param_deriv h)).comp (f:=fun z:ℝ => (z,0)) (0 : ℝ) (contDiffAt_id.prodMk contDiffAt_const)).const_smul _

end

def peeled (F : KindF G) (i : G.ColorIndex) (r : Momentum) :=
  quad (fun t => epScene F (tilt 0 t) r (stripe i) (stripe i))

lemma keel_relaxed (F : KindF G) (μ : ℝ) (x : Gaia) (i : G.ColorIndex) :
    keelRay (amena μ G F) i (exileE x) =
    quad (fun t => relaxed μ F (tilt 0 t) (tap x) (stripe i) (stripe i)) := by
  unfold keelRay strolls quad
  rw [Complex.real_smul]
  simp only [Complex.ofReal_inv,Complex.ofReal_ofNat,one_div]
  rfl

lemma Endpoint.tendsto_keel (s : Endpoint p R F) (x : Gaia)
    (hv : 0<shadeK (tap x)) (i : G.ColorIndex) :
    Tendsto (fun μ => keelRay (amena μ G F) i (exileE x))
      (𝓝[>] (0:ℝ)) (𝓝 (peeled F i (tap x))) := by
  simp_rw [keel_relaxed]

  unfold peeled
  rw [← relaxed_zero]
  exact (param_quad (s.curve_stable (tap_real _) hv (stripe i) (stripe i))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end ExactRunning
