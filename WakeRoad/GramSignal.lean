import SU5SatinWakePhysicalGramNovember8

set_option autoImplicit false
set_option synthInstance.maxSize 28000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind
namespace GramSignal
open Regis Regis.Circuit Regis.Head.Brecht Ballad CF.Hiro Emu CF.Onyx
open Preparation.Yoke.Jewel Precision Exterior

lemma diet_scaling (R : ℕ) (o p : Cover) (L G : Twah.DirSpin) (N : Side)
    (j : ℕ) (M : Jill.Male) (h : Even N.val) :
    dietary R o p L G N j M = (R:ℂ)^3 * dietary 1 o p L G N j M := by
  unfold dietary
  rw [in_transcript,in_transcript,partial_price _ _ _ _ _ h,partial_price _ _ _ _ _ h, if_pos rfl, if_pos rfl]
  unfold bore
  rw [Matrix.smul_apply, Matrix.smul_apply, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

lemma dice_scaling (R : ℕ) (o p : Cover) (L G : Twah.DirSpin) (N : Side)
    (j : ℕ) (M : Jill.Male) (h : Even N.val) :
    diced R o p L G N j M = (R:ℂ)^6*diced 1 o p L G N j M := by
  unfold diced
  rw [diet_scaling R _ _ _ _ _ _ _ h,diet_scaling R _ _ _ _ _ _ _ h]
  ring


lemma gauge_scaling (R : ℝ) (W V : Staff) (N : Side) (M : Bed) :
    acePower SU.group (magnify M R (plaquette W.face.2) (plaquette V.face.2)
      (W.face.1-V.face.1) (More N)) =
      (R:ℂ)^4 * gaugeCoupon W V N M := by
  have ht : rimble (More N) M (wrap (More N) (W.face.1-V.face.1),plaquette W.face.2)
        (0,plaquette V.face.2) =
      rimble (More N) M (wrap (More N) W.face.1, plaquette W.face.2)
        (wrap (More N) V.face.1,plaquette V.face.2) := by
    rw [rimflare (More N) M (wrap _ _) 0 _ (sub_zero _),
      rimflare (More N) M (wrap _ _) (wrap _ _) _ (map_sub (wrap (More N)) W.face.1 V.face.1).symm]
  unfold acePower magnify gaugeCoupon
  rw [ht]; ring

variable (P : Spine) (f : ℕ → ℕ)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "iA" n:max=> P.period (P.projection.rows (f n))
local notation "kA" n:max=> P.cutoff (P.projection.columns (f n))
local notation "ν" s:max n:max=> side P.run (iA n) s
open _root_.YM.Stationary (Gaia)
abbrev stairs := (atTop : Filter ℕ).curry (atTop : Filter ℕ)

lemma steps_sides (h : StrictMono f) (s : ℕ) : Tendsto (fun n=> ν s n) atTop atTop :=
  (Papal.count_la Y s).comp ((P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop.comp h.tendsto_atTop)

variable {P f} {r:ℕ→ℕ} (u:∀ i,0<r i)(U:Tendsto r atTop atTop)
    (W V : ℕ → Staff) {a:Gaia}(e:a≠0)(p:Tendsto (fun s=>riseX (r s) ((W s).u-(V s).u)) atTop (𝓝 a))
set_option quotPrecheck false
local notation "spinScaled" => (fun sn : ℕ × ℕ => (r sn.1:ℂ)^6 *
    spinCoupon Y sn.1 (iA sn.2) (kA sn.2) (W sn.1) (V sn.1))
include u U e p
lemma spin_target (h:StrictMono f) (L G:Twah.DirSpin) (t:∀ s,(W s).spin=L) (v:∀ s,(V s).spin=G) :
    Tendsto spinScaled stairs (𝓝 (shotR L G (X:=a))) := by
  refine Metric.tendsto_nhds.mpr fun ε hε=> ?_
  rw [eventually_curry_iff]
  have hx:= travel_feast (Λ).K.j L G ((Λ).kJ.symm ▸ (by decide : 1≤(4:ℕ))) r U u (fun s=>(V s).u) (fun s=> (W s).u) p e (ε/2) (half_pos hε)
  filter_upwards [hx] with s t'
  filter_upwards [(steps_sides P f h s).eventually t'] with n g
  change dist ((r s:ℂ)^6 * diced 1 _ _ _ _ _ _ _) _ < _
  let Q:= (RootBook Y (iA n) (kA n) s).J.M
  have E:Even (ν s n).val:= Vale.val_e ..
  rw [t,v,←dice_scaling _ _ _ _ _ _ _ _ E]
  exact (g E Q).trans_lt (half_lt_self hε)
local notation "Q" s:max n:max=> (Λ).V.L.H ((Y).uv (kA n)-s)
local notation "gaugeScaled" => (fun sn:ℕ × ℕ => ((2*(r sn.1:ℝ):ℝ):ℂ)^4 * gaugeCoupon (W sn.1) (V sn.1) (ν sn.1 sn.2) (Q sn.1 sn.2))

omit p
lemma gauge_target (b : Tendsto (fun s=>riseX (2*(r s:ℝ)) ((W s).face.1-(V s).face.1)) atTop (𝓝 a)) (h:StrictMono f) (F D:PlaqAxes) (t:∀ s,(W s).face.2=F) (v:∀ s,(V s).face.2=D):
    Tendsto gaugeScaled stairs (𝓝 (speckleV F D SU.group a)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε=> ?_
  rw [eventually_curry_iff]
  have R: Tendsto (fun s : ℕ=> 2*(r s:ℝ)) atTop atTop:=
    (tendsto_natCast_atTop_atTop.comp U).const_mul_atTop (by norm_num)
  have S(s:ℕ):0< 2*(r s:ℝ):= mul_pos (by norm_num) (Nat.cast_pos.mpr (u s))
  have ht:= manifold F D (Λ).K.top.clip (Λ).V.W.parcel (Λ).K.width (zero_lt_one.trans_le (Λ).V.up) S R (U:= fun s=> (W s).face.1) (W:=fun s=> (V s).face.1) b e (ε/2) (half_pos hε) SU.group
  filter_upwards [ht] with s t'
  filter_upwards [(steps_sides P f h s).eventually t'] with n g
  have hc:= (Λ).V.L.roof ((Y).uv (kA n)-s)
  change dist (((2*(r s:ℝ):ℝ):ℂ)^4 * gaugeCoupon _ _ _ _) _ < _
  rw [← gauge_scaling,t,v]
  exact (g _ hc.1 (hc.2.1 _)).trans_lt (half_lt_self hε)

/-- One weight-five staff: matter current weight 3, gauge curvature weight 2.
Lattice spacings differ by 2; `r` is the number of matter spacings. -/
def staffWeight (r : ℕ) : ℂ := (r:ℂ)^3*((2*(r:ℝ):ℝ):ℂ)^2

variable {β:ℕ→ℝ}
include p
lemma wale_target (b : Tendsto (fun s=>riseX (2*(r s:ℝ)) ((W s).face.1-(V s).face.1)) atTop (𝓝 a))
    (g: Pooling Y (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β)
    (L G:Twah.DirSpin) (t:∀ s,(W s).spin=L) (v:∀ s,(V s).spin=G)
    (F D:PlaqAxes) (t':∀ s,(W s).face.2=F) (v':∀ s,(V s).face.2=D):
    Tendsto (fun sn:ℕ×ℕ=> (staffWeight (r sn.1))^2 *
      wale Y sn.1 (iA sn.2) (kA sn.2) (W sn.1) (V sn.1) (κFix β sn.1)) stairs
      (𝓝 (shotR L G (X:=a) * speckleV F D SU.group a)) := by
  let C (sn:ℕ×ℕ):ℝ := reachCost Y sn.1 (iA sn.2) (kA sn.2) (κFix β sn.1)
  have ht : Tendsto C stairs (𝓝 1) := by
    refine Metric.tendsto_nhds.mpr fun ε hε=> ?_
    rw [eventually_curry_iff]
    exact Eventually.of_forall fun s=> Metric.tendsto_nhds.mp (Gathering Y g s) ε hε
  have he:Tendsto (fun sn:ℕ×ℕ=> (spinScaled sn)*((C sn:ℂ)^2*gaugeScaled sn)) stairs
      (𝓝 (shotR L G (X:=a)*((↑(1:ℝ):ℂ)^2*speckleV F D SU.group a))) :=
    (spin_target u U W V e p g.up L G t v).mul (((Complex.continuous_ofReal.continuousAt.tendsto.comp ht).pow 2).mul (gauge_target u U W V e b g.up F D t' v'))
  rw [Complex.ofReal_one,one_pow,one_mul] at he
  apply he.congr
  rintro ⟨s,n⟩
  unfold wale staffWeight C
  dsimp only
  ring
#print axioms wale_target
#check @wale_target
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
