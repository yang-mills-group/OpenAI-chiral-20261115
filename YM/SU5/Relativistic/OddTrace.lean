import YM.SU5.Relativistic.OddSlab
import YM.CF.Buffered.Trace

/-! Modified from Buffered.Trace to certify odd inputs (with phase). -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "U₊" => upperP (CSide m B)
local notation "Wμ" => wheel m B

private lemma twoSeams_mp2 (i) : MeasurePreserving (twoSeams i) ((Wμ).prod Wμ) Wμ := binary_w ..

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
variable (b : Budget B e d) (H : ScaleK a₁ a₂ W) (i : Axis) (cut : Foot m B)
include H b
section
local notation "T" => transfer p W clip β t u e i cut
local notation "κ" => kernelInside p W clip β t u e i cut
local notation "M" => slabTerm p W clip β t e
theorem at_Fermi (hu : 0 ≤ u) (n : ℕ) (f g : RP.Test m B) (hf : HalfOdd i f) (hg : HalfOdd i g) :
    (∫ x, slabTerm p W clip β t e (Complex.I • testProduct i f g) (hotEvol i cut u n) x ∂wheel m B) =
      kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)) := by
  let N := Tape m B (n+1)
  let a := tiedK m B i
  let F (x) (y) j k := κ n f j k (a x y y)
  let G (x) (y) j k := κ n g j k (a x y y)
  let P (j k : N) x := (∫ y, G x y j k ∂Wμ)*star (∫ y, F x y j k ∂Wμ)
  let Q := M (Complex.I • testProduct i f g) (hotEvol i cut u n)
  have hp := slabTerm_env p W clip β t b H _ _ (Girt.pole_w _ (fun x:A => Complex.I • x) (by fun_prop) (product_env i hf.envelope hg.envelope)) (Env.compact (hotEvol_cont i cut u n))
  have ht(j k:N):Envelope (P j k):=env_mult (marginalK_env p W clip β t u b H i cut g hg.envelope j k)
    (Girt.pole_w _ star continuous_star (marginalK_env p W clip β t u b H i cut f hf.envelope j k))
  have hx (x : X) : (∫ z, Q (RP.quill m B i (x,z)) ∂(Wμ).prod Wμ)= ∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), P j k x := by
    let A' j k (z:X×X) := G x z.1 j k * star (F x z.2 j k)
    have he (z:X×X) : Q (RP.quill m B i (x,z))=∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), A' j k z :=
      (sewnOdd p W clip β t u b H hu i cut n f g hf hg x z.1 z.2).trans (sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_comm ..)
    have hA (j k:N): Envelope (A' j k) := by
      have hz : Continuous fun y:X=> tiedK m B i x y y := (zoneA i x).comp (continuous_id.prodMk continuous_id)
      exact env_mult (Env.along (kernelInside_env p W clip β t u b H i cut n g hg.envelope j k) (hz.measurable.comp measurable_fst))
        (Girt.pole_w _ star continuous_star (Env.along (kernelInside_env p W clip β t u b H i cut n f hf.envelope j k) (hz.measurable.comp measurable_snd)))
    simp_rw [he]
    rw [integral_finsetSum]; swap
    · exact fun i _ => Env.integrableX (Env.total _ (hA i)) _
    refine sum_congr rfl fun j _ => ?_; rw [integral_finsetSum]; swap
    · exact fun i _ => Env.integrableX (hA j i) _
    refine sum_congr rfl fun k _ => ?_ ; unfold A' P; rw [integral_prod_mul (fun y=> G x y j k) (fun z => star (F x z j k))]; exact congrArg (_ * ·) (show (∫ z, star (F x z j k) ∂Wμ)=_ from integral_conj (𝕜:=ℂ) (f:=fun z=> F x z j k))
  unfold kernelTrace; rw [heard m B i Q (Env.integrableX hp Wμ)]
  simp_rw [hx]; rw [integral_finsetSum]; swap
  · exact fun i _ => Env.integrableX (Env.total _ (ht i)) _
  refine sum_congr rfl fun j _ => ?_; rw [integral_finsetSum]; swap
  · exact fun i _ => Env.integrableX (ht j i) _
  refine sum_congr rfl fun k _ => ?_
  -- use both seams and their measures
  simp_rw [kernelStar,Prod.swap_swap]
  change ∫ x,P j k x ∂Wμ = ∫ x, P j k (twoSeams i x) ∂(Wμ).prod Wμ
  have hv  := twoSeams_mp2 (m:=m) (B:=B) i
  exact (congrArg (fun ν:Measure X => ∫ x,P j k x ∂ν) hv.map_eq.symm).trans (integral_map hv.measurable.aemeasurable (ht j k).meas.aestronglyMeasurable)

theorem from_Fermi_layers (hu : 0 ≤ u) (f g : RP.Test m B) (hf : HalfOdd i f) (hg : HalfOdd i g) :
    Tendsto (fun n => kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)))
      atTop (𝓝 (heatNum p W clip β t e u (axisCut m B i cut) (Complex.I • testProduct i f g))) :=
  (slab_limit p W clip β t u b H i cut _ (Girt.pole_w _ (fun x:A => Complex.I • x) (by fun_prop) (product_env i hf.envelope hg.envelope))).congr
    (fun n => at_Fermi p W clip β t u b H i cut hu n f g hf hg)

theorem two_Fermi (hu : 0 ≤ u) (f : RP.Test m B) (hf : HalfOdd i f) :
    0 ≤ heatNum p W clip β t e u (axisCut m B i cut) (Complex.I • testProduct i f f) :=
  ge_of_tendsto' (from_Fermi_layers p W clip β t u b H i cut hu f f hf hf) fun _ =>
    trace_mul_star _ _ (transfer_env p W clip β t u b H i cut _ hf.envelope)
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.two_Fermi
