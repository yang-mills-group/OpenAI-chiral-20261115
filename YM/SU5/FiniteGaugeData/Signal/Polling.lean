import YM.SU5.FiniteGaugeData.Signal.Metropolis
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
/-! # Single curvature AC of first pane. -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.Frobenius ComplexConjugate Pointwise
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
namespace Showcasing
local notation "G"=> SU.group
local notation "E"=> SU.group.El
lemma along_one : (𝓝[≠] (1:SU.E)).NeBot:=by
 haveI:Nontrivial (G).Color:= yet_one.nontrivial_color; let A:= (G).Color; let F:Filter A:=𝓝[≠] (0:A); letI hF : NeBot F:=inferInstanceAs ((𝓝[≠] (0:SU.group.Color)).NeBot)
 have he : Tendsto (G).lieExp F (𝓝 (1:SU.E)):=by
    rw [← (G).mat_lieExp_zero]; exact (G).lieExp_cont.continuousAt.continuousWithinAt
 apply (tendsto_nhdsWithin_iff.mpr ⟨he,?_⟩).neBot -- tune
 filter_upwards [Eventually.filter_mono (show F ≤ _ from nhdsWithin_le_nhds) SU.group.plog_left, self_mem_nhdsWithin (a:= (0:SU.group.Color)) (s:={ (0:SU.group.Color) }ᶜ)] with x u v; intro h; have hl : SU.group.lieExp x=1:=h; rw [hl,Gauge.mat_one,Gauge.plog_one] at u; exact v (Set.mem_singleton_iff.mpr u.symm)
-- separate correction
lemma bare_prior (M: Side)(p:Face (Per M))(h:1<M.val): MeasurePreserving (fun x: Config SU.group M=> faceValue x p) (prior SU.group M) SU.group.probHaar:=by
 let f(x:Config SU.group M):=faceValue x p; have he: Measurable f:= (continuous_travel _ _).measurable
 refine ⟨he,Measure.ext_of_integral_eq_on_compactlySupported (fun g=>?_)⟩
 have hx: ∃ i: Edge (Site M), i∈ YM.Next.Rank.Axial.edges p:= by obtain ⟨x,⟨i,j⟩,q⟩:= p; exact ⟨_,(YM.Next.Rank.Axial.reads_four ..).2 (Or.inl rfl)⟩
 obtain ⟨i,v⟩:=hx
 rw [integral_map (f:=fun x=> g x) (φ:=fun x: Config G M=> faceValue x p) he.aemeasurable g.continuous.aestronglyMeasurable]; simpa using (YM.Next.Rank.Axial.pull_link («G»:=SU.group) h p i v g g.continuous (fun _=>1) continuous_const (fun _ _=> rfl))
lemma displacement (M:Side)(p:Face (Per (More M))): ∀ᵐ z∂city M, 0 < SU.group.chord (faceValue z.1 p):=by
 haveI : (𝓝[≠] (1:SU.E)).NeBot:= along_one; have H:= bare_prior (More M) p (by change 2 ≤ M.val*2; exact Nat.le_mul_of_pos_left 2 M.property); let hP: MeasurePreserving Prod.fst (city M) (prior G (More M)) := measurePreserving_fst; let W:= H.comp hP
 filter_upwards [W.quasiMeasurePreserving.ae (SU.group.probHaar.ae_ne 1)] with z v; let x:= faceValue z.1 p; apply lt_of_le_of_ne (SU.group.chord_nonneg _) fun hi=> v ?_; clear v; apply SU.group.mat_injective; rw [Gauge.mat_one]; rw [Gauge.chord,eq_comm,div_eq_zero_iff] at hi; exact sub_eq_zero.mp (norm_eq_zero.mp (hi.resolve_right (Real.sqrt_pos.mpr (by exact_mod_cast group.dimPos)).ne'))
end Showcasing
end YM.CF.Signal
#print axioms YM.CF.Signal.Showcasing.displacement
