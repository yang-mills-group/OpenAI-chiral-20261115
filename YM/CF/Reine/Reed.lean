import YM.CF.Reine.Sail
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
abbrev ZoneB(T:Tube G S)(x:ℝ)(o: Support c)(U: Config G f)(V:Config G c): Prop := spanO T x∧ spanC T x ∧(∀ i∈ RG.flags (fiery G x S.patch.L) U, S.ratio.parent i∈o) ∧ RG.flags (temp x) V⊆o -- non-orient local
variable {o:Support c}(p:ZoneB T x o U V)(hp:0<fiery G x S.patch.L)
local notation "B₀"=>radiusB x
local notation "r₀"=>Stores.till x
local notation "t₀"=>fiery G x S.patch.L
local notation "E₀"=>temp x
omit p hp
lemma never_c{Y:Support c}{i j:Site c}(h:i∉halo r Y)(p:j∈Y): r < separation i j:= Nat.lt_of_not_ge fun t=>h (halo_spec.mpr ⟨j,p,separation_comm .. ▸ t⟩)
include p hp
lemma bill_x(i:Cell f)(h:S.ratio.parent i.1∉halo (B₀+10) o): king ∅ T.up T.high r₀ 1 t₀ U i=crown T.up T.high r₀ 1 t₀ U i:=by
 have he(a:Site f)(z:a∈ flags t₀ U):B₀ < separation i.1 a:=by
    have hN:= never_c h (p.2.2.1 a z); have ht:=Work.E04.parent_separation S.ratio i.1 a; omega
 exact crownK _ _ _ _ _ _ _ _ hp.le (supplies_n T.high _ _ hp.le p.1 _ _ he) (Or.inr (reign (Finset.Subset.refl _) _ (fun h=>by simpa using he i.1 h)))
omit hp
lemma kin_c {i:Cell c}(h:i.1∉halo B₀ o):king ∅ T.down T.low r₀ S.patch.L.val E₀ V i=crown T.down T.low r₀ S.patch.L.val E₀ V i:=by
 have he:= temp_nonneg x; exact crownK _ _ _ _ _ _ _ _ he (supplies_n T.low _ _ he p.2.1 _ _ fun j l=> never_c h (p.2.2.2 l)) (Or.inr (reign p.2.2.2 _ fun k=> h (halo_subset B₀ o k))) -- tune
lemma k_vis {i:Twin c}(h:i.1.1∉halo B₀ o): wV T r₀ E₀ ∅ V i=T.vision r₀ E₀ V i:=by
 have he:= temp_nonneg x; exact takes_q _ _ _ _ _ _ _ _ he (supplies_n T.low _ _ he p.2.1 _ _ fun j l=> never_c h (p.2.2.2 l)) (Or.inr (reign p.2.2.2 _ fun k=> h (halo_subset B₀ o k)))
omit p
lemma reachN (i:Co c Gain)(j:Twin c)(h:r < separation i.1 j.1.1): T.N r V i j=0:=by
 let R:=r; have hl k (h : k*S.patch.L.val ≤ R) : k ≤ R := le_trans (le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property) h
 have hf(u:Cover): Pressure.priced r S.patch.L.val V T.R.o i (Pressure.mesh j) u=0:=by
    unfold Pressure.priced; split
    next hv =>
       have hx : stop i.1 (route 0 u 1) = (Pressure.mesh j).1 := by rw [hv.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route i.1 0 u
       have he : separation i.1 (Pressure.mesh j).1 ≤ r := by rw [← hx]; exact (Work.E03.sep_walk (fun x : Site c=>x) Work.E03.sep_step ..).trans (hl _ hv.1)
       exact (h.not_ge he).elim
    rfl
 simp only [Tube.N,gk,Pressure.lane,hf,tsum_zero]
end
end YM.CF.Reine
