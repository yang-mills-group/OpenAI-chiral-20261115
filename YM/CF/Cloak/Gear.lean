import YM.CF.Cloak.Stick
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
open scoped Classical
variable {X₂:Support f}{U₀:Config G f}{A:Finset (Cell f)}{F:Forest S.ratio}{s:ℝ}
open Atala
section
abbrev rateN(j:ℕ):ℕ:=2*(j+1)*50^4*Fintype.card PlaqAxes
lemma pack_y (X:Support f): (costA X).card ≤ X.card * 50^4 * Fintype.card PlaqAxes:=by
 let Z:=halo 10 X; have hp: Z.card ≤ X.card*50^4:=(Corona.halo_size X 10).trans (Nat.mul_le_mul_left _ (pow_le_pow_left' (by norm_num : 10+(10:ℕ)+1 ≤ 50) _)) -- tune nat powers
 have hh:costA X⊆ Z×ˢFinset.univ:=by
    intro i t; obtain ⟨j,p,z⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp t).2); exact mem_product.mpr ⟨halo_spec.mpr ⟨j,p,(separation_comm ..).trans_le (le_trans (Work.E01.sep_touched i j z) (by decide))⟩,mem_univ _⟩
 exact (card_le_card hh).trans (by rw [card_product]; exact Nat.mul_le_mul_right _ hp)
lemma pill (a n:ℕ)(F:ℝ)(h:m ≤ F)(q:Chi)(σ:ℝ)(hs:0<σ):∃ C D:ℝ,0≤C∧0≤D ∧∀{f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](V:RG.Atom G a)(U:E→ Config G f)(x:E)(i:Site f)(t:ℝ)(A:Finset (Cell f)), 0<t→t≤1 → Trow U x (F*t) n→(∀ j,Tender (fun y=>faceValue (U y) j) x (F*t) n) → HeldT U A x →
 let D0:= (zest n*priceK n (rateN V.length) C)* (D*t^a*V.budget σ)
 Allows n (lush_k q V A t i∘ U) x D0 ∧ ((∀ j∈ costA (V.footprint i) \ A, Pressure.toll (U x) j≤t) → Allows n (peer_k V A t i∘ U) x (D*t^a*V.budget σ)):=by
 obtain ⟨C,hC,H⟩:=bright_k q n F h; obtain ⟨D,hD,H'⟩:=mature a n F h σ hs
 refine ⟨C,D,hC,hD,@fun f E _ _ V U x i t A p u g hT hp=>?_⟩; intro Q
 let X:=V.footprint i; let r:=east q X A t ∘ U; have he:=H t U X A x p hp fun i v=> hT i; have hJ:0 ≤ D*t^a*V.budget σ:=by unfold RG.Atom.budget RG.Atom.magnitude; positivity
 constructor
 · by_cases v:x∈tsupport r
   · refine (allot he.1 (H' t V i U x p u g hT (he.2 v))).mono ?_; let a:= (costA X).card; change zest n * priceK n a C *_ ≤ _; have hz : 0 ≤ zest n:= (zpos n).trans' zero_le_one; have ha:a ≤ rateN V.length:=(pack_y X).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Extra.Iteration.Shapes.steps V i))); unfold Q priceK; gcongr
   have hi:0 ≤ Q:=by unfold Q; exact mul_nonneg (mul_nonneg ((zpos n).trans' zero_le_one) (by unfold priceK; positivity)) hJ
   apply (allows_const x (v:=(0:ℝ)) (by rw [norm_zero]; exact hi)).germ; filter_upwards [notMem_tsupport_iff_eventuallyEq.mp v] with y hy; unfold lush_k; change 0=r y*_; rw [show r y=0 from hy,zero_mul]
 intro z; have ht :∀ᶠ y in 𝓝 x,polP t (U y) X A ↔ polP t (U x) X A:= by refine hp.mono fun y h=>forall_congr' (fun i=>imp_congr_right fun z=>?_); rw [Pressure.toll,h i (mem_inter.mp z).1]; rfl
 by_cases b:polP t (U x) X A
 · exact (H' t V i U x p u g hT ((pol_g t (U x) A X z).mpr b)).germ (ht.mono fun y hp=> (if_pos (hp.mpr b)).symm)
 exact (allows_const x (v:=(0:ℝ)) (by simpa using hJ)).germ (ht.mono fun y hp=>(if_neg (mt hp.mp b)).symm)
end
end bound
end YM.CF.Cloak
