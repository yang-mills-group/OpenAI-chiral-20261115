import GaugeFieldConstruction.Jury
import SatinThinShelter
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
variable {N:Side}{P:BudgetPoint}{o:Seat N}{K H:Vow.Pax N}{h a v k b d:ℝ}{r l L n:ℕ} (Tp:Ids N)(M:Tulip.Male)
-- canonical.Core.Clock. root halo (actual supplied).
open Ione QuadClock Beau Salt
open scoped YM.CF.Mew
section
variable (X:Scree.Hub N)
open TableF.Lenten.Layout.Fren -- tune
open Frugal
variable {I:Type}
lemma Stroke_L (U:Finset I)(A:I→ℂ)(E:I→ InkD N)(p t r:Aura N): Vow.stroke p t r (oV (∑ i∈U,A i • E i)) (oV (∑ i∈U,A i • E i)) = ∑ i∈U,A i • Vow.stroke p t r (oV (E i)) (oV (E i)):=by
 funext j D V; unfold Vow.stroke Vow.flick chasmR; by_cases h:j=r; swap; · rw [Pi.single_eq_of_ne h]; simp [Finset.sum_apply,Pi.single_eq_of_ne h]
 subst j; simp_rw [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same,Pi.sub_apply]; split_ifs <;> first| simp [oV,Finset.sum_apply]| simp_rw [oV,smul_sub, Finset.sum_apply, sum_sub_distrib,Pi.smul_apply]; simp -- nn
lemma ΩLeg (U:Finset I)(A:I→ℂ)(x:I→ℂ): χGhost N (∑ i∈U,A i • x i) =∑ i∈U,A i • χGhost N (x i):=by
 funext X; rw [Finset.sum_apply]; change (∑ i∈U,A i*x i) • (1:Cipher N)= ∑ i∈U,A i • (x i • 1:Cipher N); rw [Finset.sum_smul]; exact sum_congr rfl fun i _=>mul_smul ..
lemma Ω_Coin (U:Finset I)(A:I→ℂ)(x:I→ℂ): Ωχ X (∑ i∈U,A i • x i)=∑ i∈U,A i • Ωχ X (x i):=by
 funext i t z; unfold Ωχ; rw [ΩLeg U A x]; by_cases p:i=lagE X; swap; · unfold chasmR; simp [Finset.sum_apply,Pi.single_eq_of_ne p]
 subst i; unfold chasmR; simp_rw [Finset.sum_apply,Pi.smul_apply,Pi.single_eq_same,Pi.neg_apply]; simp [oV,Finset.sum_apply,←Finset.sum_neg_distrib] -- tune
lemma singleP_Z (U:Finset I)(A:I→ℂ)(E:I→InkD N): singleP X (∑ i∈U,A i • E i)=∑ i∈U,A i • singleP X (E i):=by
 funext i; unfold singleP; by_cases p:i=X; · subst i; simp [Finset.sum_apply]
 rw [Finset.sum_apply,Pi.single_eq_of_ne p]; simp [Pi.single_eq_of_ne p]
lemma Prop_W (Y:Scree.Hub N)(U:Finset I)(A:I→ℂ)(E:I→InkD N): Propulse (∑ i∈U,A i • E i) X Y=∑ i∈U,A i • Propulse (E i) X Y:=by
 unfold Propulse bury; apply Prod.ext; · rw [_root_.Prod.fst_sum]; simp
 rw [_root_.Prod.snd_sum]; apply Prod.ext; · rw [_root_.Prod.fst_sum]; exact Stroke_L ..
 rw [_root_.Prod.snd_sum]; simp
lemma locus_K (U:Finset I)(A:I→ℂ)(E:I→InkD N): locusH X (∑ i∈U,A i • E i)=∑ i∈U,A i • locusH X (E i):=by
 unfold locusH; apply Prod.ext; · rw [_root_.Prod.fst_sum]; exact singleP_Z ..
 rw [_root_.Prod.snd_sum]; change ((0 : Cusp N),(0:ℂ)) = _; simp
lemma ℓToll(U:Finset I)(A:I→ℂ)(E:I→InkD N)(p:∀ i∈U,∃ t:ℝ,PressB (KeyUp P) X (E i) h t)(w:0<h)(d:20<N.val)(q:P.order=6): splinter r X P h M (∑ i∈U,A i • E i)=∑ i∈U,A i • splinter r X P h M (E i):=by
 let Z:=Zhub X.val.1; let K:=KeyUp P; let T:=SealT X (∑ i∈U,A i • E i) K h M; let W(i:I):= SealT X (E i) K h M; let F:=∑ i∈U,A i • E i
 let L(i):= splinter r X P h M (E i)
 choose! B u using p
 have hu(i)(v:i∈U):PressB K X (A i • E i) h (‖A i‖*B i):= Floral.regular_scale _ (u i v)
 have hp:T=∑ i∈U,A i • W i:=by
    change SealT X (∑ i∈U, A i • E i) _ _ _ = _
    clear L T F
    induction U using Finset.induction_on with
    | empty=>rw [sum_empty,sum_empty,meter_zero]
    | insert i t y ih=>
       -- choose B in tactic dependent proof? clear internals
       rw [sum_insert y,sum_insert y,SeT_add w.le (hu i (mem_insert_self ..)) (prop_sum t (fun i=> A i • E i) (fun j=>‖A j‖*B j) _ _ _ (fun i v=>hu i (mem_insert_of_mem v))), BeaconΚ M (A i) (u _ (mem_insert_self ..)) w.le]
       exact congrArg (fun z:Waves=>A i • W i+z) (ih (fun j p=>u j (mem_insert_of_mem p)) (fun j p=> hu j (mem_insert_of_mem p))) -- tune
 have hg:splinter r X P h M F=∑ i∈U,A i • L i:=by
    let D:=incumb M X.val.1 d w (p:=K) le_rfl (show K.order≤6 from q.le); change D (ΓProj r T)=_; rw [hp,map_sum,map_sum]; apply sum_congr rfl; intro i v; rw [map_smul,map_smul]; rfl
 exact hg
lemma ℓExpand(U:Finset I)(A:I→ℂ)(E:I→InkD N)(p:∀ i∈U,∃ t:ℝ,PressB (KeyUp P) X (E i) h t)(w:0<h)(d:20<N.val)(q:P.order=6): ℓParcel r X P h M (∑ i∈U,A i • E i)=∑ i∈U,A i • ℓParcel r X P h M (E i):=by
 let Z:=Zhub X.val.1; let K:=KeyUp P; let T:=SealT X (∑ i∈U,A i • E i) K h M; let W(i:I):= SealT X (E i) K h M; let F:=∑ i∈U,A i • E i
 let L(i):= splinter r X P h M (E i)
 have hg:splinter r X P h M F=∑ i∈U,A i • L i:= ℓToll M X U A E p w d q
 have hx:χE X F=∑ i∈U,A i • χE X (E i):=by unfold χE F; rw [lifeSum,Finset.sum_apply]; apply sum_congr rfl; intro j _; rw [life_smul]; rfl
 change ℓParcel r X P h M F=_; unfold ℓParcel; simp only; rw [hg,hx]; apply Prod.ext
 · rw [_root_.Prod.fst_sum]; rw [ΩLeg U A (fun i=> χE X (E i))]
   let G(i:I):=χGhost N (χE X (E i))
   have he:F-((∑ i∈U,A i • G i)+∑ i∈U,A i • L i)=∑ i∈U,A i • (E i-(G i+L i)):=by simp_rw [smul_sub,smul_add,sum_sub_distrib,sum_add_distrib]; rfl
   rw [he,singleP_Z _ U A _,singleP_Z,←sum_add_distrib]; exact sum_congr rfl fun i _=> Eq.symm (smul_add ..)
 rw [_root_.Prod.snd_sum]; apply Prod.ext; · rw [_root_.Prod.fst_sum,Ω_Coin _ U A (fun i=> χE X (E i))]; rw [Stroke_L U A L (lagE X) (lagE Z) (lagE X),←sum_add_distrib]; exact sum_congr rfl fun i _=> Eq.symm (smul_add ..)
 rw [_root_.Prod.snd_sum]; rfl
end
end
end YM.CF.Oath
end
