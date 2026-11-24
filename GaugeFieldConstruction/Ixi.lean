import GaugeFieldConstruction.Caris
import GaugeFieldConstruction.Enmity
import GaugeFieldConstruction.Quail
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open Py.Riant Nor Lilt Larch
variable {I:Type}[LinearOrder I][Fintype I]{N B:Side}{p:BudgetPoint}{x a b h:ℝ}{V:Vow.Pax N} (Tp:Ids N)
lemma breadthENS {E:Type*}[AddCommMonoid E](y: Seat N)(f:Scree.Hub N→ E) : ∑ i∈univ.filter (fun i:Scree.Hub N=>y∈i.val.2),f i= ∑ j∈univ.filter (fun j:Aura N=>y∈j.val),∑ i∈ Ione.web0 j,f i:=by
 let T:=univ.filter (fun i:Scree.Hub N=>y∈i.val.2); let A:=univ.filter (fun j:Aura N=>y∈j.val)
 have ht:∀ i∈T,lagE i∈A:=fun i h=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
 rw [←sum_fiberwise_of_maps_to ht]; exact sum_congr rfl fun j h=>sum_congr (Finset.ext fun i=> ⟨fun p=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩,fun p=> mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,show y∈ i.val.2 from (show i.val.2=j.val from congrArg Subtype.val (show lagE i=j from (mem_filter.mp p).2)).symm ▸ (mem_filter.mp h).2⟩,(mem_filter.mp p).2⟩ ⟩) (fun i _=>rfl) -- tune
lemma ripeC (p₀:p.power=2)(t:p.order=6)(u:p.B=radiusB x)(h₀:Turf V)(g:0≤h)(q: ShelfK (SecW p g N) V p.B 3 b): ShelfK (SecX (KeyUp p) g N) (Ione.cast_E V Tp) p.B 2 (ωCost x * b):=by
 obtain ⟨W,A,H⟩:= (Wbank ..).mpr q; let Z:=ZPay x; have hx : 0 ≤ ZPay x:=by unfold ZPay; exact mul_nonneg (by positivity) pos_C
 let T:=ωCost x; have hy:0 ≤ T:= by unfold T ωCost; apply mul_nonneg _ hx; unfold reserveT coin_n stilK; positivity
 let E(i:Scree.Hub N):= Stick p i (pence_Q p W i); refine ⟨E,fun i=>?_, fun y=>?_⟩
 · have he:= Hope.longer3 p₀ (dare_L p V Tp h₀ g A i) g p.B; rw [t] at he; exact he -- tune
 apply le_trans _ (mul_le_mul_of_nonneg_left (H y) hy)
 change (∑ i∈univ.filter (fun i:Scree.Hub N=> y∈ i.val.2), _ ) ≤ _*_; rw [breadthENS, tallB, mul_sum]
 apply sum_le_sum; intro i v; let F:=W i *Trees.currency p.B 3 i.val; let B:=bassH i
 have hb : 0 ≤ B:=bassT _
 apply le_trans (sum_le_sum (g:=fun _=>B*(T*F)) (fun j w=>?_)); swap
 · have hk:lagE j=i:=(mem_filter.mp w).2; have he(i):0≤W i:=(A i).wage g; have hz:=stick_tariff p₀ t u j (B*W i) (mul_nonneg hb (he _)); apply le_trans (le_trans (le_of_eq ?_) hz) (le_of_eq ?_)
   · apply congrArg (fun a=> Tollup 2 p j*a); unfold E pence_Q; rw [hk]; apply congrArg (Stick p j); unfold B; ring
   unfold T F at *; change ωCost x * _=_; unfold Tollup; rw [show j.val.2=i.val from congrArg Subtype.val hk]; unfold Trees.currency; ring
 rw [sum_const,ore_D, nsmul_eq_mul]; change _ ≤ T*F; rw [←mul_assoc]; unfold B bassH; rw [mul_inv_cancel₀ (by exact_mod_cast Finset.card_ne_zero.mpr i.property),one_mul]
lemma inbound (q:Turf V)(g:0≤h)(p₀:p.power=2)(t:ShelfK (SecX (KeyUp p) g N) (Ione.cast_E V Tp) p.B a b) :ShelfK (SecW p g N) V p.B a (chi_f p.order*b) :=by
 obtain ⟨C,U,W⟩:=t; let H(i:Aura N):=∑ x∈Ione.web0 i,chi_f p.order * C x
 refine (Wbank ..).mp ⟨H,fun i=>?_,fun x=>?_⟩
 · have he: V i=∑ j∈Ione.web0 i,Vow.oV (cast_E V Tp j):=by
      rw [sum_congr rfl (fun j (t:j∈web0 i)=> (show Vow.oV (cast_E V Tp j) = bassH i • V i from ?_)), sum_const, ore_D]; swap
      · have he:lagE j=i:=(mem_filter.mp t).2; funext x; unfold Vow.oV cast_E; rw [he]; change bassH i • V i _=bassH i • V i _; exact congrArg _ (Eq.symm (q ..))
      rw [← Nat.cast_smul_eq_nsmul ℝ, bassH]; exact (smul_inv_smul₀ (by exact_mod_cast Finset.card_ne_zero.mpr i.property) _).symm
   let Q:= V i; -- rewriting all V i dangerous
   refine he ▸ ?_ -- tune he direction. likely replaces Sum only
   unfold H; apply Medal.sumP; intro j g'
   have h':j.val.2=i.val:=congrArg Subtype.val (show lagE j=i from (mem_filter.mp g').2); exact h' ▸ rimR (Hope.smallerP p₀ (U j) g) g
 apply le_trans _ (mul_le_mul_of_nonneg_left (W x) (show 0 ≤ chi_f p.order from spicy_f _))
 change _ ≤ _ * (∑ i∈univ.filter (fun i:Scree.Hub N=> x∈ i.val.2), _ ); rw [breadthENS,tallB, mul_sum]; apply sum_le_sum; intro i w; apply le_of_eq; unfold H; rw [sum_mul,mul_sum]; apply sum_congr rfl; intro j u; have hw:j.val.2=i.val:= congrArg Subtype.val (show lagE j=i from (mem_filter.mp u).2)
 change _= _ *(dra_k p.B a j.val.2*_); rw [hw]; unfold dra_k Trees.currency; ring
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
