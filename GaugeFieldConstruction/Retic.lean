import GaugeFieldConstruction.Ontic
import GaugeFieldConstruction.Nocta
import GaugeFieldConstruction.Gin
set_option autoImplicit false
set_option maxHeartbeats 400000
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
open Hake TableF Boom FlightFlux Tap Axon
variable {c n:Side}{e k:ℕ}
-- any lifted-root cab
abbrev sumπ (x:SM c→ℝ)(p q:Prism.Rock c):= ∑ i:SU.Slot,∑ j:SU.Slot,x ((p,i),(q,j))
abbrev kark (x:SM c→ℝ)(k:ℕ)(p q:Prism.Rock c):= ∑ i:SU.Slot,∑ j:SU.Slot,(Pi.single (Haro.tray (p,i) (q,j)) ((k+1:ℝ)*(Haro.horn*sumπ x p q)):Raid (Dwell c))
abbrev ΔTax(x:SM c→ℝ)(k:ℕ):=∑ p:Prism.Rock c,∑ q:Prism.Rock c,kark x k p q
-- prism power-oriented branch path unit. line screen
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)}
variable (A:BudgetPoint)(o:Skye.Seat (mid N B))(V:SM (mid N B)→ℝ)(W:tangD (mid N B)→ Op (Single (mid N B)))(C:Support (Domain N B))(p:∀ i j:Single (mid N B),Signs A o (fun z=>W z i j) (V (i,j)))(h: o∈ C)(g:Seat (mid N B)→SU.E)(X:ℝ) (u:A.threshold=temp X)
include p g h u S
lemma ripples (w:ℕ) : Woody A.order (fun i=> InjectPH g (W (temp X • lineP A o C w i))) 0 (ΔTax V A.order):=by
 let T:= lineP A o C w; let J (p q:Rock (mid N B))(z:tangD (mid N B)):=frame_w (N:=N) (B:=B) (W (temp X • T z)) p q
 let E1 (p q:Rock (mid N B))(z:tangD (mid N B)):=star (putX g p)*J p q z*putX g q; let F (p q:Rock (mid N B))(i j:SU.Slot)(z:tangD (mid N B)):= E1 p q z i j • gateY (p,i) (q,j);
 have hZ(x:SM (mid N B)):0≤ V x:=(p x.1 x.2).grade;
 have ht(a b: Rock (mid N B)): Allows A.order (E1 a b) 0 (Haro.horn*sumπ V a b):=by
    refine ship_x _ _ (SU.matter _).property (SU.matter _).property _ ?_; have hp : ∀ i j:SU.Slot, Allows A.order (fun z=> J a b z i j) 0 (sumπ V a b):=by
       intro i j; exact (peseta (p (a,i) (b,j)) X C u h w).mono ((single_le_sum (s:=univ) (f:=fun j:SU.Slot=>V ((a,i),(b,j))) (fun l _=>hZ _) (mem_univ j)).trans (single_le_sum (s:=univ) (fun i (_:i∈(univ:Finset SU.Slot))=>sum_nonneg (fun l (_:l∈(univ:Finset SU.Slot))=>hZ ((a,i),(b,l)))) (mem_univ i)))
    have hz:0 ≤ sumπ V a b:= sum_nonneg (fun i _=> sum_nonneg (fun j _=> hZ _))
    simpa using (softL (J a b) hz 0 (fun i j=> by simpa only [Matrix.zero_apply,sub_zero] using hp i j)) -- if simpa default
 have hh(a b:Rock (mid N B)): Woody A.order (∑ i:SU.Slot,∑ j:SU.Slot,F a b i j) 0 (kark V A.order a b):=by
    refine Woody.sumV (fun i _=>Woody.sumV (fun j _=> ?_)); have h:= Rue.bare_p _ _ (cape_l _ (ht a b) i j)
    let O:Ride S:=⊥; let c':=(A.order+1:ℝ)*(Haro.horn*sumπ V a b); let Fx(z):=E1 a b z i j;
    have hb:= scroll_w c' Fx (a,i) (b,j) O O 0 (fun _=> h)
    simp_rw [mintX, Pi.single_eq_same] at hb; exact hb
 apply (Woody.sumV (S:=@univ (Rock (mid N B)) _) (fun i _=> Woody.sumV (fun j _=> hh i j))).germ; exact Eventually.of_forall fun i=>by simp only [Finset.sum_apply]; rfl
omit p g h u S
abbrev tape (A:BudgetPoint):= Haro.flavor^2*((A.order+1:ℝ)*Haro.horn)
private lemma karCut {n:Side}(o:Seat n)(V:SM n→ℝ)(B':ℕ)(g:B'=A.power)(h:ℝ)(p q:Prism.Rock n):
 joinV (Scree.tariff A o h) (kark V A.order p q)=(tape A)*(∑ i:SU.Slot,∑ j:SU.Slot,V ((p,i),(q,j))*tariff A o h (Haro.tray (p,i) (q,j))):=by
    let c:=tape A; let Q(i j:Single n):=V (i,j)*tariff A o h (Haro.tray i j)
    change _=c*∑ i:SU.Slot,∑ j:SU.Slot,Q (p,i) (q,j)
    unfold kark
    have ht(i j:SU.Slot)(x:ℝ):joinV (Scree.tariff A o h) (Pi.single (Haro.tray (p,i) (q,j)) x)=(Haro.amt B' o p q*h^2)*x:=by
       unfold joinV; simp only [Pi.single_apply,mul_ite,mul_zero,sum_ite_eq', mem_univ,↓reduceIte]; rw [show Scree.tariff A o h (tray (p,i) (q,j))=_ from Haro.rope B' o p q i j h A g]
    let K:ℝ:=(A.order+1:ℝ)*(Haro.horn*sumπ V p q); let Pz:=(Haro.amt B' o p q*h^2); rw [joinVsum];
    change (∑ i:SU.Slot,joinV (Scree.tariff A o h) (∑ j:SU.Slot, Pi.single (Haro.tray (p,i) (q,j)) K))= c* _
    rw [show (∑ i:SU.Slot,joinV (Scree.tariff A o h) (∑ j:SU.Slot, Pi.single (Haro.tray (p,i) (q,j)) K))= Haro.flavor*(Haro.flavor*(Pz*K)) from ?_]; swap
    · calc
          _= ∑ i:SU.Slot,∑ j:SU.Slot,Pz*K:=by refine sum_congr rfl fun i _=>?_ ; rw [joinVsum]; apply sum_congr rfl; exact fun j _=> ht i j _
          _ = _:=by simp only [sum_const,card_univ,nsmul_eq_mul,flavor]
    rw [show (∑ i:SU.Slot,∑ j:SU.Slot,Q (p,i) (q,j))= (sumπ V p q)*Pz from ?_]; swap
    · unfold sumπ; simp_rw [sum_mul]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_; unfold Q Pz; exact congrArg (fun x=>V ((p,i),(q,j))*x) (Haro.rope B' o p q i j h A g)
    unfold K c tape; ring

lemma ry_cost {n:Side}(o:Seat n)(V:SM n→ℝ) (y:A.power=3) (h:ℝ) : joinV (Scree.tariff A o h) (ΔTax V A.order)= tape A *(h^2 * WhX 3 V o):=by
 let B':= A.power; let o0:=o
 let P(p q:Rock n):= Hake.joinV (Scree.tariff A o h) (kark V A.order p q)
 let c:=tape A
 let Q(i j: Single n):= V (i,j)*tariff A o h (Haro.tray i j)
 have he(p q:Prism.Rock n):P p q=c*(∑ i:SU.Slot,∑ j:SU.Slot,Q (p,i) (q,j)):= karCut A o V A.power rfl h p q
 unfold ΔTax; rw [joinVsum];
 rw [show (∑ i:Rock n,joinV (Scree.tariff A o h) (∑ j:Rock n,kark V A.order i j))=∑ i:Rock n,∑ j:Rock n,P i j from sum_congr rfl fun i _=> joinVsum _ _]
 rw [←Wh_charge A y h V]
 change (∑ i:Prism.Rock n,∑ j,P i j)=c*(∑ i:Single n ×Single n,Q i.1 i.2); conv_rhs=> rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
 rw [mul_sum]; apply sum_congr rfl; intro p _
 have hu: (∑ i:SU.Slot, ∑ j:Single n,Q (p,i) j)= ∑ j:Prism.Rock n,∑ i:SU.Slot,∑ a:SU.Slot,Q (p,i) (j,a):=by
    rw [sum_comm (s:=@univ (Prism.Rock n) _ )]; apply sum_congr rfl; intro i _; exact Fintype.sum_prod_type _
 change (∑ j:Prism.Rock n,P p j)=c*(∑ i:SU.Slot, ∑ j:Single n,Q (p,i) j); rw [hu,mul_sum]; apply sum_congr rfl; exact fun i _=>he p i
end YM.CF.Oath
end
