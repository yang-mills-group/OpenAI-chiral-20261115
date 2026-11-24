import GaugeFieldConstruction.Growth
import GaugeFieldConstruction.Mell
import GaugeFieldConstruction.Enmity
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 120000
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
section
open Py.Riant
open CoeffArc
open Roots.Connect TableF Lenten Layout Fren
variable {I J U Λ Ω:Type}[LinearOrder I][Fintype I][LinearOrder J][Fintype J][LinearOrder U][Fintype U]{N B:Side}
local notation "G7"=> mid N B
variable (d:U→ℕ)(σ:I→Seat (mid N B))(x:U→Seat (mid N B))(κ:I→ℕ)(C:U→ Key I)
variable (F:Key I→Vow.Pax (mid N B))(H:Key J→ Vow.Pax (mid N B))
 (s:Sweep (mid N B))(t:J→Seat (mid N B))(y:U→Seat (mid N B))(μ:J→ℕ)(A:U→Key J)
  (p:BudgetPoint)(Lk:Side)(ℓ h:ℝ)(M:Tulip.Male)(T Q:Ids (mid N B))
open QuadClock Salt
variable {W1 W2:ℝ}
-- Vg.Sheet.strong schedules. root support & key. mask ζ.
structure StripK (p:BudgetPoint)(σ:I→ Seat G7)(F:Key I→Vow.Pax G7)(h:ℝ):Prop where
   bill (z:Key I)(t:z∈hill I): Turf (F z)
   art (x:Aura G7)(y:Orbit G7): River fun z=> F z x y
   fee(i:I): SiteFee p (debit F i) (σ i) h
abbrev ζTippy (F:Key I→Vow.Pax G7)(z:Key I): Vow.Pax G7:=∑ i:I, z i • debit F i -- tune no Junk
abbrev PressRow (P:BudgetPoint)(M:Tulip.Male)(d:I→ℕ)(σ:I→Seat (mid N B))(h:ℝ)(F:Key I→Vow.Pax (mid N B))(L:Side)(i:I): Oath.Zone (mid N B):= Brow (RootPrice P (σ i)) M h P (debit F i) L (d i)
abbrev BandPlot{W:Type}[AddCommMonoid W][Module ℂ W](F:I→W)(C:Key I):=∑ i:I,C i • F i
abbrev OnPlot (d:U→ℕ)(σ:I→Seat G7)(x:U→Seat G7)(κ:I→ℕ)(C:U→Key I):Prop:= Tours (fun i=>(σ i,κ i)) (fun j=>(x j,d j)) C
abbrev RiverMate (C:Aura G7→ Orbit G7 → Cipher G7):=ℝ -- trim
abbrev Λpay (s:Sweep G7):ℂ→+*ℂ:= if wageZ s then starRingEnd ℂ else RingHom.id ℂ
abbrev Turk (S:Sweep G7): Cipher G7 →L[ℝ] Cipher G7:= (suit_Y S).toLinearMap.toContinuousLinearMap
lemma inkPay (i:ℂ): Λpay s i=Spire.payZ s i:=by unfold Λpay Spire.payZ; cases wageZ s <;> simp [cSignX]
lemma inkC (i:ℂ)(x: Cipher G7): Turk s (i • x)=Λpay s i • Turk s x:=by rw [inkPay]; exact scar_y ..
lemma inkR (i:ℝ): Spire.payZ s (i:ℂ)=(i:ℂ):=by unfold Spire.payZ; cases wageZ s <;> simp [cSignX] -- tune
lemma rowSpot {W:Type}[AddCommMonoid W][Module ℂ W](F:I→W)(z:Key U) : BandPlot F (SpotQ C z)=BandPlot (fun i=>BandPlot F (C i)) z:=by
 unfold BandPlot SpotQ; simp_rw [Finset.sum_apply,Finset.sum_smul,Finset.smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; exact mul_smul ..
variable {x y}
variable (v:100<(mid N B).val)(e:h>0)(hp:p.order=6)(hv:CapeLen (mid N B) p Lk.val) -- binder macro fix expand
variable (oF:StripK (N:=N) (B:=B) p σ F h)(oH: StripK (N:=N) (B:=B) p t H h)
variable (wL: fortK ≤ Lk.val)(fw:y=sh s ∘ x)(u:OnPlot (N:=N) (B:=B) d σ x κ C)(a:OnPlot (N:=N) (B:=B) d t y μ A) -- uses N implicit
variable (ω':∀ᶠ z:U→ℝ in 𝓝 0,passingFee (mid N B) s (F (LegQ C z)) (H (LegQ A z)))
lemma root_d (o:Seat G7): moveHub s (RootPrice p o)=RootPrice p (sh s o):=by
 refine Subtype.ext (Prod.ext rfl ?_)
 change Finset.map _ _=_; change actY s (Lattice.halo _ {o})=Lattice.halo _ {sh s o}; unfold actY sh; rw [← sitU,←paysT,map_singleton]; rfl -- tune
include oF u
local notation "Πν"=> (fun i:I=>(σ i,κ i))
local notation "T9"=> (fun j:U=>(x j,d j))
abbrev rootsSub (σ:I→Seat G7)(w:Seat G7)(κ:I→ℕ)(d:ℕ): Finset I:=Entry (fun i=>(σ i,κ i)) (w,d)
variable {Lk M}
lemma Row_ξ (k:U)(i:Aura G7)(V:Orbit G7): Pica Πν T9 C (fun z=> F z i V) [k]= BandPlot (debit F) (C k) i V:=by
 let P(j:I):= C k j • debit F j i V; unfold Pica Jetd; rw [Jetd.aux]; unfold BandPlot; simp_rw [Finset.sum_apply,Pi.smul_apply]; refine sum_subset (f:=P) (subset_univ _) ?_ -- tune defeq Jetd.aux nil
 intro j _ e; unfold P; rw [u _ _ e,zero_smul]
lemma OnTrail (k:U): SiteFee p (BandPlot (debit F) (C k)) (x k) h:=by
 let T:=rootsSub σ (x k) κ (d k); let B:= fun i:I=> C k i • debit F i
 rw [show BandPlot (debit F) (C k)=∑ i∈T,B i from (sum_subset (subset_univ T) fun i _ q=>by rw [u _ _ q, zero_smul]).symm]
 refine SF_pool T _ _ ?_; intro i g; have ht:σ i=x k:=congrArg Prod.fst (mem_filter.mp g).2; rw [←ht]; exact oF.fee _
variable (M Lk)
include wL hp hv v e
lemma Funding (k:U): BandPlot (PressRow p M κ σ h F Lk) (C k)=Brow (RootPrice p (x k)) M h p (BandPlot (debit F) (C k)) Lk (d k):=by
 let T:=rootsSub σ (x k) κ (d k)
 have he(M:Type)[AddCommMonoid M][Module ℂ M](W:I→M):BandPlot W (C k)=∑ i∈T,C k i • W i:=by exact (sum_subset (subset_univ T) (fun i _ t=>by rw [u _ _ t,zero_smul])).symm
 rw [he,he]; have ht(i:I)(p:i∈T): (σ i,κ i)=(x k,d k):=(mem_filter.mp p).2
 unfold Brow; rw [Oath.FetchLinear _ M _ T _ (debit F) (o:=x k) (fun i w=>((show σ i=x k from congrArg Prod.fst (ht i w)) ▸ oF.fee _)) rfl e hp (lt_trans (by norm_num) v)] -- ▸ issue
 apply sum_congr rfl; intro i z; apply congrArg; unfold PressRow Brow; rw [show σ i=x k from congrArg Prod.fst (ht i z),show κ i=d k from congrArg Prod.snd (ht i z)]
include fw ω' oH a
lemma Lodges (k:U) : passingFee (mid N B) s (BandPlot (debit F) (C k)) (BandPlot (debit H) (A k)) ∧ Zvia s (BandPlot (PressRow p M κ σ h F Lk) (C k)) (BandPlot (PressRow p M μ t h H Lk) (A k)):=by
 let X:=RootPrice p (x k)
 have hp': passingFee G7 s (BandPlot (debit F) (C k)) (BandPlot (debit H) (A k)):=by
    intro i V; rw [←Row_ξ _ _ _ _ _ _ _ oH a,←Row_ξ _ _ _ _ _ _ _ oF u]; exact Darboux Πν T9 C _ _ A (oF.art i V) (oH.art _ _) (Turk s) u a (by simp [ψS]) (by simp [ψS]) (ω'.mono fun i p _=>p _ _) -- args order
 refine ⟨hp',?_⟩; rw [Funding d σ κ C F p Lk h M v e hp hv oF wL u,Funding d t μ A H p Lk h M v e hp hv oH wL a] -- tune args
 have he:y k=sh s (x k):=congrFun fw k
 rw [he,←root_d]; apply FetchΔ _ _ _ _ _ _ hp' _ hv e v _ -- tune
 · exact OnTrail _ _ _ _ _ p h oF u k -- tune
 · rw [←he]; exact OnTrail _ _ _ _ _ p h oH a k
 refine le_trans (b:=fortK) ?_ (wL.trans (Nat.le_succ _)); change coverNumber p.B (Lattice.halo (1000*p.B) {x k})≤ fortK; exact Corona.tile _ _ _ (by have hl:=hv.1; omega)
lemma Ribbon (i:Key U) : passingFee (mid N B) s (BandPlot (debit F) (SpotQ C i)) (BandPlot (debit H) (SpotQ A (Λpay s ∘ i))) ∧ Zvia s (BandPlot (PressRow p M κ σ h F Lk) (SpotQ C i)) (BandPlot (PressRow p M μ t h H Lk) (SpotQ A (Λpay s ∘ i))):=by
 let G:=PressRow p M κ σ h F Lk; let H':= PressRow p M μ t h H Lk;
 let uS(j):= Lodges d σ κ C F H s t μ A p Lk h M v e hp hv oF oH wL fw u a ω' j -- tune
 simp_rw [rowSpot]
 let C'(j):=BandPlot G (C j); let D'(j):= BandPlot H' (A j); let U':=suit_Y s
 constructor
 · let F'(j):=BandPlot (debit F) (C j); let H''(j):=BandPlot (debit H) (A j)
   intro X V; let L:=moldA s X; let W:=yellA s V; change (∑ j:U, (Λpay s) (i j) • H'' j) L W = (suit_Y s) ((∑ j:U,i j • F' j) X V); rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum] -- tune inner W
   exact sum_congr rfl (fun j _ => (show (Λpay s) (i j) • H'' j L W=U' (i j • F' j X V) from (congrArg ((Λpay s (i j)) • ·) ((uS j).1 X V)).trans (inkC ..).symm))
 apply via_sum (A:=fun j=>i j • C' j) (A':=fun j=>(Λpay s) (i j) • D' j) _ _ _ (Equiv.refl U) (fun _=>⟨fun _=>mem_univ _,fun _=>mem_univ _⟩) _
 intro j _; let H:= (uS j).2; let a:=Λpay s; refine ⟨fun V x=> (congrArg (a (i j) • ·) (H.1 V x)).trans (inkC ..).symm, fun V x v D e g=> (congrArg (a (i j) • ·) (H.2.1 V x v D e g)).trans (inkC ..).symm,?_⟩; change a (i j)*(D' j).2.2=Spire.payZ s _; rw [show (D' j).2.2=Spire.payZ s (C' j).2.2 from H.2.2]; change _= Spire.payZ s (i j*(C' j).2.2); rw [←inkPay,←inkPay]; exact (map_mul ..).symm
lemma κRibbon (i:U→ℝ): passingFee (mid N B) s (BandPlot (debit F) (LegQ C i)) (BandPlot (debit H) (LegQ A i)) ∧ Zvia s (BandPlot (PressRow p M κ σ h F Lk) (LegQ C i)) (BandPlot (PressRow p M μ t h H Lk) (LegQ A i)):=by
 let j:Key U:=fun u=>(i u:ℂ); have he:= Ribbon d σ κ C F H s t μ A p Lk h M v e hp hv oF oH wL fw u a ω' j; rw [show Λpay s ∘ j=j from (funext fun k=>(inkPay s _).trans (inkR ..))] at he; exact he
omit wL hp hv v e fw u oF a oH ω'
lemma PillarQ (F:I→Zone G7)(k:Key I): (BandPlot F k).1=EraT (G_P F) k∧(BandPlot F k).2.1=Φstack (G_K F) k∧(BandPlot F k).2.2= α_ξ (G_s F) k:=by
 unfold BandPlot; rw [_root_.Prod.fst_sum,_root_.Prod.snd_sum,_root_.Prod.fst_sum,_root_.Prod.snd_sum]; exact ⟨rfl,rfl,rfl⟩
lemma Leg_rise :∀ᶠ x: U→ℝ in 𝓝 0,LegQ C x∈hill I:=by have ht:=Turn_R C|>.tendsto (x:=0); rw [Leg_Z] at ht; exact ht.eventually (closedBall_mem_nhds _ zero_lt_one) -- tune
lemma waterPass (X Y:Vow.Pax G7)(h:Turf Y)(v:passingFee G7 s X Y) : passingR G7 s (Ione.cast_E X T) (Ione.cast_E Y Q) :=by
 intro i x; unfold Ione.cast_E; rw [load_Y]; simp only [Pi.smul_apply]; rw [(map_smul _ _ _),show Y (moldA s (lagE i)) (flashA s x,Q)= _ from (h (moldA s (lagE i)) (yellA s (x,T)) Q).symm, (v (lagE i) (x,T))]; change _ • _= _; congr 1; unfold bassH; change (((Finset.map _ _).card:ℝ)⁻¹:ℝ)=_; rw [Finset.card_map] -- tune ℝ.s
include wL hp hv v e fw u oF a oH ω'
local notation "Ξ"=> PressRow p M κ σ h F Lk
local notation "Ξr"=> PressRow p M μ t h H Lk
variable (Z: Cusp (mid N B))(hZ:ZealQ Z)
include hZ
lemma Rights : ∀ᶠ i: U→ℝ in 𝓝 0, passingR G7 s (N_P F T Ξ (LegQ C i)) (N_P H Q Ξr (LegQ A i)) ∧ passingU_n G7 s (NQr (LegQ C i) Z Ξ) (NQr (LegQ A i) Z Ξr) ∧ α_ξ (G_s Ξr) (LegQ A i)=Spire.payZ s (α_ξ (G_s Ξ) (LegQ C i)):=by
 filter_upwards [ω',Leg_rise A,Leg_rise C] with i v' x₁ x₂
 let a0:=LegQ C i; let b0:=LegQ A i
 obtain ⟨t,j,q,g⟩:= κRibbon d σ κ C F H s _ μ A p Lk h M v e hp hv oF oH wL fw u a ω' i; rw [← PillarQ Ξ a0 |>.2.2,← PillarQ Ξr b0 |>.2.2]; refine ⟨passingR.add _ ?_ (waterPass s T Q _ _ (turp_X H oH.bill b0 x₁) ?_),passingU_n.add s ?_ ?_,g⟩ -- tune binder order t shadows t.part
 · rw [← (PillarQ Ξ a0|>.1),← (PillarQ Ξr b0|>.1)]; exact j -- tune
 · intro j v; exact (congrArg₂ (·-·) (v' j v) (t j v)).trans (map_sub ..).symm
 · exact fun j V p D u v=> hZ s V p j D u v
 rw [← (PillarQ _ _|>.2.1),←(PillarQ _ _|>.2.1)]; exact q -- tune
#print axioms Rights
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
