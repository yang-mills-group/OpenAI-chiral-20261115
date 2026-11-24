import GaugeFieldConstruction.Bowdeck
import GaugeFieldConstruction.Nandin
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 145000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
open Boom Oath
-- normalization D offset3. r=0→FieldSlots≤3
variable {E:InkD n}{f:Waves}{M:Male}{c':ℝ}{r:ℕ}{Y:Scree.Hub n}
abbrev MSlot (n:ℕ)(f:Waves):Waves:= (f.1,if 1≤n then f.2.1 else 0,if 2≤n then f.2.2 else 0)
lemma MSlot_m (f:Waves)(n:ℕ) : ‖MSlot n f‖≤ ‖f‖:=by
 apply max_le (le_max_left ..)
 have h:= norm_nonneg f
 by_cases he:1≤ n <;> by_cases hv:2 ≤ n
 · exact le_trans (le_of_eq (congrArg _ (show (MSlot n f).2=f.2 from (by simp [MSlot,he,hv])))) (le_max_right ..)
 · unfold MSlot; rw [if_pos he,if_neg hv]; refine max_le ((le_max_left ..).trans (le_max_right ..)) ?_
   exact (le_trans (@norm_zero J5 (CartPack PackH (CartPack PackM PackS)).G.toNormedAddGroup.toSeminormedAddGroup).le h) -- tune inst
 · omega
 · unfold MSlot; rw [if_neg he,if_neg hv]; exact le_trans (@norm_zero (J4 × J5) (CartPack (CartPack PackG PackP) (CartPack PackH (CartPack PackM PackS))).G.toNormedAddGroup.toSeminormedAddGroup).le h -- tune
lemma chart_origin (f:Waves):chartF (MSlot r f)=Shorten r (chartF f):=by apply Prod.ext; rfl; apply Prod.ext <;> unfold MSlot Shorten <;> split_ifs <;> rfl -- sequencing
abbrev Nail (f:Waves) (r:ℕ) := (4≤r+2→ f.2.1.1 = 0)∧(5≤r+2→f.2.2.1=0) ∧ (1≤r→f.1=0) ∧ (2≤r→f.2.1.2=0)∧ (3≤r→ f.2.2.2.1=0) ∧ (r=3→f.2.2.2.2=0)
lemma Knock (P: MetaB o M f E p h)(v: r ≤3): CarBot _ o p M E h r ↔ (lifeH E 1=0∧ Nail f r):=by -- f,M not bind
 constructor
 · intro h; obtain ⟨⟨u,h,t⟩,⟨a,b,w⟩,v⟩:=h; rw [←P.port] at a b w; rw [←P.post] at h; rw [←P.mast] at t
   refine ⟨u,fun i=>Subtype.ext (h i), t,fun i=>Subtype.ext (a i),fun i=>Subtype.ext (b i),fun i=>Subtype.ext (congrArg (fun x:Lenten.Bank.Duo Views Pal=>x.val) (w i)), fun i=> Subtype.ext (P.mixed.trans (v i))⟩
 rintro ⟨u,t,hQ,a,b,w,hp0⟩; have hz: KappaF r (chartF f):= ⟨fun i=>congrArg Subtype.val (a i),fun i=>congrArg Subtype.val (b i),fun i=>Subtype.ext (congrArg (fun x:P25=>x.val) (w i))⟩
 exact ⟨⟨u,fun i=> P.post.symm.trans (congrArg Subtype.val (t i)),fun i=>P.mast.symm.trans (hQ i)⟩, (show KappaF _ (winJ _ _ _ _) from P.port ▸ hz),fun i=>P.mixed.symm.trans (congrArg Subtype.val (hp0 i))⟩
lemma MRet {f:Waves}(v:r≤3)(p:Nail f r):Nail (MSlot r f) r:=by
 obtain ⟨p,t,h,b,s,u⟩:=p; unfold Nail MSlot; interval_cases r <;> simp_all -- tune
lemma MNil {f:Waves}(r:ℕ)(p:r≤2):Nail (f-MSlot r f) (r+1):=by
 refine ⟨fun v=>?_,fun v=>?_,fun v=>?_,fun v=>?_,fun v=>?_,fun v=>?_⟩ -- projection val norms
 · change (bF4 f)-(bF4 (MSlot r f))=0; rw [show bF4 (MSlot r f) =bF4 f from ?_]; exact @sub_self G3 PackG.G.toAddCommGroup.toAddGroup _; unfold MSlot bF4; rw [if_pos (by omega)]
 · change bF5 f-bF5 (MSlot r f)=0; rw [show bF5 (MSlot r f) =bF5 f from ?_]; exact @sub_self Gκ PackH.G.toAddCommGroup.toAddGroup _; unfold MSlot bF5; rw [if_pos (show 2 ≤ r from by omega)]
 · exact sub_self f.1
 · change bV1 f-bV1 (MSlot r f)=0; rw [show bV1 (MSlot r f)= bV1 f from ?_]; exact @sub_self P14 PackP.G.toAddCommGroup.toAddGroup _; unfold MSlot bV1; rw [if_pos (by omega)]
 · change bV2 f-bV2 (MSlot r f)=0; rw [show bV2 (MSlot r f)= bV2 f from ?_]; exact @sub_self P25 PackM.G.toAddCommGroup.toAddGroup _; unfold MSlot bV2; rw [if_pos (show 2 ≤ r from by omega)]
 · change bm5 f-bm5 (MSlot r f)=0; rw [show bm5 (MSlot r f)= bm5 f from ?_]; exact @sub_self G15 PackS.G.toAddCommGroup.toAddGroup _; unfold MSlot bm5; rw [if_pos (show 2 ≤ r from by omega)]
lemma StrikeQ (p:BudgetPoint)(o:Skye.Seat n)(H:PressB p (Zhub o) Q h c)(u:PressB p (Zhub o) E h c') (hx:0≤h) : PressB p (Zhub o) (Q-E) h (c+c'):=by -- c' not bind.use cite strike extra params
 exact Taxi.strike 0 _ (fun i=>Vale.rinse i p h) hx H u -- tune
lemma IncPave (M:Male) (x:300<n.val)(u:0<h)(v:p.power ≤ 3)(t:p.order≤6)(H:PressB p (Zhub o) E h c)(q:CarBot _ o p M E h r)(p₀:MetaB o M f E p h)(l:r ≤2): let F:=shoulder o p M h (MSlot r f); let r':= Hcost*‖MSlot r f‖; PressB p (Zhub o) F h r' ∧ PressB p (Zhub o) (E-F) h (c+r')∧ CarBot _ o p M F h r ∧ CarBot _ o p M (E-F) h (r+1) :=by
 intro V B
 have hM:= stronghold M x u v t (MSlot r f) (o:=o); have hv:= StrikeQ _ _ H hM.2.2 u.le
 let W:=MSlot r f; let U:= exportM (X:=Zhub o) o M hv u.le rfl; let he:= export_full (X:=Zhub o) o M hv u.le rfl
 have hC:U=f-MSlot r f:=eq_sub_of_add_eq (metaUnique o M E p h (U+W) f (?_) p₀); swap
 · have ht:=linearHU o M he hM.1 u.le hv hM.2.2; rw [sub_add_cancel] at ht; exact ht
 refine ⟨hM.2.2,hv,(Knock hM.1 (by omega)).mpr ⟨hM.2.1, MRet (by omega) ((Knock p₀ (by omega)).mp q).2⟩,(Knock he (by omega)).mpr ⟨ ?_, (show Nail U _ from hC.symm ▸ MNil r l)⟩⟩
 change lifeH E 1-lifeH V 1=0; rw [q.low.unit, show lifeH V 1=0 from hM.2.1,sub_zero]
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
