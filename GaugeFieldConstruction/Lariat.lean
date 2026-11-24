import GaugeFieldConstruction.Flames
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
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
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
variable {N:Side}{P:BudgetPoint}{o:Seat N}{E:InkD N}{X:Scree.Hub N}{M:Tulip.Male}{h t a v k b d:ℝ}{r l L n:ℕ}
-- Receipt prices.No assumption on Charter at flagged region beyond Press. CPS
lemma shoot_B (w:PressB (KeyUp P) X E h t)(s:0 ≤ h) : ‖χE X E‖ ≤t:=by
 have hv: Signs (KeyUp P) X.val.1 (term E) t:= eraF E X w s 1 (ping_f _ _)
 exact (show χE X E= term E 0 from (by simp [χE,term])) ▸ Prism.sig0 hv
-- careful norm use eq
abbrev Copper_κ(c d:ℝ)(n:ℕ):= chi_f n*c +chi_f n*d
-- universal.D holds
abbrev signin (X:Scree.Hub N)(h t:ℝ)(P:BudgetPoint)(M:Tulip.Male)(E:InkD N):= SealT X E P h M
abbrev Jε:= Hcost*SectorVal
lemma Jε₀: 0≤Jε:=by unfold Jε SectorVal; have hp:=HC_pos; apply mul_nonneg hp; apply le_trans _ (le_max_left ..); norm_num
lemma vignette_cost (w:PressB (KeyUp P) X E h t)(s:0<h)(p: 300< N.val)(u:P.order=6) (M:Tulip.Male) (n:ℕ):let G:=splinter n X P h M E; let Z:= Zhub X.val.1; PressB (KeyUp P) Z G h (Jε*t) ∧ SealT Z G (KeyUp P) h M= MSlot n (SealT X E (KeyUp P) h M)∧ lifeH G 1=0:=by
 let L:= SealT X E (KeyUp P) h M; intro F Z
 obtain ⟨C,a,b⟩:=stronghold (o:=X.val.1) M p s (p:=KeyUp P) le_rfl (show (KeyUp P).order≤6 from u.le) (MSlot n L)
 refine ⟨Layout.lift_PV b ?_,(meter_sure (X:=Zhub X.val.1) _ C).symm,a⟩; unfold Jε; rw [mul_assoc Hcost SectorVal]; exact mul_le_mul_of_nonneg_left ((MSlot_m L n).trans (S_along w s.le M)) HC_pos
lemma tint_tagE (w:PressB (KeyUp P) X E h t)(s:0<h)(p:300< N.val)(u:P.order=6) (M:Tulip.Male)(n:ℕ)(v:(Zhub X.val.1).val.2⊆X.val.2) : let Z:= SealT X E (KeyUp P) h M; let F:=splinter n X P h M E; let R:= E-(χGhost N (χE X E)+F); PressB (KeyUp P) X R h ((2+Jε)*t) ∧ SealT X R (KeyUp P) h M=Z-MSlot n Z∧ lifeH R 1=0:=by
 intro Z F R; let K:= χGhost N (χE X E); let T:= Zhub X.val.1; have he:= χCost (KeyUp P) h (χE X E) X; obtain ⟨hoY,g,hP⟩:=vignette_cost w s p u M n; -- h shadow fix
 have hf :=cut_further (X:=Zhub X.val.1) hoY v rfl s.le; let G:= K+F; let hc:=prop_add (KeyUp P) X he hf; have ht:= strikeE w hc s.le
 refine ⟨Layout.lift_PV ht ?_,?_,?_⟩; · have hx:= shoot_B w s.le; linarith only [hx]
 · let P0:= KeyUp P; have hQ: SealT X G P0 h M=MSlot n Z:=by
      have hp0: SealT X K P0 h M =0:= (meter_sure (X:=X) (M:=M) _ (Layout.linearØ X.val.1 M (χE X E))).symm
      rw [show G=K+F from rfl,SeT_add s.le he hf,hp0,show SealT X F _ h M=MSlot n Z from (SeT_at X hoY s.le v rfl M).symm.trans g]; exact @zero_add Waves kinnG.toAddCommGroup.toAddMonoid.toAddZeroClass _
   have hb : SealT X R P0 h M+MSlot n Z=Z:=by rw [←hQ,←SeT_add s.le ht hc]; unfold Z; congr 1; exact sub_add_cancel ..
   exact @eq_sub_of_add_eq Waves kinnA.toAddGroup _ _ _ hb
 change lifeH E 1-(lifeH K 1+lifeH F 1)=0; rw [hP,add_zero]; exact sub_eq_zero.mpr (congrFun (Layout.life_hz (n:=N) (χE X E)) _).symm -- tune

lemma Parcel_root (w:PressB (KeyUp P) X E h t)(s:0<h)(p:300< N.val)(u:P.order=6)(M:Tulip.Male)(j:ℕ)(l:j ≤ r)(e:r ≤2)(v:(Zhub X.val.1).val.2⊆X.val.2) : let A:=Zhub X.val.1; MSlot j (SealT A ((ℓParcel r X P h M E).1 A) (KeyUp P) h M)= MSlot j (SealT X E (KeyUp P) h M):=by
 intro A; let Y:= ℓParcel r X P h M E; let Z:= SealT X E (KeyUp P) h M; let G:=splinter r X P h M E; let U:=χGhost N (χE X E); let R:=E-(U+G)
 obtain ⟨ht,hC,x⟩:=tint_tagE w s p u M r v; obtain ⟨hp,g,l'⟩:=vignette_cost w s p u M r;
 have hv:Y.1 A=singleP X R A + G:=by change _+singleP A G A=_; unfold singleP; rw [Pi.single_eq_same]
 change MSlot j (SealT A (Y.1 A) _ _ _) =_; rw [hv]; by_cases a:X=A
 · rw [show singleP X R A=R from a ▸ (Pi.single_eq_same ..)]; -- cast safe?
   have he': MSlot r (SealT A R (KeyUp P) h M)=0:=by
      rw [←a,hC]; exact n_short (MNil r e) e -- danger dependent R internal.Let? rw
   rw [SeT_add s.le (a ▸ht) hp,MSlot_k,g, ← MStore _ l, he',void_M,MStore _ l]; exact @zero_add Waves kinnG.toAddCommGroup.toAddMonoid.toAddZeroClass _ -- tune occurrence MStore
 rw [show singleP X R A=0 from (by unfold singleP; rw [Pi.single_eq_of_ne (Ne.symm a)]),zero_add, g,MStore _ l]
abbrev PieceFee (w:ℝ):= (3+2*Jε)* w
abbrev PieceCost (p:BudgetPoint)(X:Scree.Hub N)(c:ℝ):= currency p.B 3 X.val.2 * (2*chi_f p.order*Jε*c + chi_f p.order*c)
lemma piece_B (w:PressB (KeyUp P) X E h t)(tA:0≤a)(s:0<h)(p:300< N.val)(u:P.order=6)(p0:P.power=2)(M:Tulip.Male)(e:r≤2)(v:(Zhub X.val.1).val.2⊆ X.val.2)(hB:coverNumber P.B X.val.2 ≤ L): Basalt P X.val.1 l L (ℓParcel r X P h M E) (PieceFee (currency P.B a X.val.2*t)) a (PieceCost P X t) h r M := by
 let Z:=SealT X E (KeyUp P) h M; let F:=splinter r X P h M E; let R:=E-(χGhost N (χE X E)+F); let A:=Zhub X.val.1
 let aX:=lagE X; let ΩK:=Ωχ X (χE X E); let J:= Vow.stroke aX (lagE A) aX (oV F) (oV F)
 obtain ⟨ht,hC,x⟩:=tint_tagE w s p u M r v; obtain ⟨hp,g,l'⟩:=vignette_cost w s p u M r
 have he:Basalt P X.val.1 l L (locusH X R) _ a 0 h r M:= locusH_g ht s.le (fun _=> ⟨x,fun _=> hC.symm ▸ n_short (MNil r e) e⟩)
 have hP:Basalt P X.val.1 l L (locusH A F) _ a 0 h r M:= locusH_g hp s.le (fun _=> ⟨l',fun h=> False.elim (h rfl)⟩)
 have hQ:= (transport_X A X hB v rfl hp s.le p0).2.2
 let U:=J + ΩK; have hf:= HasCopper.add hQ (ΦCost s.le X hB (χE X E)); have hx: HasCopper L X.val.1 P h U (PieceCost P X t):=by
    refine hf.shove ?_; unfold PieceCost; let C:=Trees.currency P.B 3 X.val.2; let Z:=chi_f P.order; have h:0 ≤ C:=(Real.exp_pos _).le; have he:0 ≤ Z:=spicy_f _; let T:=χE X E; have hQ:‖T‖ ≤ t:= shoot_B w s.le
    change C * (Z * (Jε*t)+Z*(Jε*t))+ C*(Z * ‖T‖) ≤ C*(2*Z*Jε*t+ _); nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ he) h]
 have hk := Basalt.terms (he.terms hP s.le) (bury_budget U (χE X E) hx) s.le
 rw [show ℓParcel r X P h M E=locusH X R+locusH A F+bury U (χE X E) from ?_]; swap
 · apply Prod.ext; · change _=singleP X R+singleP A F+0; rw [add_zero]; rfl
   apply Prod.ext; · change _=0+0+U; simp only [add_zero,zero_add]; rfl
   change _=0+0+χE X E; rw [add_zero,zero_add]; rfl
 refine hk.sharpen ?_ (by simp)
 let C:=Trees.currency P.B a X.val.2; have h':0≤t:= skim w s.le; have hc:1 ≤ C:= Real.one_le_exp (by positivity); unfold PieceFee; change C*_+ _+_ ≤ _*(C*t); refine (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_right (show Trees.currency P.B a A.val.2≤C from Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Corona.cover_mono v _)) tA)) (mul_nonneg Jε₀ h')) _) ((shoot_B w s.le).trans (le_mul_of_one_le_left h' hc))).trans_eq ?_
 ring
end
end YM.CF.Oath
end
