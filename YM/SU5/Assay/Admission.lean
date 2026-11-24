import YM.SU5.Diva.Emporium

/-!
# Closing the purchase while retaining supplemental grants
 Given a grant (`Lux`) procured on the preparation of Emporium with
 the commission, issue on that very preparation. Adapted from Emporium.
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
variable {F' G' Q₀ C:ℝ→ℝ}{F:(s:Side)→Scree.Loom s→Prop}{N0:ℕ}{W:GivenX V U}{M:Side}{J:Robes M V W}(q:Chi)(b:ℕ)(h a τ :ℝ)(F0:Scrolls B)
namespace LocalLimit
open Preparation

def Admission (Lux:Preparation →Prop):Prop:=∀ (e' ε:ℝ), 0<e' →∀ Hq:Supplier,
    ∃ (P:Preparation)(l:ℕ)(Z:ℝ) (Y : Course P (VolumeCape.Dream.Nimbus l)), Lux P ∧ decorate Hq P l Z ≤ P.h ∧ ε < P.x ∧ P.d ≤ e' ∧ Inflation Z P ∧ Geometry P ∧ Attic P ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
        (∃ z, Usable (D:=P.δ) P.V P.W P.J P.N0 z P.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay) ∧
        (∀ i j : ℕ, Buffered.Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ u k : ℕ → ℕ, StrictMono u ∧ StrictMono k ∧ Nonempty (Y.Query u k)

theorem ordinaryAdmission : Admission (fun _=>True):=by
 intro e' ε h Q; obtain ⟨P,l,Z,Y,w⟩:=commissionAttic e' ε h Q; exact ⟨P,l,Z,Y,trivial,w⟩

variable {L₁ L₂:Preparation →Prop}
lemma Admission.mono (v:Admission L₁)(e:∀ P,L₁ P →L₂ P):Admission L₂:=by
 intro x y d K; obtain ⟨P,l,Z,Y,h,w⟩:=v _ y d K; exact ⟨P,l,Z,Y,e _ h,w⟩

def mergeSup (Q U:Supplier):Supplier:= fun K p X V B d T W M J l Z=> max (Q K p X V B d T W M J l Z) (U K p X V B d T W M J l Z)

/-- Additional grants one can pay by capping P.d and raising P.h. -/
def DoorMoney (Lux:Preparation →Prop):Prop:=
 ∃ r>(0:ℝ),∃ Q:Supplier, ∀(P:Preparation)(l:ℕ)(Z:ℝ),Geometry P→P.d≤r → decorate Q P l Z ≤P.h → Lux P
lemma Admission.fund (v:Admission L₁)(w:DoorMoney L₂):Admission (fun P=>L₁ P∧L₂ P):=by
 intro x y p U
 obtain ⟨r,t,Q,q⟩:=w; obtain ⟨P,l,Z,Y,h,g,z,d,c,f,u⟩:=v (min r x) y (lt_min t p) (mergeSup U Q)
 exact ⟨P,l,Z,Y,⟨h,q _ _ Z f (d.trans (min_le_left ..)) ((le_max_right ..).trans g)⟩, (le_max_left ..).trans g,z,d.trans (min_le_right ..),c,f,u⟩
end LocalLimit
end Rate
end YM.CF.Py
namespace YM.CF.Py
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
open Satin Tapestry
open Lifted (nodeC node_of)
-- extra supplier passed into govt, allow ask heights arbitrarily. IF need calibration radius issues come back
private def augment_AA (Q U : Supplier) : Supplier := fun K p X V B d T W M J l Z=> max (U K p X V B d T W M J l Z) (Q K p X V B d T W M J l Z)
private def agendum_AA (G Z:ℝ)(d:ℕ):= max 0 ((G+Z+6)/innerRatio d)
private def heatSupp_AA (G Z:ℝ)(d:ℕ)(R:ℝ):= min 1 (Real.exp (-2*(agendum_AA G Z d+R))/(2*R+3))
private def ukase_AA (d:ℕ)(R:ℝ): Supplier:= fun K _ _ V _ _ _ W _ _ _ Z=> (heatSupp_AA (sealPrice V W+ blossom K) Z d R)⁻¹
private lemma shoots_AA (G Z:ℝ)(d:ℕ)(h:0<R):
 let e:=heatSupp_AA G Z d R; 0<e ∧ e ≤ 1 ∧ e*(2*R+3) ≤ Real.exp (-2*(agendum_AA G Z d+R)) ∧ agendum_AA G Z d*innerRatio d ≥ G+Z+6:=by
 unfold heatSupp_AA; have hp:=innerRatio_pos d; intro V; unfold V
 refine ⟨lt_min zero_lt_one (by positivity),min_le_left ..,(le_div_iff₀ (by linarith)).mp (min_le_right ..),(div_le_iff₀ hp).mp (le_max_right ..)⟩
private lemma honey_s_AA (_Rδ:0<δ)(p:P.d ≤ δ) (q₀:0<R)(Z:Inflation A P)
    (g:∃ N:ℕ,(∀ n:Side,N≤ n.val→∀ S:Finset (Skye.Seat n),Sparse d S→∀ (M:Tulip.Male) (b: Bool), HearthB R (sp b P.K.j M (1:Pane n)) S)∧∀ ε> (0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side, N ≤ n.val→Winter P.K.j δ n γ w ε) (u: decorate (ukase_AA d R) P l A ≤ P.h): ∃ q w,Cornet Y H q d w ((1+R)^(q^4)) A:=by
 let G:=sealPrice P.V P.W+blossom P.K; let a:=agendum_AA G A d; let e:=heatSupp_AA G A d R; obtain ⟨t,v,x,pX⟩:= shoots_AA G A d q₀
 let η:= (2*R+4*R*R); let ε:= min (1/(3*R)) (e^3/η); have hz: 0< ε:= lt_min (by positivity) (by have h: 0<e:=t; unfold η; positivity)
 obtain ⟨N,h0,h1⟩:=g; obtain ⟨γ,hγ,w,sh⟩:=h1 ε hz; let L:=w+d+1+(addgap (tent Y H))
 have hw: 0<L:= by unfold L; omega
 have hc: ε*R ≤1/3:= (le_div_iff₀ q₀).mp ((min_le_left ..).trans_eq (by ring)); refine ⟨L,w, coeval Y H hγ Z hw q₀ (wineGod (T:=G+A+6) (h:=e⁻¹) Y H u Z p ((eventually_ge_atTop N).mono (fun x p n l=>?_)) hγ hc ((le_div_iff₀ (show 0<η by unfold η; positivity)).mp (min_le_right ..)) t v rfl (le_max_left (0:ℝ) (((G+A+6)/innerRatio d))) x pX (by unfold G; linarith) q₀ hw (Nat.le_add_right ..) (Nat.le_add_left ..))⟩
 exact ⟨sh n (p.trans l),fun M b S v=> h0 n (p.trans l) S v M b⟩
theorem elite_admission {Lux: Preparation →Prop}(V':Admission Lux) (ε η:ℝ)(p:0<η)(U:Supplier) :
    ∃ (P:Preparation)(l:ℕ)(Z:ℝ),Lux P ∧ ε<P.x ∧ P.d ≤ η ∧ decorate U P l Z≤ P.h ∧ Geometry P ∧ Attic P ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H:Real.exp 1≤ P.x)(Y:Course P (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=P.δ) P.V P.W P.J P.N0 z P.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay) ∧
        (∀ i j:ℕ, Buffered.Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ q d w C, Cornet Y H q d w C Z∧
        ∃ (a b:ℕ→ℕ) (I: ℕ→Buffered.Family (tent Y H)→ℕ→ℂ)(E:ℕ→Buffered.Family (tent Y H)→ℂ) (L:Rack P l)(B:Tapestry.Clay P l)(T:ℕ→ℕ→Tapestry.Tariff)(t:ℕ→Tapestry.Tariff),∃ D: Tapestry.Fashion Y H a b I E L B T t, SeasonCert Y H D:=by
 obtain ⟨R,δ,r,v,N,d,h,u⟩:= chosenFlatPrice 4 (by decide); obtain ⟨Λ,l,Z,Y₀,Lx,g,z,g',T,Wℓ,αAttic,p₀,p₁,p₂,p₃,W,F,u0,f,Q⟩:= V' (min δ η) (max ε (Real.exp 1)) (lt_min v p) (augment_AA U (ukase_AA d R)); let Y:=Y₀; let H:Real.exp 1≤Λ.x:= (le_max_right ..).trans z.le; have gZ:= honey_s_AA Y H v (g'.trans (min_le_left ..)) r T (d:=d) (by rw [Λ.kJ]; exact ⟨N,h,u⟩) ((le_max_left ..).trans g)
 obtain ⟨q,w,e⟩:=gZ
 -- build universal I/E & Chronicle. retain original crew indirectly
 obtain ⟨i,k,G,c,w'',v'⟩:= Journey.exist_excerpt Y H W F u0 f (fun _ _=>True) (fun _=>Eventually.of_forall fun _=> trivial)
 let P:Journey.Cabinet Y H (W∘i) (F∘k):=⟨u0.comp G,f.comp c,fun a b p=> (w'' a b p).1,v'⟩
 obtain ⟨r,s,L,B,T',t,_,_,D,H'⟩:= Tapestry.chronicle Y H (Journey.canvassed Y H P); exact ⟨Λ,l,Z,Lx,(le_max_left ..).trans_lt z,g'.trans (min_le_right ..),(le_max_right ..).trans g,Wℓ,αAttic,p₀,H,Y,p₁,p₂,p₃,q,d,w,_,e,_,_,_,_,_,_,_,_,D,H'⟩
end Papal
end LocalLimit
end Rate
end YM.CF.Py
