import YM.SU5.Selected.Broadcast

/-! # A boosted version of Papal.elite. Purchase (including Cornet) on EXACT platform, before mixed-probe election. Do not identify with another choice of V. -/

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
structure Policy (q d w:ℕ)(Z R γ:ℝ) : Prop where
 old : Cornet Y H q d w ((1+R)^(q^4)) Z
 positive : 0<R ∧ 0<γ ∧ 1≤payout d q w
 focus (j:Axis) : ∀ᶠ s in atTop,∀ᶠ i in atTop, ∀ᶠ k in atTop,(Y.voyage i).kick≤k ∧ s≤Y.uv k ∧
    (∀ b (S:Finset (Seat (Papal.count Y s i))), Sparse d S→HearthB R (sp b P.K.j (gram Y s i k).J.M (1:Pane (Papal.count Y s i))) S) ∧ ∀ z:SU.Slot, CoupleCost Y H γ R j d q w s i k z
private def spendTwice (Q U : Supplier) : Supplier := fun K p X V B d T W M J l Z=> max (U K p X V B d T W M J l Z) (Q K p X V B d T W M J l Z)
private def formalAgenda (G Z:ℝ)(d:ℕ):= max 0 ((G+Z+5003)/ratioFort d)
private def formalPhase (G Z:ℝ)(d:ℕ)(R:ℝ):= min 1 (Real.exp (-2*(formalAgenda G Z d+R))/(2*R+3))
private def reserveHeight (d:ℕ)(R:ℝ): Supplier:= fun K p X V B d0 U W M J l Z=> (formalPhase (sealPrice V W+ blossom K) Z d R)⁻¹
private lemma heightBounds (G Z:ℝ)(d:ℕ)(h:0<R):
 let e:=formalPhase G Z d R; 0<e ∧ e ≤ 1 ∧ e*(2*R+3) ≤ Real.exp (-2*(formalAgenda G Z d+R)) ∧ formalAgenda G Z d*ratioFort d ≥ G+Z+5003:=by
 unfold formalPhase; have hp:=(ratioFort_price d).1; intro V; unfold V
 refine ⟨lt_min zero_lt_one (by positivity),min_le_left ..,(le_div_iff₀ (by linarith)).mp (min_le_right ..),(div_le_iff₀ hp).mp (le_max_right ..)⟩
private lemma scopePair (Rδ:0<δ)(p:P.d ≤ δ) (q₀:0<R)(Z:Inflation A P)
    (g:∃ N:ℕ,(∀ n:Side,N≤ n.val→∀ S:Finset (Skye.Seat n),Sparse d S→∀ (M:Tulip.Male) (b: Bool), HearthB R (sp b P.K.j M (1:Pane n)) S)∧∀ ε> (0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side, N ≤ n.val→Winter P.K.j δ n γ w ε) (u: decorate (reserveHeight d R) P l A ≤ P.h): ∃ q w γ, Policy Y H q d w A R γ:=by
 let G:=sealPrice P.V P.W+blossom P.K; let a:=formalAgenda G A d; let e:=formalPhase G A d R; obtain ⟨t,v,x,pX⟩:= heightBounds G A d q₀
 let η:= (2*R+4*R*R); let ε:= min (1/(3*R)) (e^3/η); have hz: 0< ε:= lt_min (by positivity) (by have h: 0<e:=t; unfold η; positivity)
 obtain ⟨N,h0,h1⟩:=g; obtain ⟨γ,hγ,w,sh⟩:=h1 ε hz; let L:=w+d+1+(addgap (tent Y H))
 have hw: 0<L:= by unfold L; omega
 have hc: ε*R ≤1/3:= (le_div_iff₀ q₀).mp ((min_le_left ..).trans_eq (by ring))
 have Ft: ∀ᶠ n:ℕ in atTop,∀ (M:Side),n≤M.val→Winter P.K.j δ M γ w ε ∧ ∀ M':Tulip.Male,∀ b S,Sparse d S→ HearthB R (sp b P.K.j M' (1:Pane M)) S := (eventually_ge_atTop N).mono (fun x p n l=> ⟨sh n (p.trans l),fun M b S v=> h0 n (p.trans l) S v M b⟩)
 have ha: (0:ℝ) ≤ a:= le_max_left ..
 exact ⟨L,w,γ,coeval Y H hγ Z hw q₀ (wineGod (T:=G+A+5003) (h:=e⁻¹) Y H u Z p Ft hγ hc ((le_div_iff₀ (show 0<η by unfold η; positivity)).mp (min_le_right ..)) t v rfl (show 0≤a from ha) x (pX.trans (mul_le_mul_of_nonneg_left (ratioFort_price d).2 ha)) (by unfold G; linarith) q₀ hw (Nat.le_add_right ..) (Nat.le_add_left ..)),⟨q₀,hγ,by unfold payout; omega⟩,fun j=> wineLaunch (T:=G+A+5003) (h:=e⁻¹) Y H j u Z p Ft hγ hc ((le_div_iff₀ (show 0<η by unfold η; positivity)).mp (min_le_right ..)) t v rfl (show 0≤a from ha) x pX (by unfold G; linarith) q₀ hw (Nat.le_add_right ..) (Nat.le_add_left ..)⟩
theorem subsidy (ε η:ℝ)(p:0<η)(U:Supplier) :
    ∃ (P:Preparation)(l:ℕ)(Z:ℝ),ε<P.x ∧ P.d ≤ η ∧ decorate U P l Z≤ P.h ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H:Real.exp 1≤ P.x)(Y:Course P (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=P.δ) P.V P.W P.J P.N0 z P.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay) ∧
        (∀ i j:ℕ, Buffered.Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ q d w R γ, Policy Y H q d w Z R γ ∧
        ∃ (a b:ℕ→ℕ) (I: ℕ→Buffered.Family (tent Y H)→ℕ→ℂ)(E:ℕ→Buffered.Family (tent Y H)→ℂ) (L:Rack P l)(B:Tapestry.Clay P l)(T:ℕ→ℕ→Tapestry.Tariff)(t:ℕ→Tapestry.Tariff),∃ D: Tapestry.Fashion Y H a b I E L B T t, SeasonCert Y H D:=by
 obtain ⟨R,δ,r,v,N,d,h,u⟩:= chosenFlatPrice 4 (by decide); obtain ⟨Λ,l,Z,Y₀,g,z,g',T,p₀,p₁,p₂,p₃,W,F,u0,f,Q⟩:= commission (min δ η) (max ε (Real.exp 1)) (lt_min v p) (spendTwice U (reserveHeight d R)); let Y:=Y₀; let H:Real.exp 1≤Λ.x:= (le_max_right ..).trans z.le; have gZ:= scopePair Y H v (g'.trans (min_le_left ..)) r T (d:=d) (by rw [Λ.kJ]; exact ⟨N,h,u⟩) ((le_max_left ..).trans g)
 obtain ⟨q,w,γ,e⟩:=gZ
 -- build universal I/E & Chronicle. retain original crew indirectly
 obtain ⟨i,k,G,c,w'',v'⟩:= Journey.exist_excerpt Y H W F u0 f (fun _ _=>True) (fun _=>Eventually.of_forall fun _=> trivial)
 let P:Journey.Cabinet Y H (W∘i) (F∘k):=⟨u0.comp G,f.comp c,fun a b p=> (w'' a b p).1,v'⟩
 obtain ⟨r,s,L,B,T',t,_,_,D,H'⟩:= Tapestry.chronicle Y H (Journey.canvassed Y H P); exact ⟨Λ,l,Z,(le_max_left ..).trans_lt z,g'.trans (min_le_right ..),(le_max_right ..).trans g,p₀,H,Y,p₁,p₂,p₃,q,d,w,R,γ,e,_,_,_,_,_,_,_,_,D,H'⟩
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.subsidy
