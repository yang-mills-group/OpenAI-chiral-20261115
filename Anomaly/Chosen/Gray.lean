import Anomaly.Compass.Fathom
import Anomaly.Hop.Abode
import Anomaly.Compass.Grid
import Anomaly.Compass.Card
import SatinThinVow
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
open Oise Rive
open Ione.Clock
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Tc"=> mid N B
local notation "Tf"=> mid P B
local notation "Wν" => (duty_Q X.p.order X.p.power*W)
-- CP protocol reports.
variable {j k mc:ℕ}
variable {r:I→Site (mid N B)}{A:I→ArcΦ}{a:I→ℝ}{X₁:Key I→RegBudget (mid P B)}{X₂:Key I→ForceBudget (mid P B)}
variable (p:JuiceMeter V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp j mc) (U:OrbitPulse G X Y h b g l.L r X₁ X₂ A a mc)
-- Retains permission for P branch for comparison at one master. ONE sweep identity.
lemma soleA(x:Seat n): boxA (1:Sweep n) x=x:=(boxA (1:Sweep n)).injective (by rw [sitV,one_mul])
lemma soleT(A:Support (More n)): actY (1:Sweep n) A=A:=by ext i; simp [actY,soleA]
lemma soleY(x:Aura n): moldA (1:Sweep n) x=x:=Subtype.ext (soleT _)
lemma soleV(x:Orbit n):yellA (1:Sweep n) x=x:=by have ht:= y_rev (1:Sweep n) x; rwa [inv_one,yell_t,one_mul] at ht
lemma soleR : reSweep G (1:Sweep (mid N B))=1:=by unfold reSweep; congr 1; exact map_zero G.root
lemma parUni (X:Cusp n) :passingU_n n (1:Sweep n) X X:=by intro i x p j v w; rw [soleY,soleV,soleT,toon_Q] -- tune
variable (hc:IncX primeU Y.F Y.p h 1)(u₁:X.p.order=6)(u₂:X.p.power=2) -- remove
-- Output certificate retains raw allocator for matched tickets.
structure CordMint {r:I→ Site (mid N B)}{A:I→ArcΦ}{a:I→ℝ}{M:Key I→RegBudget (mid P B)}{F:Key I→ForceBudget (mid P B)} (Z:JuiceMeter V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp j mc) (x:OrbitPulse G X Y h b g l.L r M F A a mc) (R':Key I→RegBudget Tc)(V':Key I→ForceBudget Tc)(φ:I→ArcΦ) (s:I→ℂ) : Prop where
  grant: RoadMap V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp r M F A a j mc R' V' s φ
  raw : let Be:=Z.trust.choose; let CSP:=Z.trust.choose_spec.choose; let Kζ:=Z.trust.choose_spec.choose_spec.choose; ∃ (D:Key I→Cusp (mid N B)) (D':I→Cusp (mid N B)), (∀ i∈ hill I,Be.source (M i) (F i) (D i))∧(∀ (i:Aura Tc) (z: Orbit Tc), River fun x:Key I=>heat_P X.p D x i z)∧ V'=(fun z=>rust_L X.p (D z) (CSP+Φstack D' z)) ∧ ∀ i, let k:= nun_ω Y.F (Hove.heel G (r i)); let R:= κprobe mintR l.L h (a i) T k (A i); Ice l.L.val (r i) X.p h (W*R) (Kζ (A i) (a i)) (C*R) (feeTip X.p D i) (νTip R' i) (D' i) (s i) (φ i) ∧ αPrice l.L h (a i) T BQ Rt Zt (A i) (φ i) X.p Y.p k
variable {tO:I→ℂ}{K₀:I→Cusp (mid N B)}{M₀:Key I→ ForceBudget (mid N B)}{A₁:I→ArcΦ}{F':Key I→ RegBudget Tc}
local notation "Be"=> p.trust.choose
local notation "CSP"=> p.trust.choose_spec.choose
local notation "Caζ"=> p.trust.choose_spec.choose_spec.choose
include U hc u₁ u₂
lemma paints : let H:=p.trust.choose_spec.choose_spec.choose_spec; let Xf:= (H.heat r X₁ X₂ A a U).choose; ∀ (E:I→ RegBudget (mid N B))(Q:I→Cusp (mid N B))(z:I→ℂ)(Φ:I→ArcΦ), (∀ i:I, let k:= nun_ω Y.F (Hove.heel G (r i)); let R:= κprobe mintR l.L h (a i) T k (A i); Ice l.L.val (r i) X.p h (W*R) (Caζ (A i) (a i)) (C*R) (feeTip X.p Xf i) (E i) (Q i) (z i) (Φ i) ∧ αPrice l.L h (a i) T BQ Rt Zt (A i) (Φ i) X.p Y.p k)→ let Xk:= fun i=> rust_L X.p (Xf i) (p.trust.choose_spec.choose+Φstack Q i); ∃ R, (∀ i,νTip R i=E i) ∧ CordMint V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp p U R Xk Φ z:=by
 intro Bm F E K z Φ H Xk
 obtain ⟨v,s,ul,T'⟩:=(Bm.heat r X₁ X₂ A a U).choose_spec
 obtain ⟨R,hX,z',t,q',Q⟩:=T' E K Φ z (fun i=> ⟨iceφ_grow (zero_le_one.trans p.toe) (H i).1 u₁ u₂,(H i).2⟩)
 obtain ⟨M₀,Γ,θ⟩:=vow_life Y h hc p.toe (fun i _=>p.stillE i)
 have ht:νTip R=E:= funext t; refine ⟨R,t,⟨⟨⟨hX,z',_,_,Q⟩,?_⟩, ?_⟩⟩
 swap; · intro Be' C' Ca'
         rw [ht]; exact ⟨F,K,v,s,rfl,H⟩
 intro J a0 t'' i S₁ σ E' K' w R'
 obtain ⟨N,Pz,T',_,Tκ⟩:=Bm.heat _ _ _ _ _ R'
 let B₁:=fun j:J=> dashF (S₁ j) (E (i j)); let F₁:= fun j:J=>dashK (S₁ j) (K (i j))
 let θ₁(j:J):=Φ (i j); let z₁:=paint_S z i S₁; let θ':=orbit Φ i S₁
 obtain ⟨A₀,hT,b₀,Jv,M,Q⟩:= Tκ B₁ F₁ θ' z₁ (fun k=>by
   intro Kμ ℝq; let j:=i k; let s':=S₁ k; let e:=h
   let D:= H j; let T₀:= s'.s; let t' := spinU false T₀; let η:ArcΦ:=arc_s T₀ t' (A j)
   let u:=w.ride k; let Yv:= X.p; let U:=U; have hw:Kμ=(M₀:ℂ):= Γ _
   let b':=H j|>.1; let ht':=p.toe
   have hv := stocks (Q:=A j) (Q':=Φ j) s' u t' (show αPrice l.L _ _ _ _ _ _ _ _ X.p Y.p (M₀:ℂ) from (Γ _) ▸ D.2) -- pattern infer.L.V.Pin/Wager
   have had:= listens G X Y h b g U R' s' j k (p.stillE _) (p.stillF _) (w.park k) (w.fire k) v Pz s T'
   let q':= p.chamber
   -- move annot.
   let k_:= κprobe mintR l.L h (a j) T (nun_ω Y.F (Hove.heel G (r j))) (A j)
   have kK:s'=S₁ k:=rfl
   have he: k_=ℝq:=by
      unfold k_ ℝq; rw [Γ (Hove.heel G (r j)),hw]; exact Eq.symm (sameGauge ..)
   obtain ⟨e1,e2,e3⟩:= aria t' T₀ (A j)
   have heM:=Bm.voyage η (A j) e1 e2 e3
   have hi:=iceLaw s' (σ k) (feeTip X.p _ j) (feeTip X.p _ k) _ _ _ _ (W*k_) (Caζ (A j) (a j)) _ (zero_le_one.trans p.toe) (Ice_γ (zero_le_one.trans p.toe) b').1 (show Ice l.L.val (mPath (S₁ k) (σ k)) X.p h (W*k_) (Caζ (A j) (a j)) (C*k_) (feeTip X.p F j) (E j) (K j) (z j) (Φ j) from by rw [w.path k]; exact b') q'.rooms q'.period u t' (spinZ ..) had
   rw [he,← heM] at hi; exact ⟨hi,hw.symm ▸ hv⟩)
 refine ⟨A₀,_,⟨hT,b₀,_,_,Q⟩, fun j=>⟨?_,?_⟩⟩
 · rw [Jv,t]; try rfl
 exact listenForce G X Y _ b g U R' _ (i j) j (p.stillE _) (p.stillF _) (w.park j) (w.fire j) v Pz CSP Bm.light K F₁ (fun i g _ D h f=> dash_apply (S₁ j) ..) (fun i v=>(hX.tape i).2 v) (fun i v=>(hT.tape i).2 v)
lemma freshFrame :∃ X V t Φ, CordMint _ P_ G S G₀ G₁ _ Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp p U X V Φ t:=by
 let B:= (p.trust.choose_spec.choose_spec.choose_spec); let a:=B.heat _ _ _ _ _ U; choose E H z Φ v using a.choose_spec.2.2.1
 obtain ⟨Z,T,U⟩:=paints V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp p U hc u₁ u₂ E H z Φ v
 exact ⟨Z,_,_,_,U⟩
-- Reuse at partial Port. s=1 so same actual copy. Need no equality of input high terms.Core site relations only. Returns Cord for this receipt so orientation listeners remain usable.
lemma tradeCore {F':Key I→RegBudget (mid N B)} {A₁:I→ArcΦ}(J': Finset I)(x:CordMint V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp p U F' M₀ A₁ tO)(E:Key I→RegBudget (mid P B))(D:Key I→ ForceBudget (mid P B))(K':I→ArcΦ)(Vw:OrbitPulse G X Y h b g l.L r E D K' a mc) (qL:∀ i∈ J',K' i=A i ∧ passingR (mid P B) 1 (νTip X₁ i) (νTip E i) ∧ passingF (mid P B) 1 (emberTip X₂ i) (emberTip D i)): ∃ R K Φ z, CordMint V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp p Vw R K Φ z ∧ ∀ i∈J', z i=tO i ∧ Φ i=A₁ i ∧ νTip F' i=νTip R i ∧ passingF (mid N B) 1 (emberTip M₀ i) (emberTip K i):=by
 let PW:=p.trust.choose_spec.choose_spec.choose_spec; let M:= PW.heat _ _ _ _ _ Vw; let V₀:= M.choose
 obtain ⟨Yw,Mu,Rb,Hv,W'⟩:= PW.heat _ _ _ _ _ U
 obtain ⟨Vz,F,T',Yk,Wu,Fρ⟩:= x.raw; obtain ⟨f',w',a',v'⟩:= M.choose_spec
 choose E K z Z w using a'; -- E shadow
 let F_:=(fun i=>if i ∈ J' then νTip F' i else E i)
 let G_:=(fun i=>if i ∈ J' then F i else K i)
 let V':=(fun i=>if i ∈ J' then tO i else z i); let T'':=fun i=> if i ∈ J' then A₁ i else Z i
 have hv(Y₁ Y₂:RegBudget (mid P B))(i:I)(p:passingR (mid P B) 1 Y₁ Y₂): passingR (mid P B) (reSweep G 1) Y₁ Y₂ :=by rw [soleR]; exact p
 obtain ⟨R,Z,x'⟩:=paints V P_ G S G₀ G₁ _ _ Xp q d h Vp Vf T W C BQ Rt Zt b g κp p Vw hc u₁ u₂ F_ G_ V' T'' (fun i=>by
    intro k_ r'; by_cases g': i∈J'; swap; · unfold F_ G_ V' T''; simp only [if_neg g']; exact w i
    have t' : passingF (mid P B) (reSweep G 1) (emberTip X₂ i) (emberTip D i):=by rw [soleR]; exact (qL i g').2.2
    have he: feeTip X.p V₀ i=feeTip X.p Vz i:=by
       funext y; have ht:= listens G X Y h b g U Vw 1 i i (p.stillE _) (p.stillF _) (hv _ _ i (qL i g').2.1) t' T' f' Yk w' y; rw [soleV,toon_Q] at ht; exact ht
    unfold F_ G_ V' T'' r'; simp only [if_pos g',(qL i g').1]; rw [show _=_ from he]; exact Fρ i)
 refine ⟨R,_,_, V',x',fun i z=>?_⟩; refine ⟨if_pos z,if_pos z,((Z i).trans (if_pos z)).symm,?_⟩
 have t' : passingF (mid P B) (reSweep G 1) (emberTip X₂ i) (emberTip D i):=by rw [soleR]; exact (qL i z).2.2
 let t':= listenForce G X Y h b g U Vw 1 i i (p.stillE _) (p.stillF _) (hv _ _ i (qL i z).2.1) t' T' f' (p.trust.choose_spec.choose) PW.light F G_ (by unfold G_; rw [if_pos z]; exact parUni _) (fun i v=> (?_)) (fun i v=>(x'.grant.receipts.power.tape i).2 v)
 · rw [Wu]; exact t'
 have hz:=(x.grant.receipts.power.tape i).2 v; rwa [Wu] at hz
end YM.CF.QuadClock
