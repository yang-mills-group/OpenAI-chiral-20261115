import YM.SatinExist.Vichy
import YM.SatinExist.Mozart
import YM.SatinExist.Chocolate
import YM.SatinExist.Marina
/-! # Price the unbounded-order (over j) Test Card at true widths. Laurent. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 680000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open SatinTails SatinJets Boundary Spectral
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
variable (P:Spine)(x:P.Spectrum0 3)
local notation "C"=>P.calibration
local notation "Mm"=>timeMesh P.par
local notation "X"=>P.ColorHil 3 (P.advocate 3 x 3)
local notation "Y"=>P.ManyF 3 (P.advocate 3 x 3)
local notation "ℰ" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "R"=>P.seasons 3 (P.advocate 3 x 3)
local notation "Λ"=>P.kiosk 3 (P.advocate 3 x 3)
local notation "E"=> (ℰ).E
local notation "U"=> (R).E
local notation "V"=>P.advocate 3 x 3
local notation "E!" s:max i:max=> whenly (timeMesh P.par) s i
local notation "q'" n:max=> P.probeClock n 3
local notation "Ψ" L:max a:max t:max => P.pillar 3 V L (- (a:ℝ)) (t:ℝ) 0
-- card final-op and summing support expense
variable (F:P.Apron)(D:Prism)
local notation "G"=>P.aTuba D F
noncomputable def lilLeft(s:ℕ): ℕ:= lastTuba D + 2 - s
noncomputable def lilRight(s:ℕ): ℕ:= lastTuba D - s
private lemma cashAlign {v w:ℕ}{u p}{n:ℕ}{i:P.Test}{X':(P.ColorHil 3 (P.advocate 3 x 3)).Op}(g:v=w)(x':P.PrismS 3 V n v u i X'): P.PrismS 3 V n w p i X':=by subst v; exact x'
lemma booked_wage {i:ℕ}(h:i≤lastTuba D):
    let m:= F.s; let L:= P.gearT F i; let A:=(G).u 3
    P.PrismS 3 (P.advocate 3 x 3) m (A+A) (by have ht:= (G).pos 3; omega) (P.shifts 3 (A:ℕ) (P.shifts 3 1 L.F)) (E (E! m (lilLeft D i)) * L.engine P 3 V * E (E! m (lilRight D i))) := by
 intro m L A; have hw0: L.s=m:=rfl; let q:= L.u 3; let g:= lilLeft D i; let r:=lilRight D i; let T:=F.u 3;
 have h₁:A=T+lastTuba D+1:=rfl; have h₂:q=T+i:=rfl
 have hu:L.u 3+i=L.u 3+i:=rfl
 have hv:0<q:= L.pos _; have hp:0<g:=by unfold g lilLeft; omega
 have hr:P.PrismS 3 V m (q+q) (add_pos hv hv) (P.shifts 3 q L.F) (L.engine P 3 V):=P.meterRule0 3 V L
 have h' := P.cashMul 3 V (P.cashOne 3 V hp) hr
 have he: (g:ℤ)+q=A+1:=by unfold g lilLeft; omega
 rw [one_mul,P.shifts_sum,he] at h'
 change P.PrismS 3 V _ _ _ _ (_*_*(E (E! m r)))
 rw [P.shifts_sum]
 rcases eq_or_ne r 0 with f|f
 · have hu:g+(q+q)=A+A:=by unfold g lilLeft; unfold r lilRight at f; omega
   rw [f,when_zero,(ℰ).eZero,show ContinuousLinearMap.id ℂ _ = (1:(X).Op) from rfl,mul_one]
   exact P.cashAlign x hu h'
 have hp:0<r:=Nat.pos_of_ne_zero f
 have hz:=P.cashMul 3 V h' (P.cashOne 3 V hp)
 rw [map_one,mul_one] at hz
 exact P.cashAlign x (by unfold g r lilLeft lilRight; omega) hz
#check Finset.sum_smul
lemma lernt : (G).engine P 3 V= ∑ i∈D.support,D i • (E (E! F.s (lilLeft D (i+1))) * (P.gearT F (i+1)).engine P 3 V * E (E! F.s (lilRight D (i+1)))):=by
 let q(i:ℕ):=(P.gearT F (i+1)); let d:=(G).u 3
 let x'(i:ℕ):=P.shifts 3 d (P.shifts 3 1 (q i).F)
 let P'(i:ℕ):= E (E! F.s (lilLeft D (i+1))) * (q i).engine P 3 V * E (E! F.s (lilRight D (i+1)))
 let u:=(G).pos 3; have hp:=add_pos u u
 have hv: P.shifts 3 d (G).F=∑ i∈D.support,D i • x' i:=by
    change P.shifts 3 d (P.shifts 3 1 (P.drumroll F.s F.F D))= _; unfold drumroll; simp_rw [map_sum,map_smul]; rfl
 apply P.values_too 3 V F.s (d+d) hp (P.meterRule0 3 V (G))
 rw [hv]; exact P.prism_screen 3 V _ _ _ _ _ x' P' (fun i t=> P.booked_wage x F D (le_sup (f:=fun i=>i+1) t))
lemma piloted_sum(t:ℝ≥0)(h:P.zt (G)≤t):
    let W:= U (t-P.zt (G))
    (Ψ (G) t t)=∑ i∈ D.support,D i • (W*(U (E! F.s (lilLeft D (i+1))) * Λ ((P.gearT F (i+1)).engine P 3 V)* U (E! F.s (lilRight D (i+1))))*W):=by
 intro W; obtain ⟨L,hL⟩:=P.kioskL 3 V;
 rw [P.stampPoint x (G) t t h h, P.lernt, ←hL, map_sum];
 simp_rw [map_smul,hL,P.projectionLingo]; rw [mul_sum,sum_mul]; refine sum_congr rfl fun i q=> ?_
 rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc] -- tune
-- estimates at election
local notation "ν"=> P.pillar 3 V
local notation "K"=> Cache (R)
variable (A:ℕ→ P.Apron) (r:ℕ) (L:(P.ManyF 3 (P.advocate 3 x 3)).Op)
structure Concerto :Prop where
   thin : Tendsto (fun i=>P.zt (A i)) atTop (𝓝 0)
   high : Tendsto (fun i=>(A i).s) atTop atTop
   purchase (a:ℝ≥0)(u:0<a): Brakes (fun i=> P.pillar 3 (P.advocate 3 x 3) (A i) (-(a:ℝ)) a 0) (plated (r:=r) (P.seasons 3 (P.advocate 3 x 3)) L (a:ℝ))
-- inherits
variable (Q:P.Concerto x A r L)
include Q
lemma Concerto.waveMore(m:ℕ): P.Concerto x A (m+r) (K m * L * K m):=by
 refine ⟨Q.thin,Q.high,fun a u=> ?_⟩
 let f:=plated (r:=r) (R) L
 have ht:RealMint (R) r f L:=fun t p=> by unfold f plated; rw [Real.toNNReal_coe]
 have h': f ↑a=plated (r:=m+r) (R) (K m * L * K m) ↑a:= Eq.trans (RealMint.increases _ _ _ _ ht m a u) (by unfold plated; rw [Real.toNNReal_coe])
 exact (Q.purchase a u).sameC (Eventually.of_forall fun i=>rfl) h'
lemma moreConc : P.Concerto x (fun i=>P.gearT (A i) 1) (r+1) (oneJet (R) L):=by
 let e(i:ℕ):=P.burst (A i).s; have he:Tendsto e atTop (𝓝 0):= P.burst_zero.comp Q.high
 let V'(i):= P.gearT (A i) 1; let g(i):= P.zt (V' i)
 have hg:Tendsto g atTop (𝓝 0):=by
    unfold g V'; simp_rw [P.ztd]; exact ((add_zero (0:ℝ≥0)) ▸ Q.thin.add he)
 refine ⟨hg,Q.high,fun t p=>?_⟩
 let b:=t/2; have hb:0<b:=half_pos p
 let L':=(Ψ (A 0) t t); have ht:= braid (R) L e he (fun i=>P.burst_p _) b hb r (Q.purchase b hb)
 apply ht.sameC
 · filter_upwards [hg.eventually (ge_mem_nhds hb)] with i p
   have h:t=b+b:=(add_halves t).symm
   refine (P.voucher_LocalFieldBounds x _ r b (show P.zt (P.gearT (A i) 1) ≤ b from p)).symm.trans ?_; rw [←h]
 rw [show b+b=t from add_halves t]
omit Q
noncomputable def composer(i:ℕ): (Y).Op := ((oneJet (P.seasons 3 (P.advocate 3 x 3)))^[i]) L
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
lemma composer_pay(i:ℕ) (f:Test4) : ℑ (R) (P.composer x L i) f (r+i)=ℑ (R) L (((-(εpref (3:Axis)): Test4→L[ℂ] Test4)^[i]) f) r:=by
 induction i generalizing f with
 | zero=> rfl
 | succ i ih=>
    unfold composer
    rw [Function.iterate_succ_apply', show r+(i+1)=r+i+1 from by omega,eventScalar]; exact ih _
include Q
lemma Concerto.choiceC (i:ℕ): P.Concerto x (fun j=> P.gearT (A j) i) (r+i) (P.composer x L i):=by
 induction i with
 | zero=> exact Q
 | succ i ih=>
    have hp:=P.moreConc x _ _ _ ih; change P.Concerto x (fun j:ℕ=> P.gearT (P.gearT (A j) i) 1) _ _ at hp
    simp_rw [P.gearH] at hp
    unfold composer; rw [Function.iterate_succ_apply', ← add_assoc]; exact hp
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
