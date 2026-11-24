import YM.SatinExist.Pinter
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
variable (A:ℕ→ P.Apron) (r:ℕ) (L:(P.ManyF 3 (P.advocate 3 x 3)).Op)
local notation "K"=> Cache (P.seasons 3 (P.advocate 3 x 3))
noncomputable def chordPaid (i:ℕ): (P.ManyF 3 (P.advocate 3 x 3)).Op:= K (lastTuba D-i) * P.composer x L i* K (lastTuba D-i)
noncomputable def ariaL := ∑ i∈D.support,D i • P.chordPaid x D L (i+1)
abbrev ariaM := r+lastTuba D
variable (Q:P.Concerto x A r L)
local notation "T" i:max=> P.aTuba D (A i)
local notation "U'" i:max => (A i).s
include Q
lemma clockL (k:ℕ) : Tendsto (fun i=> E! (U' i) k) atTop (𝓝 0):=by
 have he: Tendsto (fun i:ℕ=> whenly (timeMesh P.par) i k) atTop (𝓝 0):=by simpa [whenly] using ((vanishes (timeMesh P.par)).const_mul (k:ℝ≥0)); -- fix
 exact he.comp Q.high
lemma chordC (i:ℕ)(h:i≤lastTuba D): P.Concerto x (fun j=> P.gearT (A j) i) (ariaM D r) (P.chordPaid x D L i):=by
 have a:= Concerto.choiceC P x A r L Q i
 rw [show ariaM D r= lastTuba D-i+(r+i) from (by unfold ariaM; omega)]; exact Concerto.waveMore P x _ _ _ a _
lemma tubaL :Tendsto (fun i=> P.zt (P.aTuba D (A i))) atTop (𝓝 0):=by
 have hx(i:ℕ): P.zt (P.aTuba D (A i))=P.zt (A i)+ E! ((A i).s) (lastTuba D+1):=by simp [zt,aTuba,whenly]; ring
 simp_rw [hx]; have h:= Q.thin.add (P.clockL x A r L Q (lastTuba D+1)); simpa only [zero_add] using h
variable (t:ℝ≥0)(p:0<t)
local notation "ℙ" i:max k:max=> P.gearT (A i) k
local notation "W" i:max=> t-P.zt (T i)
local notation "σ" i:max k:max=> E! (U' i) (lilLeft D k)
local notation "B" i:max k:max=> E! (U' i) (lilRight D k)
noncomputable def loftyVo(q i:ℕ):= U (W i)*(U (σ i q)*Λ ((ℙ i q).engine P 3 (P.advocate 3 x 3))* U (B i q))* U (W i)
noncomputable def plateA(i:ℕ): (Y).Op:= plated (R) (r:=ariaM D r) (P.chordPaid x D L i) (t:ℝ)
include p
lemma portsA (i:ℕ)(h:i≤lastTuba D): Brakes (P.loftyVo x D A t i) (plateA P x D r L t i):=by
 let v:=t/2; have hv:0<v:=half_pos p; have hu:v+v=t:= add_halves _; have hl:v<t:=half_lt_self p
 let q(k:ℕ):= (ℙ k i); let r':= ariaM D r; let w(k:ℕ):=P.zt (q k); let X':=P.chordPaid x D L i; let l(k:ℕ):= σ k i; let g(k:ℕ):= B k i; let u(k:ℕ):= W k
 let T':= P.chordC x D A r L Q i h
 let Y'(k:ℕ):= Ψ (q k) v v; let Q':=plated (R) (r:=r') X';
 have hc:Brakes Y' (Q' v):= T'.purchase v hv
 have hf : Tendsto (fun i=> P.zt (T i)) atTop (𝓝 0):= P.tubaL x D A r L Q
 have hb : Tendsto u atTop (𝓝 t):=by simpa [tsub_zero] using ((tendsto_const_nhds (x:=t)).sub hf)
 have hx':Tendsto w atTop (𝓝 0):= T'.thin
 have ho:Tendsto l atTop (𝓝 0):=P.clockL x A r L Q _; have hd:Tendsto g atTop (𝓝 0):=P.clockL x A r L Q _
 let v₀(k):=v-w k;
 have h₁:Tendsto v₀ atTop (𝓝 v):=by simpa [tsub_zero] using ((tendsto_const_nhds (x:=v)).sub hx')
 have he(a):Commute (U a) (U a):=Commute.refl _
 have heℝ(a b:ℝ≥0):U a * U b= U (a+b):=((R).time ..).symm
 let p₁(k:ℕ):=u k + l k-v₀ k; let p₂(k:ℕ):=g k+u k-v₀ k
 have hd:Tendsto p₁ atTop (𝓝 (t-v)):=by simpa only [add_zero] using ((hb.add ho).sub h₁)
 -- oops hd shadows
 have hy:Tendsto g atTop (𝓝 0):=P.clockL x A r L Q _;
 have ht:Tendsto p₂ atTop (𝓝 (t-v)):=by simpa only [zero_add] using ((hy.add hb).sub h₁)
 apply (((Brakes.heatT (R) hd).weave hc).weave (Brakes.heatT (R) ht)).sameC
 · filter_upwards [hb.eventually (le_mem_nhds hl), hx'.eventually (ge_mem_nhds hv)] with k p hT
   have ha₀:v₀ k≤v:=tsub_le_self
   have hb₁: U (p₁ k)*U (v₀ k)=U (u k)*U (l k):=by rw [heℝ,heℝ,tsub_add_cancel_of_le (ha₀.trans ((show v≤u k from p).trans (le_self_add)))]
   have hb₂: U (v₀ k)*U (p₂ k)= U (g k)*U (u k):=by rw [heℝ,heℝ,add_tsub_cancel_of_le (ha₀.trans ((show v ≤ u k from p).trans (le_add_self)))]
   change U (p₁ k) * Y' k * U (p₂ k) = _
   let f:= Λ ((q k).engine P 3 V); unfold Y'; rw [stampPoint _ x _ _ _ hT hT]; change U (p₁ k)*(U (v₀ k)* f*U (v₀ k))*U (p₂ k)= U (u k)*(U (l k)*f* U (g k))* U (u k)
   calc
       _= (U (p₁ k)*U (v₀ k))*f*(U (v₀ k)*U (p₂ k)):=by simp only [mul_assoc]
       _= _:= by rw [hb₁,hb₂]; simp only [mul_assoc]
 have hV: t-v=v:=by nth_rw 1 [← hu]; rw [add_tsub_cancel_right]
 change U (t-v)*Q' (v:ℝ)* U (t-v)= Q' (t:ℝ); unfold Q' plated; rw [Real.toNNReal_coe, Real.toNNReal_coe,hV, show U v=Par (R) 0 v from ((R).roots_heat hv).symm]; simp only [mul_assoc]; rw [PP'_S _ r' 0 hv hv, Nat.add_zero,←mul_assoc _ (Par _ r' _), PP'_S _ 0 r' hv hv, Nat.zero_add,hu]
omit p Q
lemma conduit_rule (f:Test4): ℑ (R) (P.ariaL x D L) f (ariaM D r) = ∑ i∈D.support,D i • ℑ (R) L (((-(εpref (3:Axis)): Test4→L[ℂ] Test4)^[i+1]) f) r:=by
 let S':=R; let H':= P.chordPaid x D L
 let m:= ariaM D r
 have hv (A:Finset ℕ): ℑ (R) (∑ i∈A,D i • H' (i+1)) f m= ∑ i∈A,D i • ℑ (R) (H' (i+1)) f m:=by
    classical
    induction A using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; exact (congrArg (fun a:(Y).Op=> ℑ (R) a f m) (zero_smul ℂ L)).symm.trans ((anyC ..).trans (zero_smul ..)) -- tune
    | insert i A k ih=> rw [sum_insert k,sum_insert k,anyB,ih,anyC]
 refine (hv D.support).trans (sum_congr rfl ?_); intro i t; apply congrArg (fun p:Bench (R)→ₗ[ℂ] Bench (R)=> D i • p); let j:=i+1; have hx:j≤ lastTuba D:=le_sup (f:=fun i=>i+1) t; rw [← composer_pay]; unfold H' m; rw [show ariaM D r= lastTuba D-j +(r+j) from (by unfold ariaM; omega)]; exact (price_same ..).symm
include Q
lemma chordConcert : P.Concerto x (fun i=> T i) (ariaM D r) (P.ariaL x D L):=by
 refine ⟨P.tubaL x D A r L Q,Q.high,fun t p=>?_⟩
 let m:=ariaM D r; let X'(n k:ℕ):=P.loftyVo x D A t n k; let F(n:ℕ):=plateA P x D r L t n; let G(n:ℕ):=P.chordPaid x D L n
 have hp(S:Finset ℕ)(u:S ⊆ D.support):Brakes (fun i=> ∑ j∈S, D j • X' (j+1) i) (∑ j∈S,D j • F (j+1)):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp; exact Brakes.by_budget tendsto_const_nhds
    | insert i S h ih=> simp only [sum_insert h]; exact spline_sum ((P.portsA x D A r L Q t p (i+1) (le_sup (f:=fun i=>i+1) (u (mem_insert_self ..)))).pump (D i)) (ih ((subset_insert ..).trans u))
 apply (hp _ Finset.Subset.rfl).sameC
 · filter_upwards [(P.tubaL x D A r L Q).eventually (ge_mem_nhds p)] with i e; exact (P.piloted_sum x (A i) D _ e).symm
 change _=Par (R) _ _*(∑ i∈D.support,D i • G (i+1))*Par (R) _ _; rw [mul_sum,sum_mul]; refine sum_congr rfl fun i t=>?_ ; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
