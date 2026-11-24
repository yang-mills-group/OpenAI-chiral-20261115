import YM.CF.Forge.Tea
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Forge
open AnalyticBridge.SectorAffine
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open Pressure.Tube Exterior Bloch Oriented Work.E03
section band
local notation "G"=>SU.group
variable {T:Tube G S}{r n:ℕ}{X:Support c}{U V:Monk G S}
variable (s:Signed)(h:Duo G S U V X)(hr:Ready T x)(hp:1000 ≤ radiusB x)(hz:shovel S.patch+10 ≤ radiusB x)
local notation "b"=>radiusB x
local notation "R"=>Stores.till x
local notation "U₀"=>U.sent x T q d l β
local notation "V₀"=>V.sent x T q d l β
local notation "Uc"=>pull s 0 U.V
local notation "Vc"=>pull s 0 V.V
local notation "Uf"=>pull s 0 U₀
local notation "Vf"=>pull s 0 V₀
local notation "A"=> turnStore s U.key
local notation "O"=> turnStore s V.key
local notation "Au"=> traceZ (turnStore s U.key).flags
local notation "Ou"=> traceZ (turnStore s V.key).flags
local notation "WA"=> wV T R (temp x) (traceZ (turnStore s U.key).flags) Uc
local notation "W'"=>wV T R (temp x) (traceZ (turnStore s V.key).flags) Vc
variable (w:ℝ)(L: Stores S)
local notation "ψ"=> layS q U.k U.key x w U₀ U.V s
local notation "ψ'"=>layS q V.k V.key x w V₀ V.V s
include s h hr hp
lemma nearG{ι:Type}(P: Config SU.group c→ι→Twin c→Pay SU.group)(m:ι→Site c)(i:ι)(H:∀j,(R<separation (m i) j.1.1→P Uc i j=0)∧(AgreeNear id (m i) R Uc Vc→P Uc i j=P Vc i j))(p:Beat.shadows (o:=s.act (m i)) X (18*b)): zip (P Uc) WA i= zip (P Vc) W' i:=by
 have hp':R ≤ b:=Nat.div_le_self ..; exact Lift.zipAt R _ _ (m i) i P _ _ H (cu_b s h hr hp _ (aroundBk X p (by rw [separation_self]; omega))) (fun j u=> (lo_b s h hr hp j (aroundBk X p (by rw [separation_signed]; omega))).1)
include hz
lemma toothS(i:Bond c)(p:Beat.shadows (o:=s.act i.1) X ((l+71)*b)): ψ i=ψ' i:=by
 have hp := cu_b s h hr hp i.1 (r:=0) (aroundBk X p (by simp_rw [Nat.add_mul,separation_self]; omega))
 unfold layS prism; simp only; rw [hp i (by simp),(h.turnI hr ‹_› hz (sendEdge s 0 i) w (aroundBk X p ?_)).1]
 have hh:=Background.setback i.1 s i; rw [separation_self] at hh; simp_rw [Nat.add_mul]; omega
lemma wakeG{i:Twin c}(p:Beat.shadows (o:=s.act i.1.1) X ((l+75)*b))(hv:spanO T x): kC T R (temp x) Au Uc i.1 + (kL T R (temp x) Au Uc Uf ψ i.1+kD T R (temp x) Au Uc i.1) = kC T R (temp x) Ou Vc i.1 +(kL T R (temp x) Ou Vc Vf ψ' i.1+kD T R (temp x) Ou Vc i.1):=by
 let t:=temp x; let o:=i.1; let P(x:Twin f):=S.ratio.parent x.1.1; have hp':R ≤ b:=Nat.div_le_self ..
 have ht{y:Site c}{c':ℕ}(u:c'+ R ≤ (l+75)*b)(v:separation i.1.1 y ≤ R):Beat.shadows (o:=s.act y) X c':=aroundBk X p (by rw [separation_signed]; omega)
 have he(j:Bool):Beat.shadows (o:=s.act i.1.1) X (16*b):=ht (y:=i.1.1) (by simp_rw [Nat.add_mul]; omega) (by simp)
 have hu(j:Bool) := lo_b s h hr hp (i.1,j) (he j)
 have hh:AgreeNear id i.1.1 (2*R) Uc Vc:= cu_b s h hr hp _ (ht (by simp_rw [Nat.add_mul]; omega) (by simp))
 unfold kC kL kD; refine congrArg₂ (·+·) ?_ ?_
 · unfold king; refine congrArg₂ (·-·) ?_ ?_ -- tune
   · refine sum_congr rfl fun j _=> ?_; rw [(hu j).2.2]; have h:= (show WA (i.1,j)= _ from (hu j).1); rw [h]
   rw [(hu true).1,(hu true).2.1]
 refine congrArg₂ (·+·) ?_ ?_
 · refine sum_congr rfl fun j _=>?_ ; have hL:= (show WA (i.1,j)=_ from (hu j).1)
   rw [hL,(hu j).2.2, paidZip (T.Φ R) (T.Xf R Uf) (T.Xf R Vf) P (i.1,j) R (Lift.vBand T R) hh (fun z hz=> (hi_b (q:=q) (d:=d) (β:=β) (l:=l) s h hr hp z hv (ht (by simp_rw [Nat.add_mul]; omega) hz)).2.2), paidZip (T.Φ' R) (kZ (S:=S) ψ) (kZ (S:=S) ψ') Prod.fst (i.1,j) R (Lift.kickBand T R) hh (fun z u=>congrArg (fun m=>Real.sqrt S.kernel.penalty • curvatureL G m) (toothS (q:=q) (d:=d) (β:=β) (l:=l) s h hr hp hz w z (ht (by simp_rw [Nat.add_mul]; omega) u)))] -- tune
 refine sum_congr rfl fun j _=>?_ ; have hL:= (show WA (i.1,j)=_ from (hu j).1); rw [hL]
 rw [paidZip (T.Φ R) (zF T R (temp x) Au Uc) (zF T R (temp x) Ou Vc) P (i.1,j) R (Lift.vBand T R) hh (fun z u=>nearG s h hr hp (T.Φ R) P z (Lift.vBand T R Uc Vc z) (ht (by simp_rw [Nat.add_mul]; omega) u)), paidZip (T.Φ' R) (zI T R (temp x) Au Uc) (zI T R (temp x) Ou Vc) Prod.fst (i.1,j) R (Lift.kickBand T R) hh (fun z u=> nearG s h hr hp (T.Φ' R) Prod.fst z (Lift.kickBand T R Uc Vc z) (ht (by simp_rw [Nat.add_mul]; omega) u)), paidZip (T.N R) (zip (T.N R Uc) WA) (zip (T.N R Vc) W') Prod.fst (i.1,j) R (payBand T R) hh (fun z u=>nearG s h hr hp (T.N R) Prod.fst z (payBand T R Uc Vc z) (ht (by simp_rw [Nat.add_mul]; omega) u))]
lemma vixen (L:Stores S)(i:ℕ)(hu: spanO T x)(p:L.dome (i + (l+75)*radiusB x) ⊆ X): caseP T x U.key U.k q w U₀ U.V s (anchorage (turnStore s L) i) = caseP T x V.key V.k q w V₀ V.V s (anchorage (turnStore s L) i):=by
 let P:=turnStore s L; let t:=temp x; have he{x':Site c}{r:ℕ}(hv:r ≤ (l+75)*b)(u:x'∈P.dome i): Beat.shadows (o:=s.act x') X r:=by
    obtain ⟨k,hp,ht⟩:= halo_spec.mp ((dome_turn s L i x').mp u)
    intro y v; obtain ⟨z,w,v⟩:=halo_spec.mp v; rw [mem_singleton.mp w] at v; exact p (halo_spec.mpr ⟨k,hp,(separation_triangle k (s.act x') y).trans (by omega)⟩)
 unfold caseP ore; refine congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg₂ (·+·) (sum_congr rfl fun j h'=>?_) (sum_congr rfl fun j h'=>?_)) (sum_congr rfl fun j h'=>?_)) (sum_congr rfl fun j h'=>?_)
 · have hk:S.ratio.parent j.1∈P.dome i:=(mem_filter.mp h').2; unfold kF; have hx(a:Bool):=hi_b (U:=U) (V:=V) (β:=β) (d:=d) (q:=q) (l:=l) s h hr hp (j,a) hu (he (Nat.mul_le_mul_right _ (by omega)) hk); refine congrArg₂ (·+·) ?_ (sum_congr rfl fun a _=>?_); unfold king; rw [(hx true).1,(hx true).2.1]; unfold zF; rw [nearG s h hr hp (T.Φ R) (fun (v:Twin f)=>S.ratio.parent v.1.1) (j,a) (Lift.vBand T R _ _ _) (he (by simp_rw [Nat.add_mul]; omega) hk), (hx a).2.2]
 · have hk:j.1∈ P.dome i:=(mem_filter.mp h').2; have hx : ψ j=ψ' j:=toothS s h hr hp hz w _ (he (by simp_rw [Nat.add_mul]; omega) hk); unfold kI zI kZ; rw [nearG s h hr hp (T.Φ' R) Prod.fst j (Lift.kickBand T R _ _ _) (he (by simp_rw [Nat.add_mul]; omega) hk),hx]
 · exact wakeG s h hr hp hz w (i:=(j,true)) (he le_rfl ((mem_filter.mp h').2)) hu
 unfold kN; rw [nearG s h hr hp (T.N R) Prod.fst j (payBand T R _ _ _) (he (by simp_rw [Nat.add_mul]; omega) ((mem_filter.mp h').2))]
end band
end YM.CF.Forge
