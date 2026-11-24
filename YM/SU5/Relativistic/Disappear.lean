import YM.SU5.Relativistic.Intervals
import YM.SU5.Relativistic.CubicAverage
import YM.SU5.Selected.Conveyance
import YM.SU5.FiniteGaugeData.Tower.Multigrid
/-!
# Killing excluded directions by mesh Riemann average, substitution proof
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Finset Set Filter InnerProductSpace Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
section flights
variable {I K:Type*}[Fintype I]{H:Hilbert}(M:Mesh)(P:Alliance K (marks M) H)(e:K→I)
local notation "L"=> M.L
local notation "N" t:max k:max => notch M t k
local notation "U" t:max => P.raw t
local notation "π" i:max => (P.crew i).pi_c

lemma misscost (l:List K)(u v':K→Stamp M)(h:∀i∈l,u i=v' i):(U l) u=(U l) v':=by
 induction l with
 | nil=> rfl
 | cons i l ih=> rw [P.raw_step,P.raw_step,h i List.mem_cons_self,ih (fun i k=>h i (List.Mem.tail _ k))]
lemma raw_norm (l:List K) (u:K→Stamp M)(x:H) : ‖(U l) u x‖=‖x‖:=by
 induction l with
 | nil=> rfl
 | cons i l ih=>rw [P.raw_step,ContinuousLinearMap.comp_apply,(P.crew i).wins,ih]

local notation "B" l:max n:max t:max c:max => (P.raw l (fun i=> notch M (n+t) ((c (e i)).val:ℤ)))
lemma first_measure (h:Injective e) (l : List K) (p:l.Nodup) (n t:ℕ) (x:H):
    Average.center (fun i:I→ Fin (M.L^t)=> (B l n t i) x) = Rides.first M P l n t x := by
 letI : Nonempty (Fin (M.L^t)):= avg_lives M t
 induction l with
 | nil=> exact Average.constant (A:=I→ Fin (M.L^t)) x
 | cons i l ih=>
    let a:=e i; let C (v' : Fin (M.L^t))(z:Average.Other I (e i)→ Fin (M.L^t)):= (Equiv.funSplitAt (e i) (Fin (M.L^t))).symm (v',z)
    let q:= Classical.choice (avg_lives M t)
    obtain ⟨hj,ht⟩:= List.nodup_cons.mp p
    have hk(v' : Fin (M.L^t)) (z: Average.Other I (e i)→ Fin (M.L^t)): (B l n t (C v' z))=(B l n t (C q z)):=by
       apply misscost
       intro j u; have hz:e j ≠ e i:=fun k=> hj (h k ▸ u)
       unfold C; rw [Average.stands _ _ _ hz, Average.stands _ _ _ hz]
    rw [Average.point (e i), Rides.first_step, ContinuousLinearMap.comp_apply, ← ih ht, Average.point (e i) (fun k: I→ Fin (M.L^t)=> (B l n t k) x)]
    have hy(v' : Fin (M.L^t)) (z: Average.Other I (e i)→ Fin (M.L^t)) :
        (B (i::l) n t (C v' z)) x=(P.crew i).play (N (n+t) v'.val) ((B l n t (C q z)) x):=by
       rw [P.raw_step,hk,ContinuousLinearMap.comp_apply,show C v' z (e i)=v' from Average.stops (e i) (v',z)]
    change Average.center (fun j:Fin _ => Average.center (fun z=> (B (i::l) n t (C j z)) x))= average M (P.crew i) (n+t) t (Average.center (fun j:Fin _=> Average.center (fun z=> (B l n t (C j z)) x)))
    have hZ: (fun j:Fin _=>Average.center (fun z=> (B l n t (C j z)) x))=fun _=> Average.center (fun z=> (B l n t (C q z)) x) := funext fun j => Average.eq_of _ _ (fun z=> by rw [hk])
    rw [hZ,Average.constant,avgvalue M (P.crew i)]
    apply Average.eq_of; intro j
    rw [←Average.natural _ ((P.crew i).play _)]; exact Average.eq_of _ _ (fun z=> hy j z)

lemma crew_leaves (a b:K)(s:ℕ) (x:H): roller M (P.crew a) s ((π b) x)=(π b) (roller M (P.crew a) s x):= by
  apply tendsto_nhds_unique (rolls M (P.crew a) s _); have hi := (π b).continuous.continuousAt.tendsto.comp (rolls M (P.crew a) s x)
  refine Tendsto.congr' ?_ hi; apply Eventually.of_forall; intro t
  change (π b) (average M (P.crew a) (s+t) t x)= average M (P.crew a) (s+t) t ((π b) x); rw [avgvalue M (P.crew a),avgvalue, ← Average.natural]; exact Average.eq_of _ _ (fun i=> congrArg (fun u:H.Op=>u x) ((P.crew b).commutes_c _ (fun i' => P.cCom b a i' (N (s+t) (i.val:ℤ)))).symm) -- sign tune
lemma crew_preserved (l:List K)(b:K)(s:ℕ)(x:H): Rides.camp M P l s ((π b) x)=(π b) (Rides.camp M P l s x):=by
 induction l with
 | nil=> rfl
 | cons i l ih=>rw [Rides.camp_step,ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ih]; exact crew_leaves M P i b s _
lemma crew_plan (l:List K)(s:ℕ)(x:H) : Rides.camp M P l s (P.stackS l x)=Rides.camp M P l s x := by
 induction l with
 | nil=> rfl
 | cons i l ih=>rw [Rides.camp_step,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,P.shel_step,ContinuousLinearMap.comp_apply, crew_preserved M P l i s, ih,clear_course] -- tune Rides.camp_step already both uses single rw?
local notation "μ" q:max => MeasureTheory.volume.restrict (OBox q)

lemma constant_gap (l:List K)(p:l.Nodup)(g:Injective e)(b:K→ Stamp M)(x:H)(n:ℕ) :
    Tendsto (fun t:ℕ=>Average.center (fun i:I→ Fin (M.L^t)=> P.raw l (b+(fun k=> notch M (n+t) ((i (e k)).val:ℤ))) (x-P.stackS l x))) atTop (𝓝 0):=by
  simp only [P.travelR,ContinuousLinearMap.comp_apply,Average.natural]
  simp_rw [first_measure M P e g l p]
  have hh : Tendsto (fun i=> Rides.first M P l n i (x - P.stackS l x)) atTop (𝓝 0):=by
    have hh:= Rides.consec M P l (x - P.stackS l x) n; rw [map_sub,crew_plan,sub_self] at hh; exact hh
  simpa only [map_zero,Function.comp_def] using ((P.raw l b).continuous.tendsto 0).comp hh -- tune
end flights
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.constant_gap
