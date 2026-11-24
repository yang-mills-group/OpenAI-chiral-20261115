import YM.SU5.Registration.Momenta.Gallery
/-!
 # Sector budget: lift useful extension to all time-energy smooth vectors in the point sector.
 Purpose: common dense domain including interpolating (positive allow.) operators after their
    width limit and relative convergence, & compare all at Lorentz boosts. From support &
    actual real Lor action. Still on this K.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Set Filter MeasureTheory Measure Complex Submodule SatinRegistration
open Boundary Probe Mink Mink.Poincare Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert}{S: _root_.YM.OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
variable (B:Carton S V)
local notation "D"=> radial S
local notation "G"=> bands S
local notation "Q"=> B.pointShelf
local notation "R"=> B.station
local notation "L"=> B.joinT
open SatinRegistration.Grading
-- grading on the very station. compatible with Grading G in original H.
abbrev pointGrade : Grading B.station where
 P n:= B.joinT.P.region (foldBand timeAxis n)
 real n:= (L).P.real (foldBand_meas n)
 same n:= by rw [(L).P.joins (foldBand_meas _) (foldBand_meas _),inter_self]
 other h:=by rw [(L).P.joins (foldBand_meas _) (foldBand_meas _), disjoint_iff_inter_eq_empty.mp (foldBand_disjoint timeAxis h), (L).P.none] -- implicit
 sum x:= by
   have p:=(L).P.unites (foldBand timeAxis) foldBand_meas (foldBand_disjoint timeAxis) x; rw [foldBand_all,(L).P.all] at p; exact p
local notation "F'"=> B.pointGrade
lemma grade_at (x:B.station)(n:ℕ) : ((F').P n x).1=(G).P n x.val:= B.sees_zone _ (foldBand_meas n) x
lemma price_at (x:B.station)(k:ℕ): (F').due x k=(G).due x.val k:=funext fun n=> by
 change weight k n * ‖((F').P n x).val‖=_; rw [B.grade_at]; rfl
lemma operates_honest (x:B.station)(k:ℕ): (F').budget k x=(G).budget k x.val:= by unfold Grading.budget; simp_rw [B.price_at x]
lemma prices_root (x:B.station): x∈ B.pointGrade.domain ↔ x.val ∈ D :=forall_congr' fun k=>iff_of_eq (congrArg (fun f:ℕ→ℝ=> Summable f) (B.price_at x k))
variable (U:Boundary.Action B.station) (p:B.joinT=U.orbit)
local notation "Y" r:max=>U.V (motion r)
local notation "Zv" n:max=> foldBand timeAxis n
lemma honor_translate (x:E4)(v:R) : (L).P.diagonal ((L).translation x v)=(L).P.diagonal v:=by
 rw [B.sees_m, B.sees_m]; apply Measure.ext_of_charFun; funext t; rw [S.joint, S.joint]; -- unit.moves norm etc
 let f(u) := S.unit.translation u; change inner ℂ (f x v.val) (f t (f x v.val))= _
 have h:(f t).comp (f x)= (f x).comp (f t):= by unfold f; rw [S.unit.sends,add_comm, ← S.unit.sends]
 rw [←ContinuousLinearMap.comp_apply,h]; exact LinearIsometry.inner_map_map (⟨(f x).toLinearMap,S.unit.unitary x⟩ : H→ₗᵢ[ℂ]H) _ _
include p
lemma motion_μ (r:Poincare)(v:B.station): (L).P.diagonal (U.V r v)= ((L).P.diagonal v).map (Lorentz.act (Lorentz.dual r.Λ)):=by
 let r₀:= motion r.Λ; let x:=r.b; let U':=U.V r₀; rw [show U.V r v=(L).translation x (U' v) from ?_,B.honor_translate,p]; exact U.placed _ _
 rw [p]; change U.V r v=U.V (translation x) (U.V (motion r.Λ) v); rw [← ContinuousLinearMap.comp_apply,← U.mult, show translation x * motion r.Λ=r from by apply by_placement; intro y; simp [x,sends,translation,motion]]
-- no triangle Mink inference outside cone. mark measures
lemma unlit (e:(L).P.region Mink.coneᶜ=0) (r:Poincare) (n m:ℕ) (h:∀ x∈ Mink.cone ∩ (Zv n), Lorentz.act (Lorentz.dual r.Λ) x∉ Zv m) (x:R) : ((F').dissect (U.V r)).op m n x=0:=by
 change (F').P m (U.V r ((F').P n x))=_; let y:= (F').P n x; apply ((L).P.null_pair (foldBand_meas m) _).mp;
 rw [B.motion_μ U p, Measure.map_apply _ (foldBand_meas _)]; swap
 · exact (ContinuousLinearMap.continuous _).measurable
 let μ:= (L).P.diagonal y; have he: μ Mink.coneᶜ=0:= ((L).P.null_pair Mink.closed_cone.isOpen_compl.measurableSet y).mpr (by rw [e]; rfl); have hz: μ (Zv n)ᶜ=0:= ((L).P.null_pair (MeasurableSet.compl (foldBand_meas _)) _).2 (by
   change (L).P.region _ ((L).P.region _ x) =_; rw [← ContinuousLinearMap.comp_apply,(L).P.joins (MeasurableSet.compl (foldBand_meas _)) (foldBand_meas _),Set.compl_inter_self,(L).P.none]; rfl)
 exact MeasureTheory.measure_mono_null (show _ ⊆ coneᶜ ∪ (Zv n)ᶜ from fun z hz=>by
   by_contra p'; rw [Set.mem_union, Set.mem_compl_iff,Set.mem_compl_iff] at p'; push Not at p'; exact h z ⟨p'.1,p'.2⟩ hz
 ) (measure_union_null he hz)
omit p
abbrev fluc (r:Lorentz):ℝ:= ‖Lorentz.act (Lorentz.dual r)‖*2+1
lemma fluc_nonneg (r:Lorentz):0 ≤ fluc r:=by unfold fluc; positivity
lemma fluc_fee {x:E4} (e:x∈Mink.cone) (r:Poincare) {n m: ℕ}(p:x∈Zv n) (y:Lorentz.act (Lorentz.dual r.Λ) x ∈ Zv m): (m+1:ℝ) ≤ fluc r.Λ*(n+1:ℝ):=by
 let i:=time x; have ht: 0 ≤ i:=(Mink.cone_self _ |>.mp e).1; have h:‖x‖≤2*i:=le_of_sq_le_sq (by rw [Mink.squares]; have he1:‖spatial x‖ ≤ i:=e; haveI u:(0:ℝ)≤ ‖spatial x‖:= norm_nonneg _; change ‖spatial x‖^2+i^2 ≤ _; nlinarith) (by positivity)
 let c:=Lorentz.act (Lorentz.dual r.Λ); have hv:i≤(n+1:ℝ):=by
    have m:= p; change (n:ℝ) ≤ max 0 i ∧ max 0 i<((↑(n+1:ℕ):ℝ)) at m; rw [max_eq_right ht,Nat.cast_add_one] at m; exact m.2.le
 have hm:= (show (m:ℝ)≤timeOf timeAxis (c x) from y.1).trans ((timeOf_bound _).trans ((c.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h.trans (by gcongr : 2*i≤2*(n+1:ℝ))) (norm_nonneg _))))
 unfold fluc; change _ ≤ (‖c‖*2+1)*(n+1:ℝ); linarith only [hm,Nat.cast_nonneg (α:=ℝ) n]
include p
lemma motion_tariff (k:ℕ) (e:(L).P.region Mink.coneᶜ=0) (r:Poincare) : (B.pointGrade.dissect (U.V r)).Tariff k (k+2) (fluc r.Λ^(k+2)):=by
 have hC:= fluc_nonneg r.Λ
 intro m n; let A:= ((F').dissect (U.V r)).op m n
 change Grading.weight (k+2) m* ‖A‖ ≤ _
 by_cases h:(m+1:ℝ) ≤ fluc r.Λ*(n+1:ℝ)
 · have he: ‖A‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>by rw [one_mul]; exact ((F').project_le _ m).trans ((U.usual r _).le.trans ((F').project_le x n)) -- defeq
   apply le_trans (mul_le_of_le_one_right (Grading.weight_pos (k+2) m).le he); unfold Grading.weight; push_cast; rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h _
 have hv: A=0:= ContinuousLinearMap.ext (B.unlit U p e r n m (fun x p' y=> h (fluc_fee p'.1 r p'.2 y))); rw [hv,norm_zero,mul_zero]; exact mul_nonneg (pow_nonneg hC _) (Grading.weight_pos (k+2) n).le
-- Actual usable extension preserving sector budgets.
lemma important (e:(L).P.region Mink.coneᶜ=0) (r:Poincare)(x:B.station)(u:x∈ (F').domain) : U.V r x∈ (F').domain ∧ ∀ k:ℕ,(F').budget k (U.V r x) ≤ ((∑' n,tariffW n)*fluc r.Λ^(k+2))* (F').budget (k+2) x:=by
 let A:=B.pointGrade.dissect (U.V r); have h:A.Usable:= fun k=> ⟨(k+2),_,pow_nonneg (fluc_nonneg _) _,B.motion_tariff U p k e r⟩; have he:A.reach ⟨x,u⟩ = U.V r x:= A.reaches_whole _ rfl h ⟨x,u⟩; rw [← he]; exact ⟨A.reach_mem h _, fun k=> A.estimate h (B.motion_tariff U p k e r) ⟨x,u⟩⟩ -- rfl
end YM.SatinWFixed.Carton
open YM.SatinWFixed
#print axioms Carton.motion_tariff
#print axioms Carton.important
