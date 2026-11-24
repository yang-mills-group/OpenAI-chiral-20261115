import YM.SU5.May.TorqueCap
import YM.SU5.May.TorqueSchur
/-! # capacity retained. costs. Notice NO μ smoothness, actually only needs prob kernels.
      ℓ² budgets composite. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Advance.Whorl
open Function Fock NormedSpace SU Lat Lattice Spire Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree Vault Fir Peaks Drapes Tap Precision Tree Next.SectorChange Stencil RG
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical ENNReal
attribute [local instance] opCStarAlgebra
open Hygrometry Flare
variable (R:Patch){N P : Side} (G : Ratio N P) (hs:G.count=R.L) (A : RG.StepData (More N) (More P))
variable (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)
local notation "L" => G.count.val
variable {k κ κ' : ℕ} (p : LaurentRadius R.J G.count k)(U:Support (More N)) (z:Nom N P)
variable {b:Bool}{ρ c:ℝ}
open Buffered.Stent.Purchase
noncomputable abbrev additionB (x:ℝ) := (Real.sqrt G.count.val)⁻¹ * (Real.exp (lockPrice*‖Q‖)*x)
local notation "W" => padded G U (clothRadius G.count k)
noncomputable abbrev scout (x: Reader0 (Single N)): Reader0 (Single P):= (x.1,(byMode G R.J Q M z (!x.1)) x.2)
include hs p ho
lemma carried (x: Reader0 (Single N))(h:Worth (Tset N) (modesIn N U) ρ x): Worth (Tset P) (modesIn P (padded G U (clothRadius G.count k))) (additionB G Q ρ) (scout R G Q M z x):=by
 refine ⟨?_,mode_support G R.J Q M ho U p h.touches (!x.1), (byMode_bill R G hs z p M (!x.1) Q x.2).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h.budget (Real.exp_nonneg _)) (by positivity))⟩
 rcases x with ⟨g,x⟩; cases g; exact carried_up G R.J Q M ho z true h.limb; exact carried_down G R.J Q M ho z false h.limb
omit hs p in
lemma reversed (C:List (Reader0 (Single N)))(h:∀ i∈ C,Worth (Tset N) (modesIn N U) ρ i): subF G R.J Q M ho z (rollC ton C)= rollC ton (C.map (scout R G Q M z)):=by
 have h(C: List (Reader0 (Single N)))(i:∀ j∈ C,Worth (Tset N) (modesIn N U) ρ j): Fine (Tset N) (modesIn N U) (wheat C) (rollC ton C):=by induction C with
  | nil=>exact Fine.one | cons x C ih=>exact (i x (by simp)).fine.grow (ih fun y v=> i y (List.mem_cons_of_mem x v)) -- shadows
 rename_i h' -- unnecessary? shadow name h
 induction C with
 | nil=> exact sub_one ..
 | cons i C ih=>
   let g:=h' i (by simp); have hx:= fun j (z:j∈C)=> h' j (List.mem_cons_of_mem i z)
   change subF G R.J Q M ho z (ton i* rollC ton C)=ton (scout R G Q M z i)* _; rw [sub_mul G R.J Q M ho z g.fine (h _ hx),ih hx]; apply congr_arg (· * _)
   rcases i with ⟨⟨⟩,i⟩; exact sub_create G R.J Q M ho z (v:=i) g.limb; exact sub_remove G R.J Q M ho z (v:=i) g.limb
lemma tariffF {f:FC (Single N)}(u:f∈Fort (Tset N) (modesIn N U) b κ ρ c): subF G R.J Q M ho z f ∈ Fort (Tset P) (modesIn P (padded G U (clothRadius G.count k))) b κ (additionB G Q ρ) c:=by
 refine passFort isClosed_closure _ ((subF ..).continuous_of_finiteDimensional) ?_ u; rintro x ⟨J,g,F,w,f,t,rfl⟩; apply subset_closure; simp_rw [map_sum,map_smul,reversed R G Q M ho U z _ (fun i=>(f _).allKeys i)]; refine ⟨J,g,fun x=>(F x).map (scout R G Q M z),w,fun i=> ?_,t,rfl⟩
 refine ⟨fun v ht =>?_,by simpa using (f i).size,by rw [←(f i).poll,wheat_grade,wheat_grade,List.length_map]⟩; obtain ⟨x,d,rfl⟩:=List.mem_map.mp ht; exact carried R G hs Q M ho p U z x ((f i).allKeys _ d)
omit hs p ho
noncomputable def Maintain (N:Side)(b:Bool)(κ:ℕ)(ρ c:ℝ)(U:Support (More N))(f:Mark N) : Prop:=∀ X,f X∈ Fort (Tset N) (modesIn N U) b κ ρ c
lemma scopeF {U V: Support (More N)} (p:U⊆V){f:Mark N}(u:Maintain N b κ ρ c U f){x y:ℝ}(g:ρ≤x)(h:c≤y):Maintain N b κ x y V f:= fun i=>increasedF (modes_monotone p) g h le_rfl (u i)
private lemma forestPass (sc:0≤c){I:Type*}[LinearOrder I][Fintype I]{A S: Finset I} (f:Forest G→ FC I)(v:∀ x, f x∈Fort A S b κ ρ c): avgF f∈Fort A S b κ ρ c:= by
 cases isEmpty_or_nonempty (Forest G) with
 | inl h=> simp_rw [avgF,Finset.univ_eq_empty,sum_empty, smul_zero]; exact subset_closure (capital_zero sc)
 | inr h=>
   let w:= (Fintype.card (Forest G):ℝ)⁻¹
   have hw: ∑ _i: Forest G, w=1:= by unfold w; simp only [sum_const,card_univ,nsmul_eq_mul]; apply mul_inv_cancel₀; positivity
   rw [avgF, Finset.smul_sum]; exact capital_convex.closure.sum_mem (fun _ _=> (by positivity)) hw (fun i _=>v i)
-- forestPass params {M} unused Lean not inserts? explicit binder {M: ...} REMOVE.
private lemma paidDensity_t (μ:Measure (Pane N)) [IsProbabilityMeasure μ]{A:Finset (Single P)}{f:Pane N→ FC (Single P)} (g:Pane N→ ℝ) (h:AEMeasurable g μ)(p:Integrable g μ)(u:∀ x,0≤g x)(q:(∫ x,g x ∂μ)=1)(v:∀ x,f x∈Fort (Tset P) A b κ ρ c)(sc:0≤c) : (∫ x,g x • f x ∂μ)∈ Fort (Tset P) A b κ ρ c:=by
 let G:= μ.withDensity (fun x=> ENNReal.ofReal (g x)); have he:IsProbabilityMeasure G:= by constructor; unfold G; rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal p (Filter.Eventually.of_forall u),q]; exact ENNReal.ofReal_one -- indentation after `constructor`
 have hp(X:Pane N→ FC (Single P)): (∫ x,g x • X x ∂μ)=∫ x,X x ∂G:=by unfold G; rw [integral_withDensity_eq_integral_toReal_smul₀ h.ennreal_ofReal (Filter.Eventually.of_forall (fun x=> ENNReal.ofReal_lt_top))]; simp_rw [ENNReal.toReal_ofReal (u _)]
 rw [hp]; by_cases i:Integrable f G
 · exact capital_convex.closure.integral_mem isClosed_closure (Filter.Eventually.of_forall v) i
 rw [integral_undef i]; exact subset_closure (capital_zero sc)
include hs p ho
lemma mayRaise (v:A.patch.Branches A.kernel SU.group) (sc:0≤c) {f:Mark N}(h:Maintain N b κ ρ c U f): Maintain P b κ (additionB G Q ρ) c (padded G U (clothRadius G.count k)) (pushMark G A R.J Q M ho q d β l f):=by
 let hk:= A.isKernel v β; intro X; unfold pushMark linkLaw; refine paidDensity_t (P:=P) (prior SU.group _) _ (hk.integrable X.1).aemeasurable (hk.integrable X.1) (hk.positive X.1) (hk.total X.1) (fun x=>?_) sc
 unfold assembled; let T (i:Ids N):= gathered G R.J Q M ho q d f X (drawn l (x,i))
 by_cases u:Integrable T (depot N)
 · exact capital_convex.closure.integral_mem isClosed_closure (Filter.Eventually.of_forall (p:=fun i=>T i∈Fort (Tset P) (modesIn P (padded G U (clothRadius G.count k))) b κ (additionB G Q ρ) c) fun i => forestPass (ratio G) sc _ (fun t=>tariffF R G hs Q M ho p U _ (h (drawn l (x,i))))) u -- need decidables etc.
 rw [integral_undef u]; exact subset_closure (capital_zero sc)
#print axioms reversed
#print axioms mayRaise
end YM.CF.Buffered.Advance.Whorl
