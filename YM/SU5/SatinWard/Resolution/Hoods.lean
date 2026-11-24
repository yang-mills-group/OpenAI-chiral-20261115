import YM.SU5.SatinWard.Resolution.Seuss
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
open Set Function Finset Metric Filter ENNReal MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal BigOperators ContDiff Classical
noncomputable section
namespace GarnetAct.Cut
local notation "G"=> (Fin 4 → ℝ)
local notation "W"=> (Fin 4 → ℤ)
namespace Curtain
open YM.MacroSix.Grid
abbrev shifter(t:ℝ):G→ W:=tag t
variable (F F':Curtain)(t:ℝ) (h:0<t)
local notation "μ"=> F.ppm
local notation "ν"=> F'.ppm
local notation "x↺"=> shifter t
local notation "Z" u:max=> (region t u)
lemma covered : ∀ᵐ x ∂ F.ppm.prod F'.ppm,x∈ F.boxS ×ˢ F'.boxS := (quasiMeasurePreserving_fst.tendsto_ae.eventually F.inhabits).and (quasiMeasurePreserving_snd.tendsto_ae.eventually F'.inhabits)
include h
lemma shifted_finite : (shifter t '' F.boxS).Finite:=by
 obtain ⟨Z₀,p⟩:= F.ownsK.isBounded.subset_closedBall 0; refine (compact_tags t h (isCompact_closedBall (0:G) (Z₀+t))).subset ?_; rintro _ ⟨x,hx,rfl⟩; change dist (place t (x↺ x)) 0 ≤ Z₀+t; have h₁:dist x 0≤ Z₀:=(p hx); exact (dist_triangle _ x 0).trans (by linarith only [h₁, show dist (place t (x↺ x)) x ≤ t from (dist_comm ..).trans_le (distance_tag t h x)])
abbrev kinSet : Finset W:= (F.shifted_finite t h).toFinset
lemma picked (x:W): x∈F.kinSet t h ↔∃ y∈F.boxS,x↺ y=x:= Set.Finite.mem_toFinset ..
abbrev fare (x:W):ℝ:= (μ).real (Z x)
variable {X : Type*} [NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]
local notation "TK"=> F.kinSet t h
private lemma basePaid (g:W→X)(x:W): Integrable ((Z x).indicator fun _=>g x) μ:= Integrable.indicator (integrable_const _) (measurable_region t h _)
noncomputable def sampling (g:W→X):G→X:= fun u=>∑ i∈TK,(region t i).indicator (fun _=>g i) u
lemma sampling_eq (g: W→X) : sampling F t h g=ᵐ[μ] (g ∘ shifter t):= by
 filter_upwards [F.inhabits] with x hx; unfold sampling; rw [sum_eq_single (shifter t x)]; · exact indicator_of_mem (s:=region t _) rfl _
 · intro j _ k; exact indicator_of_notMem (fun v=> k (Eq.symm (v:tag t x=j))) _
 exact fun u=> False.elim (u ((F.picked ..).2 ⟨x,hx,rfl⟩))
lemma sampler (g: W→X): Integrable (g ∘ shifter t) μ∧ (∫ x:G,g (x↺ x) ∂μ)=∑ i∈TK,F.fare t i • g i:=by
 let T:= F.sampling_eq t h g; refine ⟨(integrable_finsetSum _ (fun i _=>basePaid F t h g i)).congr T,?_⟩; rw [←show (∫ x:G,sampling F t h g x∂ μ)= (∫ x:G,g (x↺ x) ∂μ) from integral_congr_ae T]; unfold sampling; rw [integral_finsetSum _ fun i _=>basePaid F t h g i]; exact sum_congr rfl (fun i _=>by rw [integral_indicator (measurable_region t h i),setIntegral_const])
local notation "R" i:max j:max=> ((region t i) ×ˢ (region t j))
local notation "U"=> F.ppm.prod F'.ppm
local notation "TZ"=> F'.kinSet t h
noncomputable def duo (g:W→ W→ X):G×G→X:= fun u=>∑ i∈F.kinSet t h,∑ j∈ F'.kinSet t h,(R i j).indicator (fun _=>g i j) u
local notation "Ab" x:max=> x↺ (x:G×G).1
local notation "Bb" x:max=> x↺ (x:G×G).2
private lemma duoPaid (g:W→W→X)(x:W){y:W} : Integrable ((R x y).indicator fun _=>g x y) U:= Integrable.indicator (integrable_const _) ((measurable_region t h x).prod (measurable_region t h y))
lemma duo_eq (g:W→ W→X) : duo F F' t h g =ᵐ[U] (fun x=>g (Ab x) (Bb x)):=by
 filter_upwards [covered F F'] with x hx; unfold duo; obtain ⟨h₁,h₂⟩:=hx; rw [sum_eq_single (shifter t x.1)]
 · rw [sum_eq_single (shifter t x.2)]; · exact indicator_of_mem (s:=R (shifter t x.1) (shifter t x.2)) ⟨rfl,rfl⟩ _
   · intro i _ p; exact indicator_of_notMem (fun (q : x∈R (Ab x) i)=>p (Eq.symm (q.2:x↺ x.2=i))) _
   exact fun g=> False.elim (g ((F'.picked ..).2 ⟨x.2,h₂,rfl⟩))
 · intro i _ p; exact Finset.sum_eq_zero fun j _=>indicator_of_notMem (fun (q:x∈ R i j)=>p (Eq.symm (q.1:x↺ x.1=i))) _
 exact fun g=>False.elim (g ((F.picked ..).2 ⟨x.1,h₁,rfl⟩))
lemma resample (g:W→ W→ X) : Integrable (fun x=>g (Ab x) (Bb x)) U∧ (∫ x:G×G,g (Ab x) (Bb x)∂ U)=∑ i∈TK,∑ j∈TZ,(F.fare t i* F'.fare t j) • g i j:=by
 have he:= duo_eq F F' t h g; have ht(i:W): Integrable (fun x=>∑ j ∈ TZ,(R i j).indicator (fun _=>g i j) x) U:= integrable_finsetSum _ fun _ _=>duoPaid F F' t h g i
 refine ⟨(integrable_finsetSum _ fun i _=>ht i).congr he,(integral_congr_ae he.symm).trans ?_⟩; unfold duo; rw [integral_finsetSum _ (fun i _=> ht i)]; refine sum_congr rfl fun i _=>?_; rw [integral_finsetSum _ fun j _=>duoPaid F F' t h g i]; exact sum_congr rfl fun j _=> by rw [integral_indicator ((measurable_region t h i).prod (measurable_region t h j)), setIntegral_const,measureReal_prod_prod]
lemma allHands : ∑ k∈TK,F.fare t k= 1:=by simpa only [integral_const,measureReal_univ_eq_one,one_smul,smul_eq_mul,mul_one] using ((sampler F t h (fun _=>(1:ℝ))).2).symm
end Curtain
end GarnetAct.Cut
