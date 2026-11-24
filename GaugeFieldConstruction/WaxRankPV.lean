import GaugeFieldConstruction.ChalkRankPV
/-
# Class component real table
-/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
noncomputable section
namespace YM.GaugeFieldConstruction.Sunpath
open Calibration Raw Filter Module Function Cauchy Conj Ortho Ember LabelAction U1 Row Record
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate Classical
variable {I K:Type*}(R:Record I K){H: Flip I}{δ φ:Submodule ℂ (J I)}
local instance δγ (δ:Submodule ℂ (J I)): AddCommGroup δ:= @Submodule.addCommGroup ℂ (J I) _ _ _ _
local instance αΓ {δ:Submodule ℂ (J I)}{V:Type*}{A:Labels V} : AddCommGroup (R.allowed A δ):= @Submodule.addCommGroup ℂ (V→J I) _ _ _ _
local instance ωΓ (δ:Submodule ℂ (J I)): AddCommGroup ((WW R δ).prod (VV R δ)):= @Submodule.addCommGroup ℂ _ _ _ _ _
local instance αt (δ:Submodule ℂ (J I)): AddCommGroup ↥(TT R δ):= @Submodule.addCommGroup ℂ _ _ _ _ _
local instance αw (δ:Submodule ℂ (J I)): AddCommGroup ↥(WW R δ):= @Submodule.addCommGroup ℂ _ _ _ _ _
local instance αv (δ:Submodule ℂ (J I)): AddCommGroup ↥(VV R δ):= @Submodule.addCommGroup ℂ _ _ _ _ _
variable (Q: Grade R H δ)(τ: Grade R H φ)
include Q in
private theorem awePV {V:Type*}(A: Labels V)(x:R.allowed A δ): (fun i: V=>H (x.val i))∈R.allowed A δ := by
 let u (i:V) : δ:=⟨x.val i, x.property.2 i (Set.mem_univ i)⟩
 let v (i:V) : δ:=⟨_,Q.way (u i)⟩
 refine ⟨(Q.toCarries.turn_field A v).mpr ?_,fun i h=>(v i).property⟩
 intro s i
 have hg:= (Q.toCarries.turn_field A u).mp x.property.1 s i
 apply Subtype.ext
 rw [← Q.star s (u i) (v i) rfl,hg]
 cases A.cost s i <;> first | rfl | exact map_neg ..
def monthPV {V:Type*} (A:Labels V)(τ:Grade R H φ): R.allowed A φ→ₛₗ[bar] R.allowed A φ where
 toFun x:=⟨_,awePV R τ A x⟩
 map_add' _ _:= Subtype.ext (funext fun _=>map_add ..)
 map_smul' a x:= Subtype.ext (funext fun i=>LinearMap.map_smulₛₗ _ a (x.val i))

lemma datePV {V:Type*}(A:Labels V)(h:Function.Involutive H): Function.Involutive (monthPV R A τ):=by
 intro x; exact Subtype.ext (funext fun i=>h (x.val i))
def yellowPV (τ:Grade R H φ): ↥((WW R φ).prod (VV R φ))→ₛₗ[bar] ↥((WW R φ).prod (VV R φ)) where
 toFun x:=⟨((monthPV R Raw.v τ ⟨_,x.property.1⟩).val,(monthPV R vsAct τ ⟨_,x.property.2⟩).val),⟨Subtype.property _,Subtype.property _⟩⟩
 map_add' i j:= Subtype.ext (Prod.ext (funext fun a=>map_add H _ _) (funext fun a=>map_add H _ _))
 map_smul' r i:= Subtype.ext (Prod.ext (funext fun a=> LinearMap.map_smulₛₗ H r _) (funext fun a=>LinearMap.map_smulₛₗ H r _))

lemma afterPV (p:Function.Involutive H): Function.Involutive (yellowPV R τ):=by
 intro x; exact Subtype.ext (Prod.ext (funext fun i=>p (x.val.1 i)) (funext fun i=>p (x.val.2 i)))
include Q
lemma auditFinPV {V : Type*}[Fintype V](B:Labels V): Module.Finite ℂ (R.allowed B δ):=by
 haveI := Q.fin
 let g : ↥(R.allowed B δ) →ₗ[ℂ] V→δ:= LinearMap.pi fun i=>
   (LinearMap.proj i ∘ₗ (R.allowed B δ).subtype).codRestrict δ (fun v=>v.property.2 i (Set.mem_univ _))
 exact Module.Finite.of_injective g (fun x y h=>Subtype.ext (funext fun i=>congr_arg Subtype.val (congr_fun h i))) -- check

structure ReckonPV (Q:Grade R H δ)(τ:Grade R H φ)(a b c d e:ℕ): Prop where
 storeT: finrank ℝ ↥(RayPV (monthPV R symAct Q))=a
 flow: finrank ℝ ↥(LinearMap.range (RadialPV (monthPV R symAct Q) (R.divP ∘ₗ (TT R δ).subtype)))=b
 storeW: finrank ℝ ↥(RayPV (monthPV R Raw.v τ))=c
 storeV: finrank ℝ ↥(RayPV (monthPV R vsAct τ))=d
 check_: finrank ℝ ↥(LinearMap.range (RadialPV (yellowPV R τ) (div_check R φ)))=e

lemma chalkPV (p:Function.Involutive H)(g:∀ k x, H (R.P k x)= R.P k (H x)) (a b c d e)
   (ha : finrank ℂ ↥(TT R δ)=a) (hb : finrank ℂ ↥((TT R δ).map R.divP)=b) (hc : finrank ℂ ↥(WW R φ)=c)
   (hd : finrank ℂ ↥(VV R φ)=d) (he: finrank ℂ ↥(((WW R φ).prod (VV R φ)).map (codiff R))=e): ReckonPV R Q τ a b c d e:=by
 letI : Module.Finite ℂ ↥(R.allowed symAct δ):= auditFinPV R Q _
 letI : Module.Finite ℂ ↥(R.allowed Raw.v φ):= auditFinPV R τ _
 letI : Module.Finite ℂ ↥(R.allowed vsAct φ):= auditFinPV R τ _
 letI : Module.Finite ℂ ↥(WW R φ):= inferInstanceAs (Module.Finite ℂ ↥(R.allowed Raw.v φ))
 letI : Module.Finite ℂ ↥(VV R φ):= inferInstanceAs (Module.Finite ℂ ↥(R.allowed vsAct φ))
 haveI : Module.Finite ℂ ↥((WW R φ).prod (VV R φ)):= Module.Finite.equiv (gear R φ).symm
 constructor
 · rw [peakPV _ (datePV _ Q _ p)]; exact ha
 · rw [trailRankPV _ (datePV _ Q _ p),LinearMap.range_comp]
   · change finrank ℂ ↥(Submodule.map R.divP (LinearMap.range ((TT R δ).subtype)))=b
     rw [Submodule.range_subtype]; exact hb
   intro x hx; rw [LinearMap.mem_ker]; ext1 i
   have h: R.divP x.val i=0:=congr_fun (show R.divP x.val=0 from hx) i
   change R.divP _ i=0
   rw [← H.map_zero,← h,divT,divT,map_sum]; exact Finset.sum_congr rfl fun j _=>(g ..).symm
 · rw [peakPV _ (datePV _ τ _ p)]; exact hc
 · rw [peakPV _ (datePV _ τ _ p)]; exact hd
 rw [trailRankPV _ (afterPV R τ p)]
 · unfold div_check; rw [LinearMap.range_comp,Submodule.range_subtype]; exact he
 intro x hx; rw [LinearMap.mem_ker]; ext1 ⟨i,j⟩
 have h: codiff R x.val (i,j)=0:= congr_fun (show codiff R x.val=0 from hx) _
 change codiff R _ (i,j)=0; rw [← H.map_zero,← h]
 change R.divA _ (i,j)-R.P i _=H (R.divA _ (i,j)-R.P i _)
 rw [map_sub,g,divV,divV,map_sum]; congr 1
 exact Finset.sum_congr rfl fun k _=> (g ..).symm
#print axioms chalkPV
omit Q
set_option maxHeartbeats 250000
lemma θG_countPV: ReckonPV recG (Calibration.gauge Floor.four) (Calibration.gauge Floor.five) 3 2 2 20 19:= chalkPV recG (Calibration.gauge Floor.four) (Calibration.gauge Floor.five) g2 G_tr _ _ _ _ _
 g_ranks.1 g_ranks.2.1 g_ranks.2.2.1 g_ranks.2.2.2.1 g_ranks.2.2.2.2.1
lemma θF_countPV: ReckonPV ph (Calibration.matter Floor.four) (Calibration.matter Floor.five) 2 1 1 14 13:= chalkPV ph (Calibration.matter Floor.four) (Calibration.matter Floor.five) f2 f_tr _ _ _ _ _
 f_ranks.1 f_ranks.2.1 f_ranks.2.2.1 f_ranks.2.2.2.1 f_ranks.2.2.2.2.1
lemma θX_countPV: ReckonPV recX (Calibration.mixed Floor.four) (Calibration.mixed Floor.five) 0 0 1 6 7:= chalkPV recX (Calibration.mixed Floor.four) (Calibration.mixed Floor.five) x2 x_tr _ _ _ _ _
 x_ranks.1 x_ranks.2.1 x_ranks.2.2.1 x_ranks.2.2.2.1 x_ranks.2.2.2.2
#print axioms θF_countPV
#print axioms θG_countPV
#print axioms θX_countPV
end YM.GaugeFieldConstruction.Sunpath
