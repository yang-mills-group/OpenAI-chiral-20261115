import YM.SU5.Reconstruction.Oblique.Dynamo
/-! # REAL time evolution & observer translation unit. Associated to this true field $Spi.p operation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (B:BoostBacking Y H V G C a χ) {s: Signed}(A:Pave Y H V G C a χ s) {j z:Axis} (t:Oriented s j z)
local notation "L" => motor Y H V G C a χ B A t
local notation "Z" => (L).conjStarAlgEquiv
section
open OS.Semigroup
private lemma under_heat {X T:Hilbert}{r b:Axis}(U:OS.Semigroup X r)(QX:OS.Semigroup T b)(F:X≃ₗᵢ[ℂ]T)
    (p: ∀ (k:ℝ≥0)(x:X), F (U.E k x)= QX.E k (F x)) (t:ℝ) (x:X): F (U.edge t x)=QX.edge t (F x):=by
    have hp{X:Hilbert} {r:Axis} (Q:OS.Semigroup X r) (f:X) : AnalyticOnNhd ℂ (fun v=> Q.F v f) inside := fun a' h=> ((ContinuousLinearMap.apply ℂ X.space f).analyticAt _).comp (Q.localHeat a' h)
    have h(y:X)(z:ℂ)(q:z∈inside): F (U.F z y)=QX.F z (F y):=by
       refine ConePrice.Sail.pioneer («A»:=OS.Semigroup.inside) (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (w:=1) (show ((↑(1:ℝ)):ℂ)∈ inside from (by change 0< (Complex.ofReal (1:ℝ)).re; simp)) 0 2 (by norm_num) (M₁:=fun z=> F (U.F z y)) (fun a' h=> (F.toLinearIsometry.toContinuousLinearMap.analyticAt _).comp (hp _ _ a' h)) (hp QX (F y)) ?_ q
       intro u v; change F (U.F (u:ℂ) y)=QX.F (u:ℂ) (F y)
       rw [show (u:ℂ)=duration (Real.toNNReal u) from (by unfold duration; rw [Real.coe_toNNReal u v.1.le]), QX.roots_heat (Real.toNNReal_pos.mpr v.1),U.roots_heat (Real.toNNReal_pos.mpr v.1),p]
    apply congrFun (a:=x) ((U.whole 1).equalizer (F.continuous.comp (U.edge t).continuous) ((QX.edge t).continuous.comp F.continuous) _)
    funext u; dsimp only [Function.comp_apply]; rw [p,OS.Semigroup.high,OS.Semigroup.high,h _ _ (length.mpr zero_lt_one)]
end
include B A t
lemma allot (u:ℝ≥0)(x: Fs j) : L ((S₀ j).E u x)= (S₀ z).E u (L x):= by
 have hh : (fun v:ℝ≥0=> L ((S₀ j).E v x))=fun v=> (S₀ z).E v (L x):=by
    apply (fills (timeMesh Λ)).denseRange_val.equalizer ((L).continuous.comp ((S₀ j).continuousE _)) ((S₀ z).continuousE _); funext v; obtain ⟨n,b,e⟩:=MeshClock.split _ v.property; let p:=notch (timeMesh Λ) n b
    have ht : (p:ℝ)=(v.val:ℝ) := (natural_time _ n b).trans (congrArg (fun x:ℝ≥0=>(x:ℝ)) e)
    have Q:0 ≤ (p:ℝ):= ht.symm ▸ v.val.property; have H':=turn_appointment Y H V G C a χ B A t (eject j p) (show 0 ≤ (eject j p j).val from by simpa using Q); rw [t.axis_eject p, bridge_time,bridge_time, ht,Real.toNNReal_coe] at H'; dsimp only [Function.comp_apply]
    rw [←H',LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]
 exact congrFun hh u
lemma allotted_time(u:ℝ) : Z ((℘ j) (u • basis j)) = (℘ z) (sailPoint s (u • basis j)):=by
 rw [t.stroll,Picket.trans_time,Picket.trans_time]; ext1 x; obtain ⟨x,rfl⟩:= (L).surjective x; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact under_heat (S₀ j) (S₀ z) _ (allot Y H V G C a χ B A t) _ _
lemma allotted_space(d:Axis)(p:d≠j)(u:ℝ): Z ((℘ j) (u • basis d)) = (℘ z) (sailPoint s (u • basis d)):=by
 let f:= s.perm d; have q:f≠z:=by unfold f; rw [← t.peer]; exact s.perm.injective.ne p
 ext1 x; obtain ⟨x,rfl⟩:= (L).surjective x; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,sail_axes]
 have hv:Continuous (hush (s.flip d) («α»:=ℝ)):=by
    cases s.flip d; · exact continuous_id
    exact continuous_neg
 apply congrFun (a:=u) ((daylight (timeMesh Λ)).denseRange_val.equalizer ((L).continuous.comp (((S₀ j).unit.moves x).comp (show Continuous fun x:ℝ=> x • basis d by fun_prop))) (((S₀ z).unit.moves (L x)).comp (hv.smul (continuous_const (y:=basis f)))) _)
 funext u; dsimp only [comp_apply]
 have T:= turn_appointment Y H V G C a χ B A t (eject d (u:↥(marks (timeMesh Λ)))) (show 0≤(eject d u j).val from by simp [Ne.symm p]); rw[tilt_eject, castSpace Y H V G C a χ j p, castSpace Y H V G C a χ z q] at T; change L ((℘ j) ((u:ℝ) • basis d) x)=(℘ z) (hush (s.flip d) (u:ℝ) • basis _) (L x)
 have hk :=DFunLike.congr_fun T (L x); rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply] at hk; rw [hk]; -- Real hush eq
 have e: ((hush (s.flip d) u:Gt).val:ℝ)=hush (s.flip d) (u:ℝ):= by cases s.flip d <;> rfl
 rw [e]
lemma allotted (x:E4): Z ((℘ j) x)= (℘ z) (sailPoint s x):=by
 have he (T:Finset Axis) : let u:=∑i∈T,x i • basis i; Z ((℘ j) u)= (℘ z) (sailPoint s u):= by
    induction T using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty,sail_zero]; rw [show (℘ j) 0=1 from (S₀ j).unit.origin,map_one]; exact (show (℘ z) 0=1 from (S₀ z).unit.origin).symm -- intro u
    | insert k l p ih=>
      dsimp only at *; rw [Finset.sum_insert p,sail_add,Picket.trans_sum,Picket.trans_sum,map_mul,ih]; by_cases h:k=j; · subst k; rw [allotted_time Y H V G C a χ B A t]
      rw [allotted_space Y H V G C a χ B A t k h]
 specialize he Finset.univ; dsimp only at he; rwa [show (∑ i:Axis,x i • basis i)=x from (by ext1 i; simp)] at he
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
