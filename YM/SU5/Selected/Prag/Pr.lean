import YM.SU5.FiniteGaugeData.Tower.Sight
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxHeartbeats 290000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open Function Filter Metric Topology NormedSpace
open scoped BigOperators Kronecker InnerProductSpace ComplexOrder NNReal ENNReal Classical
variable {Γ:AddSubgroup ℝ} {A:Hilbert}{j:Axis}(P:Alliance (Trans j) Γ A) (dp:Dense (Γ:Set ℝ)) (S: OS.Semigroup A j)(q: ∀ i v t, Commute ((P.crew i).play v) (S.E t))
local notation "u" t:max=> S.E t
local notation "L₀"=> P
local notation "δ"=> dp
local notation "X"=> look j
local notation "T₀"=> (L₀).Realm X

local notation "τ" t:max=> (L₀).lame X (u t) (fun i _ v=> q i v t)
noncomputable def Frog : OS.Semigroup ((P).Realm (look j)) j where
 E t:= (L₀).lame X (u t) (fun i _ v=> q i v t)
 U x:= (L₀).aviation (dp) (look j) (fun a => x.val a.val)
 eZero:=by ext1 x; apply Subtype.ext; rw [Alliance.grating,S.eZero]; rfl
 time t b:=by ext1 x; apply Subtype.ext; change (u (t+b)) (x.val:A)= (u t) ((u b) x.val); rw [S.time]; rfl
 shrinks t:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by rw [one_mul]; have h:=ContinuousLinearMap.le_opNorm (u t) x.val |>.trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks t)); exact h)
 sym t:=by
    change ContinuousLinearMap.adjoint (τ t)=(τ t)
    ext1 x; apply ext_inner_left ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ ((u t) y.val) (x.val:A) =inner ℂ (y.val:A) ((u t) x.val)
    rw [← ContinuousLinearMap.adjoint_inner_right (u t),S.sym]
 uZero:=by
    have hv:(fun (a: Trans j)=> (0:E4) (a:Axis))=0:=by ext1; rfl
    rw [show ((0:OS.Cross j).val)=(0:E4) from rfl,hv,Alliance.aviation_zero]
 space x y:=by
    have he:(fun a:Trans j=>(x+y).val (a:Axis))=(fun a:Trans j=> x.val (a:Axis)) + (fun a:Trans j=> y.val (a:Axis)):=rfl
    rw [he,← Alliance.aviation_group]
 independent t x:=by
    ext1 i; apply Subtype.ext
    change (u t) ((L₀).flight δ X (fun a=>x.val a.val) i.val)=(L₀).flight δ X _ ((u t) i.val)
    rw [←ContinuousLinearMap.comp_apply _ (u t),Alliance.fluid _ _ _ _ (fun i _ v=> q i v t)]; rfl
 unitary t x:=Alliance.aviation_unit ..
 continuousE x:=by
    change Continuous (fun t=> ((τ t) x:(L₀).aviator X))
    exact Continuous.subtype_mk (show Continuous (fun i=> (u i) (x.val:A)) from (S.continuousE x.val)) _
 continuousU x:=Alliance.aviation_cont _ _ _ _ (fun (i:Trans j) _=>show Continuous (fun v:OS.Cross j=>(v.val:E4) i.val) by fun_prop) x
noncomputable def prism (x:A): (T₀):=(⟨((L₀).stackS X) x,(L₀).planted X x⟩ : ↥((L₀).aviator X))
local notation "b₀"=>prism P
local notation "F₀" => Frog P dp S q
lemma prism_early(t:ℝ≥0)(x:A): b₀ ((u t) x)=(F₀).E t (b₀ x):=by
 let Q':= (L₀).stackS X
 apply Subtype.ext
 change Q' ((u t) x)=(u t) (Q' x)
 rw [←ContinuousLinearMap.comp_apply (u t), Alliance.ground _ _ _ (fun i _ v=>q i v t)]; rfl


end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
#print axioms prism_early
#print axioms Frog
