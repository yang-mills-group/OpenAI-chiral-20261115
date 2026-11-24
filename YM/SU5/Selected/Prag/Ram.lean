import YM.SU5.Selected.Prag.Pr
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
local notation "Y"=> prism P
local notation "V"=> Frog P dp S q
local notation "R"=> P.stackS (look j)
open MeshClock
local notation "U" v:max => (P.crew v).play
-- abstract manipulation of stacks of phases inside projected complement
lemma stack_ort : P.stackS (X)= (P.aviator X).starProjection:= by
 ext1 x; let Q:= P.aviator X; let S:= R; have hx: S x∈ Q:= Alliance.planted P X x; symm; apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hx; intro y k
 rw [inner_sub_left,← ContinuousLinearMap.adjoint_inner_right S x, symmetricstack P, grounded P X k, sub_self] -- orientation adjoint_inner_right f x y : ⟪x,f† y⟫ = ⟪fx,y⟫?
lemma toriel (x y:A): inner ℂ ((Y) x) ((Y) y)=inner ℂ x (R y):=by
 change inner ℂ ((P.stackS X) x) ((P.stackS X) y) = _; rw [← ContinuousLinearMap.adjoint_inner_right R, symmetricstack, P.grounded X (P.planted X y)] -- unspecified inner spaces
-- full ABO Zodiac operator. Need x in OS.Cross. function Θ all coords. Use extension zeros; `open ..` Pi
noncomputable def pours (j:Axis)(p:Trans j→ℝ) : OS.Cross j:= ⟨(show E4 from WithLp.toLp 2 (fun i=> if e:i≠j then p ⟨i,e⟩ else 0)),(by change (if e:j≠j then p ⟨j,e⟩ else 0)=0; rw [dif_neg]; simp)⟩ -- E4 uses WithLp? check
local notation "ϱ" v:max=> P.flight dp (look j) v
local notation "p₀"=> pours j
lemma splur (z:Trans j→ℝ): (fun a:Trans j=> (pours j z).val a.val)=z:= funext fun a=> dif_pos a.property
lemma sourceU (z:Trans j→ℝ)(x:A): ((V).U (p₀ z) (Y x):P.aviator X).val=(ϱ z) x:=by
    change (ϱ (fun i=>(pours j z).val i.val)) (R x)=_; rw [splur,P.over]
local notation "Φ" v:max=> P.raw X v
local notation "Y₁" v:max=>P.aviation dp X v
lemma ray (z:Trans j→Γ)(x:A): ((V).U (p₀ (fun a=>(z a:ℝ))) (Y x):P.aviator X).val=(Φ z) (R x):=(sourceU P dp S q _ _).trans (congrArg (fun F:A.Op=>F x) (P.smooth_notch dp X z))
lemma torque (z:Trans j→Γ)(x y:A): inner ℂ (Y x) ((V).U (p₀ fun a=>(z a:ℝ)) (Y y))=inner ℂ x ((Φ z) (R y)):=by
 have he:Commute (R) (Φ z):=P.ground X _ (fun i _ c=>(P.hard X _ (fun b d a=>P.cCom ..) z).symm)|>.symm -- has ground T.comp stack=stack.comp T. RHS property moves.
 have hp:Y ((Φ z) y)=(V).U (p₀ fun a=>(z a:ℝ)) (Y y):= Subtype.ext ((DFunLike.congr_fun he y).trans (ray P dp S q z y).symm); rw [←hp, toriel]; exact congrArg (inner ℂ x) (DFunLike.congr_fun he y) -- note Syntax notations
variable {Q:Set ℝ≥0}(hq:Dense Q) {d:Trans j→ Γ→Prop} (w:Trans j→A→A→Prop) -- reach
private lemma bandOn(x:A)(i:Trans j)(z:List (Trans j×Γ))(p:∀k∈z,k.1≠i)(v:∀ w':Trans j,w'≠i→∀ c:Γ, ∀ y:A,w i x y→ w i x ((U w') c y))(y:A)(q:w i x y) :w i x (P.band z y):=by
 induction z with| nil=> exact q
                 | cons k z h=> exact v k.1 (p _ List.mem_cons_self) k.2 _ (h fun k v=> p k (List.Mem.tail _ v))
lemma flight_band (z:List (Trans j × Γ)) (C:A.Op)(p:∀ k∈ z,Commute ((U k.1) k.2) C): Commute (P.band z) C:= by induction z with
 | nil => exact Commute.one_left C
 | cons k s h=> exact (p _ List.mem_cons_self).mul_left (h (fun k v=>p k (List.Mem.tail _ v))) -- orientation
private lemma public_f (z:Trans j → Γ) (x y:A)(p:∀i,w i x y)(Y':∀ i k,k≠i→∀ c:Γ, ∀ y:A,w i x y→ w i x ((U k) c y))(q:∀ i y,w i x y→ ContinuousAt (fun k:Γ=>inner ℂ x ((U i) k y)) (z i)) : P.public_test y z X (innerSL ℂ x):=by
 refine P.covered X y z (innerSL ℂ x) (fun i _ k v=> ?_) (look_one j); let K:=P.band k; have ht:∀ c:Γ, K ((U i) c y)=(U i) c (K y):= fun c=> DFunLike.congr_fun (P.flight_band k ((U i) c) (fun t _=> P.cCom t.1 i _ c)) y
 change ContinuousAt (fun c:Γ=> inner ℂ x (K ((U i) c y))) _; simp_rw [ht]; exact q i (K y) (bandOn P w x i k v (Y' i) y (p i))
include hq
open Set
lemma fortunes (z:Trans j→Γ)(x y:A)(p:∀ i,w i x y)(X':∀ i, ∀ t∈ Q,∀ y:A,w i x y→w i x (S.E t y))(Y':∀ i k,k≠i→∀ c:Γ, ∀ y:A,w i x y→ w i x ((U k) c y))(K:∀ i y,w i x y→ ContinuousAt (fun k:Γ=>inner ℂ x ((U i) k y)) (z i))(t:ℝ≥0): inner ℂ (Y x) ((V).U (p₀ fun a=>(z a:ℝ)) ((V).E t (Y y))) =inner ℂ x ((Φ z) (S.E t y)) :=by
 let V':=V; let U':= V'.U (p₀ fun a=>(z a:ℝ)); refine congrFun (hq.denseRange_val.equalizer (continuous_const.inner (U'.continuous.comp (V'.continuousE (Y y)))) (continuous_const.inner ((Φ z).continuous.comp (S.continuousE y))) ?_) t; funext i; let Z':= S.E i.val y; have hr:P.public_test Z' z (look j) (innerSL ℂ x):= P.public_f w z x Z' (fun a=> X' a _ i.property _ (p a)) Y' K
 change inner ℂ (Y x) ((V).U _ ((V).E _ (Y y)))=_; rw [←prism_early]; exact (torque P dp S q z x Z').trans (P.faith X Z' z (innerSL ℂ x) hr)
end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
#print axioms stack_ort
#print axioms public_f -- private
#print axioms fortunes
#check @fortunes
