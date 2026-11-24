import WakeRoad.HallAct
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open YM.OS YM.OS.Semigroup SatinRegistration YM.Velour YM.SatinMacro
variable (P:Spine)(x:P.Spectrum0 3)
local notation "jₓ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x jₓ
local notation "G"=> P.ManyF jₓ ξ
local notation "ℰ"=> P.seasons jₓ ξ
local notation "Ω"=> P.heaven jₓ ξ
local notation "W"=>carry P x
local notation "T"=>(ℰ).E
local notation "q*"=> foldSpace
open EmberWind
local notation "K"=> P.calibration
local notation "b"=> ruler P.par.block
-- translation of finite decks by macro-ticks.
lemma seat_hop (l:List Axis)(d:Cover)(A:Finset Cover) (h:l.Nodup) {x:Cover}(p:x∈P.placeSet A l d):∃ y∈A,∀ i:Axis,x i=if i∈l then y i+b*d i else y i:=by
    induction l generalizing x with
    | nil=> exact ⟨x,p,by simp⟩
    | cons k l ih=>
       obtain ⟨v,e⟩:= List.nodup_cons.mp h; obtain ⟨a,g,rfl⟩:= SlabMark.plow_stays K k (d k) (P.placeSet A l d) p; obtain ⟨y,t,h⟩:=ih e g
       refine ⟨y,t,fun i=>?_⟩; rw [SlabMark.moves,h i]; by_cases z:i=k
       · subst i; simp [v];exact Or.inl rfl -- b defeq K
       simp [z]
lemma unseat (l:List Axis)(d:Cover)(F:P.Test): P.cruise l d (P.cruise l (-d) F)=F:=by
    induction l with
    | nil=>rfl
    | cons i l ih=>
       rw [P.cruise_step,P.cruise_step, AlgHom.comp_apply,AlgHom.comp_apply,P.cruise_mesh,P.shifts_sum,Pi.neg_apply,add_neg_cancel,P.shifts_zero]; exact ih
-- node positions in gauge units satisfy ≥ruler bounds, all printedHere true
lemma place_here (d:Cover)(A:Finset Cover)(u:Cover)(h:b • d = 2 • u) (e:∀ z∈A, ∀ i:Axis, |z i-nodeC u i|≤ (12:ℤ))(k:Axis):
    let q:ℕ:= P.calibration.ℓ+1
    Between P.calibration k (-(b*(q:ℤ))) (b*(q:ℤ)) (P.placeSet A Vacancy.ordinate (-d)):=by
    intro q z v; obtain ⟨y,t,s⟩:= seat_hop P _ (-d) _ Vacancy.ordinate_one v
    have hv:= congrFun h k; change b*d k=(2:ℤ)*u k at hv
    rw [s k,if_pos (Vacancy.ordinates k),Pi.neg_apply,mul_neg,hv]
    have he:=e y t k; unfold nodeC at he
    have ht: (16:ℤ) ≤ b:=by
       unfold ruler; exact le_mul_of_one_le_right (by norm_num) (show (1:ℤ) ≤ (P.par.block.val:ℕ) from (by exact_mod_cast P.par.block.property))
    have i₀: (12:ℤ)+1+ P.calibration.ℓ ≤ b*(q:ℤ):=by
       apply le_trans _ (mul_le_mul_of_nonneg_right ht (by positivity)); unfold q; push_cast;omega
    change |y k- (2*(u k)+1)| ≤ _ at he; have v:= abs_le.mp he
    constructor <;> omega
abbrev reWidth(P:Spine):=P.calibration.ℓ+1
lemma ruler_two (x:Cover): b • ((2:ℤ) • x)= (2:ℤ) • (b • x):=smul_comm _ _ _
-- packing on appointed y
variable (s:ℕ)(A:Finset Cover)(d t:Cover)(Y:P.Test)
variable (p:Y∈bay P.calibration A true)(e:Y∈enclave P.calibration)(k:ruler P.par.block • d=(2:ℕ) • t) (v: ∀ z∈A, ∀ i:Axis, |z i-nodeC t i|≤ (12:ℤ))
local notation "I"=>Vacancy.ordinate
noncomputable def fitting : P.Apron:=
   ⟨s,fun _=> reWidth P, fun _=>Nat.zero_lt_succ _,P.cruise I (-d) Y,P.placeSet A I (-d),P.place_test A I (-d) p,P.cruise_color I _ e,fun i=>by rw [neg_mul]; exact place_here P d A t k v i⟩
lemma wearing :
    P.issuing s (fitting P s A d t Y p e k v) d=Y:=by
    unfold issuing fitting Apron.full
    have ht: s-s=0:=Nat.sub_self s; simp_rw [ht]; exact unseat P I d Y
lemma native_on (J:P.Ellis 3 x): native P x (fitting P s A d t Y p e k v)=P.singleState jₓ s x Y:=by
   let V:=fitting P s A d t Y p e k v
   exact (singleLocal P x V J s d (show V.s ≤ s from le_rfl)).symm.trans (congrArg (P.singleState jₓ s x) (wearing P s A d t Y p e k v))
lemma rewidth(i:Axis):(fitting P s A d t Y p e k v).realWidth P i = (reWidth P:ℝ)*P.spotMesh s:=by
   unfold Apron.realWidth; change ((↑((reWidth P:ℕ):ℤ):ℝ)*P.spotMesh s)=_; push_cast; rfl
-- seed from native readings with possibly far time price,
-- clock shortened using physical heat admission bought from gap certificate.
variable (B D:P.Apron)(p q:Vantage)(c:ℝ)(h:0<c)(J:P.Ellis 3 x)
include J
lemma skimming (k:∀ i:Axis,B.realWidth P i=c ∧ D.realWidth P i=c)(e:∀ i,p i+2*c<q i)(g:p (0:Axis)+6*c<q 0)
    (n:P.bodyPair x B D p q≠ native P x B*native P x D):∃ u v:Vantage, Cracks P B D u v ∧ crystal P x B D u v≠0:=by
    let r:=q-p; let ℓ:= (r jₓ - (c+c)).toNNReal
    have h₀:r jₓ>c+c:=by change q (3:Axis)-p 3>_; linarith only [e (3:Axis)]
    have h₁: 0<ℓ:= Real.toNNReal_pos.mpr (sub_pos.mpr h₀); have hv:q-p∈ P.forwardPair B D jₓ:=by change B.realWidth P _+ D.realWidth P _ < (q-p) jₓ; rw [(k _).1,(k _).2]; exact h₀
    let f:=songV P x B; let t:=traceV P x D; let A:=carry P x r t
    have he: inner ℂ f (T ℓ A) ≠ 0:=by
       let M:= (T ℓ).comp (W r)
       have hl: M Ω=Ω:=by unfold M; rw [ContinuousLinearMap.comp_apply,P.cart_empty,P.heaven_hot]
       have hp:M.adjoint Ω=Ω:=by unfold M; rw [ContinuousLinearMap.adjoint_comp,(ℰ).sym, ContinuousLinearMap.comp_apply,P.heaven_hot,P.cart_reverses,P.cart_empty]
       change inner ℂ (songV P x B) (M (traceV P x D))≠0
       rw [stars_fee P x B D J hl hp]
       rw [P.bodyPair_fwd x B D jₓ p q J hv,(k _).1,(k _).2] at n
       exact sub_ne_zero.mpr n
    let i:= (r (0:Axis)- 6*c)
    have ht:0 < i:=by change 0< q 0-p (0:Axis)-_; linarith only [g]
    obtain ⟨l,⟨lh,lv⟩,u⟩:= YM.OS.Semigroup.Gingham.paid_move_heat ℰ h₁ he (show (0:ℝ)≤0 from le_rfl) ht
    let L:ℝ:=l; let d:=c+L/2
    let X:= update p jₓ (-d); let Y:=update q jₓ d
    have gi (w:Axis): X w=if w=jₓ then -d else p w:=by by_cases h:w=jₓ<;> simp [X ,h]
    have hi (w:Axis): Y w=if w=jₓ then d else q w:=by by_cases h:w=jₓ<;> simp [Y ,h]
    have pll:(3:Axis)≠0:=by decide
    have u₀:Cracks P B D X Y:=by
       unfold Cracks; rw [gi,hi,(k _).1,(k _).2]; simp only [if_true]; refine ⟨?_,?_,?_,?_⟩
       · unfold d; change (0:ℝ)<L at lh; linarith
       · unfold d; change (0:ℝ)<L at lh; linarith
       · intro w; rw [gi,hi,(k _).1,(k _).2]; split_ifs with v
         · unfold d; change 0<L at lh; linarith
         linarith only [e w]
       rw [gi,hi,(k _).1,(k _).2]; simp only [if_neg pll.symm]; unfold d; change L<q (0:Axis)-p (0:Axis)-_ at lv; linarith
    refine ⟨X,Y,u₀,?_⟩; unfold crystal; rw [frost_payment P x B D u₀.1 u₀.2.1]
    have hx: (Y 3 - X 3-(B.realWidth P 3+D.realWidth P 3)).toNNReal=l:=by
       rw [hi,gi,if_pos rfl,if_pos rfl,(k _).1,(k _).2]; unfold d L
       rw [show (c+↑l/2)-( -(c+↑l/2))-(c+c)=(l:ℝ) from (by ring),Real.toNNReal_coe]
    rw [hx]; let M:=(T l).comp (W r)
    have hl: M Ω=Ω:=by unfold M; rw [ContinuousLinearMap.comp_apply,P.cart_empty,P.heaven_hot]
    have hp:M.adjoint Ω=Ω:=by unfold M; rw [ContinuousLinearMap.adjoint_comp,(ℰ).sym, ContinuousLinearMap.comp_apply,P.heaven_hot,P.cart_reverses,P.cart_empty]
    rw [show W (Y-X)=W r from of_slideP x jₓ _ _ (fun w h=> by simp [Pi.sub_apply,gi,hi,h]; rfl)]; change inner ℂ (glareY x B jₓ) (M (flashY x D jₓ))- _ ≠0
    rw [←stars_fee P x B D J (A:=M) hl hp]; exact u
#print axioms place_here
end Spine.NativeSeam
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
