import YM.SU5.Selected.Rail.Soli
/-! # Reserves & request. These Hall stubs not yet include sectors. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset Lat
variable {n k t:ℕ}{q h:Type*}[Fintype q][DecidableEq q][Fintype h][DecidableEq h]
def Rates (W:FaceL)(A:WRect (Fin n) q)(Z:q→basisRule)(k t:ℕ):Prop:=∀ i j,(↑rent':ℂ)*A i j=∑ u∈(Z j).support,Z j u*keystone k W (t+u+i.val)
lemma requests(W:FaceL)(A:WRect (Fin n) q)(p:k≥3)(t:ℕ):∃ Z:q→basisRule,Rates W A Z k t:=by
 choose Y h using fun j:q=>tenor W t p (fun i:Fin n=> (↑rent':ℂ)*A i j); exact ⟨Y,fun i j=> h j i⟩
variable (W:FaceL)(Z:q→basisRule)
def balanceA (t n k:ℕ)(M:Maj)(N:Side): WRect (Fin n) q:= Matrix.of fun i j=> packA N (fun x:Site N=> ((Spouse W n t (brim N x))ᴴ*Deep M k Z (pm x)) i j)
#print balanceA
lemma status {A:WRect (Fin n) q}(p:k≥3)(g:Rates W A Z k t) : Tendsto (fun i:Maj×Side=> balanceA W Z t n k i.1 i.2) mounts (𝓝 A):=by
 let F(p:Maj×Side):=balanceA W Z t n k p.1 p.2; suffices h:∀ i:Fin n,∀ j:q,Tendsto (fun u=> F u i j) mounts (𝓝 (A i j)) by apply tendsto_pi_nhds.mpr; intro i; exact tendsto_pi_nhds.mpr (h i)
 intro i j; let X(u:ℕ)(h:Maj×Side):=packA h.2 (hood k h.1 (Ε W ((↑(t+u+i.val:ℕ)):ℤ)) ∘ pm); let v:= (↑rent':ℂ); let Y(u:ℕ):= v⁻¹ * keystone k W (t+u+i.val); have h(u):Tendsto (X u) mounts (𝓝 (Y u)):= limit_song W _ p; let a:=Z j;
 have hF: (fun x=> F x i j)= fun x=> ∑ u∈a.support,a u*X u x:=funext fun x=> feasible_cost x.1 k Z W t n x.2 i j
 let P₀:= tendsto_finsetSum a.support (fun u (_:u∈a.support)=>(h u).const_mul (a u)); rw [hF,show A i j=∑ u∈a.support,a u*Y u from ?_]; exact P₀;
 have hp:=g i j; rw [show (∑ u∈_,a u*Y u)= v⁻¹*(∑ u∈a.support,a u*keystone k W (t+u+i.val)) from (by rw [mul_sum]; exact sum_congr rfl fun u _=>by unfold Y; ring), ← show v*A i j=_ from hp, inv_mul_cancel_left₀]; unfold v; exact_mod_cast rent_pos.ne'
-- sampled buffers, masks. no large matrix defEq fights. 
variable (N:Side)(u:Site N)
abbrev SpinN (N:Side):=Site N×SpinIdx
def presentP (u:Site N)(F:Site N→ WRect SpinIdx q): WRect (SpinN N) q:= freeze F *mask (fun i:q=>(u,i)) -- binder N? N explicit (declare property careful)
lemma profile (F:Site N→ WRect SpinIdx q)(x:SpinN N)(i:q): presentP N u F x i=freeze F x (u,i):=mask_mem ..
lemma presence(F:Site N→ Op SpinIdx)(G:Site N→ WRect SpinIdx q): freeze F * presentP N u G = presentP N u (fun x=> F x * G x):=by unfold presentP; rw [←Matrix.mul_assoc,freeze_mul]
lemma presentSub (f g: Site N→ WRect SpinIdx q): presentP N u (f-g)= presentP N u f-presentP N u g:=by unfold presentP; rw [freeze_sub, Matrix.sub_mul]
lemma pay {F:Site N→ WRect SpinIdx q}{C:ℝ}(v:0≤C)(h:∀ x:Site N, ‖F x‖≤C): ‖presentP N u F‖≤ C:= ((Matrix.l2_opNorm_mul ..).trans (mul_le_of_le_one_right (norm_nonneg _) (mask_toll (fun i:q=>(u,i)) (fun _ _ h=> (Prod.mk.inj h).2)))).trans (freeze_norm v h)
def clerks (u:Site N)(n t:ℕ):= presentP N u (Spouse W n t ∘ brim N)
def chamberU(u:Site N)(M:Maj)(k:ℕ):= presentP N u (Deep M k Z ∘ pm)
def exactU (u:Site N)(k:ℕ):= presentP N u (ShiftY k Z ∘ brim N)
lemma gram_p (M:Maj): (clerks W N u n t)ᴴ* chamberU Z N u M k= balanceA W Z t n k M N:=by
 let F:= Spouse W n t ∘ brim N; let G:= Deep M k Z ∘ (@pm N); let d:= mask (fun i:Fin n=>(u,i)); let d':=mask (fun i:q=>(u,i)) -- name `d'` parser
 unfold clerks chamberU presentP; change (freeze F*d)ᴴ* (freeze G*d')= _; rw [Matrix.conjTranspose_mul,freeze_star, Matrix.mul_assoc,←Matrix.mul_assoc (freeze _),freeze_mul,← Matrix.mul_assoc]; ext i j; rw [mask_mem,mask_star_mem,freeze_charge,balanceA,Matrix.of_apply,packA,mul_sum]; exact sum_congr rfl fun y _=> (trust N u y _).symm
local notation "P0"=> freeze (fun _:Site N=> Aop)
lemma clover : (1-P0)* clerks W N u n t= clerks W N u n t:=by
 rw [show (1-P0)=freeze (fun _:Site N=>(1-Aop)) from (freeze_one (N:=N) (n:=SpinIdx)) ▸ (freeze_sub (fun _=>(1:Op SpinIdx)) (fun _=> Aop)).symm]; unfold clerks; rw [presence]; congr 1; exact funext fun x=> stitch_x W t n _ -- tune
lemma hidden(M:Maj): P0*chamberU Z N u M k= exactU Z N u k:=by unfold chamberU exactU; rw [presence]; congr 1; exact funext fun x=> conceal M k Z (pm x)
lemma adheres (M:Maj): tip N M* chamberU Z N u M k= chamberU Z N u M k:=by unfold tip chamberU; rw [presence]; congr 1; exact funext fun x=> projection M k Z _ (stem_one x) (fun q=> Rush.mel_away x (by unfold Rush.mel; rw [q]; rfl))
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms clover
#print axioms hidden
#print axioms status
#print axioms adheres
#print axioms gram_p
#print axioms pay
