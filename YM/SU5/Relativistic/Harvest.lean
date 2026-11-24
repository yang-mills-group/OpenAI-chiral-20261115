import YM.SU5.Relativistic.Sable
/-! # Budget *also in the small error terms at the very point*. Based on Folder.ShelfFog's estimate.
 Preserve rank loss cap through all calls. No anti-trace Hilbert hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Fixed Skye Pastry
open Damask
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n ι : Type*}[LinearOrder n][Fintype n]
namespace Folder
variable {X Y Y' A A':ι→FC n}{b:Bool}{r E:ℝ}{M W:Wave n}{G:FC n}
    (p:Folder X Y Y' A A' b r E M W G)
local notation "ℓ" => fun i:ι=> together (X i) (Y i)
local notation "℮" => fun i:ι=> X i*(Y' i-Y i)
local notation "ℸ" => fun i:ι=> together (X i) (Y' i)
include p
open Papyrus.Granat Thera
private lemma shrew (i:ι): (ℸ) i=(ℓ) i+(℮) i:=by unfold together; simp only [mul_sub]; abel
variable (e:0<E)(c:0<r)(t:E ≤ 1) {P M':Op n}{η:ℝ}{D':ℕ}
    (hm:IsStarProjection P)(w:IsStarProjection M')(hM:Sea M' M)(hη:0<η) (qη:η ≤ 1)(Yt:JumpCost D' G)
local notation "K□" => Real.exp (crater M' P η)
local notation "U□" N => (K□)*(η⁻¹)^N
include e t c hm w hM hη qη Yt
private lemma glance {V: UNI n}{S: Finset n}(Vp:P=twist V (cutM S))(H Z:ℕ) (L:List ι)(U:Wave n)(k:ℕ)(d:Pause A k U)(h:L.Nodup) (f:Lode V S Z U)(u:2*L.length+ D'+ Z≤H):
    ‖inner ℂ M (acts (fo (ℓ) L*G) U)‖ ≤ (U□ H)*((E*(r+2))^L.length*(‖G‖*(‖U‖*E⁻¹^k))) := by
 obtain ⟨x,a,b1⟩:= p.shuffle L h
 rw [act_mul,p.still L h,b1,act_smul,inner_smul_right,norm_mul,a,one_mul,act_mul]
 let x0:= fo A L; have he (L : List ι):‖fo X L‖≤1:=by
    induction L with
    | nil=> simp [fo]
    | cons i l ih=> -- ih premises? shuffle deps
       rw [fo,List.map_cons,List.prod_cons]; apply (norm_mul_le ..).trans; exact (mul_le_mul (p.lifetime i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
 have hf:= deposit G A' r _ p.pitch p.switched p.change p.box p.price e t d c
 have hy:= ((JumpCost.roll (fun i=>JumpCost.letter (p.near i)) L).mul (JumpCost.roll (fun i=>JumpCost.letter ⟨b,p.pitch i⟩) L)).mul Yt; -- tune
 let U':=acts (fo X L) (acts (fo A L) (acts G U))
 have hg:Lode V S H U':=by unfold U'; rw [←act_mul (fo X L),←act_mul]; exact (hy V S _ _ f).low (by omega)
 apply (tried Vp hm w hη qη hM hg).trans (mul_le_mul_of_nonneg_left _ (by positivity))
 exact ((Graph.spentS _ _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (he L))).trans (hf L)
local notation "B"=> E*(r+2)
local notation "C"=> E*(r+3)
private lemma tremor {V: UNI n}{S: Finset n}(Vp:P=twist V (cutM S))(J Z:ℕ)(l k:List ι) (ψ:Wave n) (K:ℕ) (h:Pause A K ψ) (g:(k++l).Nodup) (f:Lode V S Z ψ)(u:2*(k++l).length+ D'+ Z≤J):
    ‖inner ℂ M (acts (fo (ℓ) k * fo (ℸ) l * G) ψ)‖ ≤ (U□ J)*(B^k.length*C^l.length * (‖G‖ * (‖ψ‖ * E⁻¹^K))) := by
 let q:=(B); let r':=(C); have hp:0<q:=by unfold q; positivity
 have hR:0<r':=by unfold r'; positivity
 let Z_:= K□* η⁻¹^J
 have hZ:0≤Z_:= by unfold Z_; positivity
 change _≤ Z_*(q^_*r'^_*_)
 simp only [List.length_append] at u
 induction l generalizing k K ψ Z with
 | nil=> simp only [fo,List.map_nil,List.prod_nil,mul_one,List.length_nil,pow_zero] at *; exact p.glance e c t hm w hM hη qη Yt Vp _ _ _ ψ _ h (by simpa using g) f (by simpa using u) -- tune order
 | cons i l ih=>
    have he (j): Letter (A j):= ⟨b,p.pitch j⟩
    let H:= (℮) i; have ha:‖H‖ ≤ E^3:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (p.lifetime i)).trans (p.frost i))
    let a:= fo (ℓ) k; let v:= (acts H ψ); have hv: Pause A (K+2) v:=by unfold v; rw [show H=X i*(Y' i-Y i) from rfl,act_mul]; exact pause_one (p.near i) he (pause_one (p.roar i) he h)
    have hn: (k++l).Nodup:=g.sublist (List.Sublist.append (List.Sublist.refl k) (List.Sublist.cons i (List.Sublist.refl l))) -- ?. .sublist
    let ℓ' := fo (ℸ) l
    have ht(r:List ι):Commute H (fo (ℸ) r):=by induction r with| nil=> exact Commute.one_right H| cons i' L ih=> exact (p.mail i i').mul_right ih
    have h':Commute H (ℓ'*G):= (ht l).mul_right (p.parcel i)
    let F:= fo (ℓ) (k++[i]); let A':= (ℸ) i
    have hI(j:ι) : fo (ℓ) (k++[j])=a*(ℓ) j:=by simp [fo,a]
    change ‖inner ℂ M (acts (a * (A'*ℓ')* G) ψ)‖≤ _
    let D:= ‖G‖*(‖ψ‖* E⁻¹^K)
    rw [show a*(A'*ℓ')*G= F *ℓ'*G+(a*ℓ'*G)*H from ?_,act_add,inner_add_right]; swap
    · unfold A'; rw [p.shrew i]; change a * ((_+H)*_) *_= _; rw [show F= _ from (show F=a* (ℓ) i from hI i)]; rw [add_mul, mul_add, add_mul]; simp only [mul_assoc]; rw [h'.eq]; simp only [mul_assoc]
    apply (norm_add_le ..).trans; rw [act_mul (a*ℓ'*G)];
    have hv': Lode V S (Z+2) v:=by unfold v; rw [show H= _ from (show H=X i*(Y' i-Y i) from rfl),act_mul]; exact (f.next (p.roar i)).next (p.near i)
    simp only [List.length_cons] at u
    have hf := ih Z (k++[i]) ψ K h (by simpa using g) f (by simp; omega) -- order
    apply (add_le_add hf ((ih (Z+2) k v _ hv hn hv' (by omega)).trans (mul_le_mul_of_nonneg_left _ hZ))).trans_eq (show Z_*(q^(k++[i]).length*r'^l.length*D) + Z_*(q^k.length*r'^l.length*D* E)= Z_*(q^k.length*r'^(i::l).length*D) from ?_)
    swap
    · rw [List.length_cons,List.length_append,List.length_singleton,pow_succ,pow_succ]
      have Ht:r'=q+E:=by unfold q r'; ring
      rw [Ht]; ring
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_trans (Graph.spentS n H ψ) (mul_le_mul_of_nonneg_right ha (norm_nonneg _))) (by positivity)) (norm_nonneg G)) (by positivity)).trans_eq ?_
    unfold D; rw [pow_add E⁻¹]; field_simp <;> ring

lemma harvest (h':Sea P W)(L:List ι)(d:L.Nodup): Yep (η⁻¹*E⁻¹) (acts (star (fo (ℸ) L*G)) M) W (((U□ (2*L.length+D'))* (E*(r+3))^L.length) *‖G‖) := by
 intro l
 obtain ⟨V,S,g⟩:=spot_projection P hm
 rw [act_inner]
 let U_:= acts (fo Damask.use l) W
 have hw(i:Token n):JumpCost 1 (Damask.use i):=JumpCost.letter (A:=Damask.use i) ⟨i.val.1,i.val.2,rfl⟩; have hp:JumpCost l.length (fo Damask.use l):=by simpa only [one_mul] using JumpCost.roll hw l
 have hf:=hp V S 0 W (Lode.origin (g ▸ h')); rw [Nat.add_zero] at hf
 have he:= tremor p e c t hm w hM hη qη Yt g (2*L.length+D'+l.length) l.length L [] U_ (0+l.length) (pause_token A (fun i=> ⟨_,p.pitch i⟩) (startPause A p.standing) l) (by simpa using d) hf (by simp only [List.nil_append]; rfl) -- tune
 simp only [fo,List.map_nil,List.prod_nil,one_mul,List.length_nil,pow_zero,zero_add] at he
 change _ ≤ _ * (η⁻¹*E⁻¹)^l.length
 apply he.trans; have hu:‖U_‖≤1:=token_limit l h'.2
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (by positivity)) (norm_nonneg G)) (by positivity)) (by positivity)).trans_eq
 rw [pow_add η⁻¹, mul_pow η⁻¹]; ring
end Folder
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Folder.harvest
