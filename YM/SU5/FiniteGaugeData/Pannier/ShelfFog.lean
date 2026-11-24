import YM.SU5.FiniteGaugeData.Pannier.Hollow
/-!
# Many identity-subtractions. Keep factor costs before seeking any path-tail threshold.
This is an operator inequality, not using any of the gauge-calibration estimates
(and doesn't hold without the phase/orthogonality/Wick data stated). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Fixed Skye Pastry
open Damask
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n ι : Type*}[LinearOrder n][Fintype n]
-- permits epsilon-power estimates independent of k. Note the same orientation in D. for pricing.
def together (x y : FC n) := (1:FC n)+x*y
def mute (M:Wave n) (x:FC n) : Prop := acts (star x) M=0
structure Folder (X Y Y' A A':ι→FC n) (b:Bool)(r E:ℝ) (M W:Wave n)(G:FC n) : Prop where
 -- λ-correction
 pitch : ∀ i,Marque b (A i)
 switched : ∀ i, Marque b (A' i)
 change : ∀ i, ‖A' i-A i‖≤E
 price : ∀ i, ‖A i‖ ≤ r
 standing : ∀ i, acts (A i) W=0
 spare :∀ i, mute M (A i-Y i)
 apart :∀ i j,i≠j→ antiB (A i) (X j)= 0
 occupy:∀ i, antiB (A i) (X i)= 1
 joint: ∀ i j, antiB (Y i) (X j)=0
 fly: ∀ i, Marque b (Y i)
 roar: ∀ i, Letter (Y' i-Y i)
 frost: ∀ i, ‖Y' i-Y i‖ ≤ E^3
 near: ∀ i, Letter (X i)
 lifetime:∀ i, ‖X i‖ ≤ 1
 mail: ∀ i j, Commute (X i*(Y' i-Y i)) (together (X j) (Y' j))
 parcel: ∀ i, Commute (X i*(Y' i-Y i)) G
 box: ∀ i,Commute G (A' i)

namespace Folder
variable {X Y Y' A A':ι→FC n}{b:Bool}{r E:ℝ}{M W:Wave n}{G:FC n}
    (p:Folder X Y Y' A A' b r E M W G)
local notation "ℓ" => fun i:ι=> together (X i) (Y i)
local notation "℮" => fun i:ι=> X i*(Y' i-Y i)
local notation "ℸ" => fun i:ι=> together (X i) (Y' i)
include p
private lemma chord_sub (i j:ι)(v:i≠j): (ℓ) j * (A i-Y i)=(A i-Y i)*(ℓ) j:=by
 let Q:= A i - Y i; have he:(X j)*Q = -(Q*X j):=by
    apply eq_neg_of_add_eq_zero_left; let h:=p.apart i j v; let z:=p.joint i j
    unfold antiB at h z; unfold Q; rw [mul_sub,sub_mul]; rw [eq_neg_of_add_eq_zero_left z,show A i*X j= _ from eq_neg_of_add_eq_zero_left h]; abel
 have hp:= same_letter (p.fly j) (can_care (p.pitch i) (p.fly i)); unfold together; change (1+ _)*Q=Q*(1+_); rw [add_mul,mul_add,one_mul,mul_one, mul_assoc]; change Q+X j*(Y j*(A i - Y i))=_; rw [hp]; change Q+X j*(-(Q*Y j))=_; rw [mul_neg,←mul_assoc,he,neg_mul,neg_neg,mul_assoc]

-- Evaluate left against grade reference. Don't price alternating error Here.
lemma still (L:List ι)(h:L.Nodup) (U:Wave n):
    inner ℂ M (acts (fo (ℓ) L) U) = inner ℂ M (acts (fo (fun i=> X i*A i) L) U):=by
 induction L using List.reverseRecOn generalizing U with
 | nil=> rfl
 | append_singleton l i ih=>
    rw [List.nodup_append] at h; simp only [fo,List.map_append, List.map_singleton,List.prod_append, List.prod_singleton,act_mul]; let F:= fo (ℓ) l; let K:= A i - Y i
    have hx:X i * A i= (ℓ) i-K*(X i):=by unfold K together; rw [sub_mul]; have ht:= p.occupy i; have hh:=p.joint i i; unfold antiB at *; rw [eq_sub_of_add_eq ht, eq_neg_of_add_eq_zero_left hh]; simp only [sub_neg_eq_add, sub_add_eq_sub_sub, add_sub_cancel_right]; abel_nf; try simp
    have hK: mute M K:=p.spare i
    have hs(l:List ι)(e:∀ j∈l,i ≠ j): Commute K (fo (ℓ) l):=by induction l with|nil=> exact Commute.one_right K|cons i l ih=> exact ((show Commute K ((ℓ) i) from (chord_sub p _ _ (e _ List.mem_cons_self)).symm)).mul_right (ih (fun j u=>e j (List.mem_cons_of_mem i u)))
    have hf : Commute K F:= hs l (fun j q=> (h.2.2 j q i List.mem_cons_self).symm)
    change inner ℂ M (acts F _) = inner ℂ M (acts (fo (fun i=> X i*A i) l) (acts (X i) (acts (A i) U)))
    rw [←ih h.1, ←act_mul (X i),hx,act_sub]; change _=inner ℂ M (acts F _); rw [map_sub,inner_sub_right]; 
    rw [act_mul K,←act_mul F K,hf.symm.eq,act_mul K,← act_inner K,hK,inner_zero_left,sub_zero]

lemma shuffle (L:List ι)(u:L.Nodup): ∃ z:ℂ, ‖z‖=1 ∧ fo (fun i=>X i*A i) L=z • (fo X L * fo A L):=by
 induction L with
 | nil=> exact ⟨1,norm_one,by simp [fo]⟩
 | cons i l ih=>
    rw [List.nodup_cons] at u; obtain ⟨v,z,t⟩:= ih u.2; have ht:= antiCycle (A i) l (fun j w=> (show X j*A i= -_ from eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact p.apart i j (fun x=>u.1 (x.symm ▸ w)))))
    let K:ℂ:= (-1)^l.length; have hp:‖K‖=1:= by simp [K]
    refine ⟨v*K,by simp [norm_mul,z,hp],?_⟩
    have he : fo X l*A i=K • (A i*fo X l):= ht
    change X i*A i* fo (fun i=>X i*A i) l=(v*K) • ((X i*fo X l)*(A i*fo A l)); rw [t]; simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_smul]; congr 1; rw [mul_assoc (X i) (fo X l),←mul_assoc (fo X l),he,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul, show K*K=1 by unfold K; rw [← mul_pow]; simp,one_smul]; simp only [mul_assoc]

variable (hm: ‖M‖≤1)(e:0<E)(c:0<r)(t:E ≤ 1)
local notation "B"=> E*(r+2)
local notation "C"=> E*(r+3)
include hm e t c
lemma glam (L:List ι)(U:Wave n)(k:ℕ)(d:Pause A k U)(h:L.Nodup) : ‖inner ℂ M (acts (fo (ℓ) L*G) U)‖ ≤ (E*(r+2))^L.length*(‖G‖*(‖U‖*E⁻¹^k)) := by
 obtain ⟨x,a,b⟩:= p.shuffle L h
 rw [act_mul,p.still L h,b,act_smul,inner_smul_right,norm_mul,a,one_mul,act_mul]
 let x0:= fo A L; have he (L : List ι):‖fo X L‖≤1:=by
    induction L with
    | nil=> simp [fo]
    | cons i l ih=> -- ih premises? shuffle deps
       rw [fo,List.map_cons,List.prod_cons]; apply (norm_mul_le ..).trans; exact (mul_le_mul (p.lifetime i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
 have hf:= deposit G A' r _ p.pitch p.switched p.change p.box p.price e t d c
 apply (norm_inner_le_norm ..).trans
 apply (mul_le_of_le_one_left (norm_nonneg _) hm).trans
 exact ((Graph.spentS _ _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (he L))).trans (hf L)
omit hm e c t
private lemma void (i:ι): (ℸ) i=(ℓ) i+(℮) i:=by unfold together; simp only [mul_sub]; abel
include hm e c t
private lemma tender (l k:List ι) (ψ:Wave n) (K:ℕ) (h:Pause A K ψ) (g:(k++l).Nodup):
    ‖inner ℂ M (acts (fo (ℓ) k * fo (ℸ) l * G) ψ)‖ ≤ B^k.length*C^l.length * (‖G‖ * (‖ψ‖ * E⁻¹^K)) := by
 let q:=(B); let r':=(C); have hp:0<q:=by unfold q; positivity
 have hR:0<r':=by unfold r'; positivity
 change _≤ q^_*r'^_*_
 induction l generalizing k K ψ with
 | nil=> simp only [fo,List.map_nil,List.prod_nil,mul_one,List.length_nil,pow_zero] at *; exact p.glam hm e c t _ ψ _ h (by simpa using g) -- tune order
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
    · unfold A'; rw [p.void i]; change a * ((_+H)*_) *_= _; rw [show F= _ from (show F=a* (ℓ) i from hI i)]; rw [add_mul, mul_add, add_mul]; simp only [mul_assoc]; rw [h'.eq]; simp only [mul_assoc]
    apply (norm_add_le ..).trans; rw [act_mul (a*ℓ'*G)];
    have hf := ih (k++[i]) ψ K h (by simpa using g) -- local ih closure incl l fixed
    apply (add_le_add hf ((ih k v _ hv hn).trans _)).trans_eq (show q^(k++[i]).length*r'^l.length*D+(q^k.length*r'^l.length*D* E)=q^k.length*r'^(i::l).length*D from ?_)
    swap
    · rw [List.length_cons,List.length_append,List.length_singleton,pow_succ,pow_succ]
      have Ht:r'=q+E:=by unfold q r'; ring
      rw [Ht]; ring
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_trans (Graph.spentS n H ψ) (mul_le_mul_of_nonneg_right ha (norm_nonneg _))) (by positivity)) (norm_nonneg G)) (by positivity)).trans_eq ?_
    unfold D; rw [pow_add E⁻¹]; field_simp <;> ring

/-- use all the selected exact-approximate subtractions at the copy moment.
`G` any other Mark debris (as long as the stated commutations hold),
on the **same torus, same base sea**. Pointwise. -/
lemma earn (g:‖W‖=1)(L:List ι)(d:L.Nodup): Yep E⁻¹ (acts (star (fo (ℸ) L*G)) M) W ((E*(r+3))^L.length *‖G‖) := by
 intro l
 rw [act_inner]
 have he:= tender p hm e c t L [] (acts (fo Damask.use l) W) (0+l.length) (pause_token A (fun i=> ⟨_,p.pitch i⟩) (startPause A p.standing) l) (by simpa using d)
 simp only [fo,List.map_nil,List.prod_nil,one_mul,List.length_nil,pow_zero,zero_add] at he
 let U:= acts (fo Damask.use l) W; change _ ≤ _ * E⁻¹^l.length
 apply he.trans; have hu:‖U‖≤1:=token_limit l g
 change C^L.length*(‖G‖*(‖U‖*E⁻¹^l.length))≤_
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (by positivity)) (norm_nonneg G)) (by positivity)).trans_eq; ring
end Folder
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Folder.earn
