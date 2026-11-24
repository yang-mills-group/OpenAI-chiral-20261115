import ForceSatin.HighFood
import Rods.Sport
-- observation roses θ: cost invariant through indefinite checker propagation
set_option autoImplicit false
set_option maxHeartbeats 270000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Matrix Thera Verses
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {I : Type}[LinearOrder I][Fintype I]
namespace Credential
variable {S T: Finset I} {m n:ℕ} {a b:ℝ} {X Y: FC I}
lemma mono (u:Credential S m a X)(p:S⊆T)(h:m≤n): Credential T n a X:=by induction u with
 | coeff u L w e=> exact coeff u L (w.trans h) (fun i v=>p (e i v))
 | add _ _ h t=> exact h.add t
 | enlarge w _ h=> exact enlarge w h
lemma scale_c (p:Credential S m a X)(c:ℂ): Credential S m (‖c‖*a) (c • X):=by induction p with
 | coeff u L w e=> rw [←norm_mul,smul_smul]; exact coeff _ _ w e
 | add _ _ h t=> rw [smul_add,mul_add]; exact h.add t
 | enlarge w _ h=> exact enlarge (mul_le_mul_of_nonneg_left w (norm_nonneg _)) h
lemma sum_c {J:Type*}(F:Finset J)(f:J→ℝ)(g:J→FC I)(h:∀ i∈F,Credential S m (f i) (g i)):Credential S m (∑i∈F,f i) (∑i∈F,g i) :=by induction F using Finset.induction_on with
 | empty=> simpa [monomial] using (coeff (S:=S) 0 [] (Nat.zero_le m) (by simp))
 | @insert i F e ih=> rw [sum_insert e,sum_insert e]; exact (h i (mem_insert_self ..)).add (ih (fun j p=>h j (mem_insert_of_mem p)))
lemma mul_c (p:Credential S m a X)(h:Credential S n b Y) : Credential S (m+n) (a*b) (X*Y):=by
 induction p with
 | add _ _ p t=> rw [add_mul,add_mul]; exact p.add t
 | enlarge w _ t=> exact enlarge (mul_le_mul_of_nonneg_right w h.nonneg) t
 | coeff u L w e=> induction h with
     | add _ _ h t=> rw [mul_add,mul_add]; exact h.add t
     | enlarge w _ t=> exact enlarge (mul_le_mul_of_nonneg_left w (norm_nonneg _)) t
     | coeff v P W E=>
       have hp: monomial (L++P)=monomial L* monomial P:=by simp [monomial,rollC]
       have he:= (smul_smul u v (monomial (L++P)))
       rw [←norm_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,←hp,he]; apply coeff; rw [List.length_append]; omega
       intro i t; exact (List.mem_append.mp t).elim (e i) (E i)
lemma creation_c (i:I)(p:i∈S) : Credential S 1 1 (put i):=by
 simpa [monomial,rollC,creed] using (coeff (S:=S) 1 [(false,i)] (show [_].length≤1 from (le_refl _)) (by simpa))
lemma removal_c (i:I)(p:i∈S) : Credential S 1 1 (takeF i):=by
 simpa [monomial,rollC,creed] using (coeff (S:=S) 1 [(true,i)] (show [_].length≤1 from (le_refl _)) (by simpa))
-- one norm on a Ketch, no spin-dependent frame
open Buffered
lemma rights_c (x:Ket I)(k:‖x‖≤a)(e:withinM S x)(b:Bool): Credential S 1 (S.card*a) (creed b x):=by
  have h(i:I): ‖x.ofLp i‖≤a:=by
    rw [←basis_inner]; exact (norm_inner_le_norm ..).trans ((by simp [basisKet] : ‖basisKet i‖ * ‖x‖= ‖x‖).le.trans k)
  rw [show ↑S.card*a=∑ _ ∈ S,a by simp]; cases b
  · change Credential _ _ _ (create x); rw [create_def]; refine (?e:univ.sum (fun i=>x.ofLp i • put i)=S.sum (fun i=>x.ofLp i • put i)) ▸ ?_ -- direction?
    case e=> apply (sum_subset (subset_univ _) (by intro i _ q; simp [(within_test ..).mp e i q])).symm
    exact sum_c _ _ (fun i=> x.ofLp i • put i) (fun i t=> enlarge (by simpa using h i) ((creation_c _ t).scale_c _))
  change Credential _ _ _ (remove x); rw [remove_def]; refine (?w:univ.sum (fun i=>star (x.ofLp i) • takeF i)=S.sum (fun i=>star (x.ofLp i) • takeF i)) ▸ ?_
  case w=> apply (sum_subset (subset_univ _) (by intro i _ q; simp [(within_test ..).mp e i q])).symm
  exact sum_c _ _ (fun i=> star (x.ofLp i) • takeF i) (fun i t=> enlarge (by simpa using h i) ((removal_c _ t).scale_c _))
#print axioms rights_c
#print axioms mul_c
end Credential
open Buffered Lat Lattice Push.SectorMeasure Skye SU Scroll Tenant Rush Lifted Dial Cube Tulip
variable {N:Side} {Z:Set (Seat N)}
inductive Street (S:Support (More N)) : ℕ → ℝ → FC (Single N) → Prop
| one : Street S 0 1 1
| leg (i:Bool)(k:Seat N)(h:k∈S) (x:Ket (Single N)) (p:withinM (modesIn N {k}) x) : Street S 1 ‖x‖ (creed i x)
| add {a b:ℝ} {X Y:FC (Single N)} {m} : Street S m a X → Street S m b Y → Street S m (a+b) (X+Y)
| scale {a:ℝ} {X:FC (Single N)} {m} (z:ℂ) : Street S m a X → Street S m (‖z‖*a) (z • X)
| mul {a b:ℝ} {X Y:FC (Single N)} {m n} : Street S m a X → Street S n b Y → Street S (m+n) (a*b) (X*Y)
| enlarge {a b X m n} : a ≤ b → m≤n → Street S m a X → Street S n b X
namespace Street
variable {S T:Support (More N)} {X Y:FC (Single N)}{a:ℝ}{m:ℕ}
-- could use knode or univ bound; fixed
lemma positions (S:Support (More N)): (modesIn N S).card ≤ S.card*180:=by
 let f(x:Single N): Seat N×(SpinIdx×SU.Slot) := (node x.1.1,(x.1.2,x.2))
 rw [←card_image_of_injective (modesIn N S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (t:= S ×ˢ univ) (fun i hi=>?_)).trans
 swap; · obtain ⟨x,h,rfl⟩:= Finset.mem_image.mp hi; exact mem_product.mpr ⟨(modes_at ..).mp h,mem_univ _⟩
 rw [card_product,card_univ,Fintype.card_prod,SU.slots,show Fintype.card SpinIdx=4 from Fintype.card_fin _]
#print axioms positions
lemma nonneg (h:Street S m a X) : 0≤ a :=by
 induction h with
 | one=> norm_num
 | leg=> exact norm_nonneg _
 | add _ _ p g=> exact add_nonneg p g
 | scale z _ p=> exact mul_nonneg (norm_nonneg _) p
 | mul _ _ p g=> exact mul_nonneg p g
 | enlarge h _ _ p=> exact p.trans h
lemma harvest (h:Street S m a X): Credential (modesIn N S) m (180^m*a) X:=by
 induction h with
 | one=> simpa [monomial,rollC] using (Credential.coeff (S:=modesIn N S) 1 [] (m:=0) (le_refl _) (by simp))
 | leg i k l x p=>
   apply Credential.enlarge _ ((Credential.rights_c x le_rfl p i).mono (modes_monotone (singleton_subset_iff.mpr l)) le_rfl)
   apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact_mod_cast (by simpa using positions (N:=N) {k} :(modesIn N {k}).card≤180^1)
 | add _ _ p g=> rw [mul_add]; exact p.add g
 | @mul a b X Y m n _ _ p g=> rw [(by rw [pow_add]; ring : (180:ℝ)^(m+n) * (a*b)=(180^m*a)*(180^n*b))]; exact p.mul_c g
 | scale z _ p=> rw [mul_left_comm]; exact p.scale_c z
 | enlarge e g p t=> apply Credential.enlarge _ (t.mono (Subset.refl _) g); exact mul_le_mul (pow_le_pow_right₀ (by norm_num) g) e p.nonneg (by positivity)
lemma reflect (h:Street S m a X)(i:Axis)(z:ℤ): Street (S.image ((plane i z).anon N)) m a (theta (carR i z N) X):=by
 induction h with
 | one=> rw [theta_one]; exact one
 | leg b k l x p=>
   let V:=carR i z N; let v:=acts V.val x; have ht: withinM (modesIn N { (plane i z).anon N k}) v:=by
     rw [withinM,←(show ( {_}:Finset (Seat N)).image ((plane i z).anon N)={_} from image_singleton ..),←refl_modes i z {k}]; rw [show acts (twist (carR i z N) _) v=acts V.val (acts (cutM (modesIn N {k})) x) from (Fock.swivel ..).symm,p]
   have he:= Street.leg (!b) _ (mem_image_of_mem ((plane i z).anon N) l) v ht; cases b
   · change Street _ _ _ (theta V (create x)); rw [theta_upV]; apply Street.enlarge (le_of_eq (by simp [v])) le_rfl ((scale _ he):Street _ _ _ (-Complex.I • remove v))
   change Street _ _ _ (theta V (remove x)); rw [theta_downV]; apply Street.enlarge (le_of_eq (by simp [v])) le_rfl ((scale _ he):Street _ _ _ (Complex.I • create v))
 | add _ _ p g=> rw [theta_add]; exact p.add g
 | mul _ _ p g=> rw [theta_mul]; exact p.mul g
 | enlarge e l _ g=> exact enlarge e l g
 | scale z _ p=> rw [theta_smul,←norm_star z]; exact p.scale _
lemma mono (h:Street S m a X)(l:S⊆T) : Street T m a X:=by induction h with
 | one=> exact one
 | leg b k t x p=> exact leg b k (l t) x p
 | add _ _ p g=> exact p.add g
 | scale z _ p=> exact p.scale _
 | mul _ _ p g=> exact p.mul g
 | enlarge e h _ p=> exact enlarge e h p
#print axioms harvest
#print axioms reflect
end Street
end YM.CF.Papyrus.Franc.SatinForce
