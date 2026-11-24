import YM.SU5.FiniteGaugeData.Pannier.Majus
/-! # Number budget on holes and the Ward approximate product estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Fixed Skye Pastry
open Damask
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n ι α : Type*}[LinearOrder n][Fintype n]
def Marque (b:Bool) (F: FC n) := ∃ x:Ket n,F=creed b x
abbrev Letter (F: FC n) := ∃ b: Bool,Marque b F
lemma courage (b:Bool)(u v : Ket n): creed b (v-u)=creed b v-creed b u:= by
 rw [eq_sub_iff_add_eq,←creed_a,sub_add_cancel]
lemma can_care {b:Bool}{A B:FC n}(h:Marque b A)(p:Marque b B): Marque b (A-B):=by
 obtain ⟨v,rfl⟩:= h; obtain ⟨u,rfl⟩:=p; exact ⟨v-u,(courage b u v).symm⟩
lemma same_letter {b:Bool}{A B:FC n}(p:Marque b A)(q:Marque b B) : A*B=-(B*A) :=by
 obtain ⟨a,rfl⟩:=p; obtain ⟨b',rfl⟩:=q; apply eq_neg_of_add_eq_zero_left; cases b with
 | false=> exact car_create ..
 | true=> exact car_rem ..
lemma anticar {A B:FC n}(p:Letter A)(q: Letter B) : ∃ c:ℂ,A*B+B*A=c•1:=by
 obtain ⟨i,a,rfl⟩:=p; obtain ⟨j,b,rfl⟩:=q; cases i <;> cases j
 · exact ⟨0,(car_create (n:=n) a b).trans ((zero_smul ..).symm)⟩
 · rw [add_comm]; exact ⟨_,car ..⟩
 · exact ⟨_,car ..⟩
 exact ⟨0,(car_rem (n:=n) a b).trans ((zero_smul ..).symm)⟩

variable {F: ι → FC n} {k:ℕ}{t ε v:ℝ}{ψ:Wave n}
abbrev fo (A : ι→ FC n) (l: List ι): FC n := (l.map A).prod
/-- kill after k appends; in taking estimates it's enough even for just such a fixed F -/
def Pause (F:ι→ FC n)(k:ℕ)(ψ: Wave n) := ∀ l:List ι, k < l.length → acts (fo F l) ψ=0
lemma still_fewer {L:List ι}(h:Pause F k ψ)(e:k<L.length): acts (fo F L) ψ=0:= h L e
lemma startPause (F:ι→FC n)(u:∀ i, acts (F i) ψ=0): Pause F 0 ψ:= by
 intro l h; induction l with
 | nil=> simp at h
 | cons i l ih=>
    rw [fo,List.map_cons,List.prod_cons,act_mul]; cases l with| nil=>simpa using u i | cons a t => exact (congrArg (acts _) (ih (by simp))).trans (map_zero _)
-- commute ζ to the left of all (`l` appended at end) with shrink condition. do using Pause definition via point recursive lemma:
lemma pause_one{A:FC n}(p:Letter A)(u:∀ i,Letter (F i))(h:Pause F k ψ):Pause F (k+1) (acts A ψ):=by
 -- use l.rcons decomposition, IH different ψ rank one lower acts F_i; prove rank one lower through r.higher orientation ANY F.
 intro l; induction k generalizing l ψ with
 | zero=>
    intro v
    -- decomp l = s++[x]; if ≤? F_x on Aψ gives cψ; exact; nonempty s =>.
    cases l using List.reverseRecOn with
    | nil=> simp at v
    | append_singleton l i _ =>
       obtain ⟨c,w⟩:= anticar (u i) p
       have hp: acts (F i) (acts A ψ)=c • ψ:= by
          rw [←act_mul,eq_sub_of_add_eq w,act_sub,act_smul,act_one,act_mul]
          rw [show acts (F i) ψ=0 from (by simpa [fo] using h [i] (show 0 < [i].length by simp)),map_zero,sub_zero]
       rw [fo,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,act_mul,hp,map_smul,h l (by simp at v; omega),smul_zero]
       -- ...
 | succ k ih=>
    intro v; cases l using List.reverseRecOn with
    | nil=> simp at v
    | append_singleton L i IH=>
        obtain ⟨c,w⟩:= anticar (u i) p
        have hp: acts (F i) (acts A ψ)=c • ψ-acts A (acts (F i) ψ):= by rw [←act_mul, eq_sub_of_add_eq w,act_sub,act_mul,act_smul,act_one]
        have he: k+1 < L.length:=by rw [List.length_append] at v; simp only [List.length_singleton] at v; omega
        have hz : Pause F k (acts (F i) ψ):= by
           intro l hl; rw [←act_mul, show _ * F i= fo F (l ++ [i]) from (by simp [fo]), h _ (by simp; omega)]
        rw [fo,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,act_mul,hp,map_sub,map_smul,h L he,ih hz L he,smul_zero,sub_self]

lemma pause_token (F:ι→ FC n)(p:∀ i, Letter (F i))(h:Pause F k ψ)(L:List (Token n)): Pause F (k+L.length) (acts (fo use L) ψ):=by
 induction L with
 | nil=>simpa [fo] using h
 | cons i L ih=> rw [fo,List.map_cons,List.prod_cons,act_mul,List.length_cons,←Nat.add_assoc]; exact pause_one ⟨_, i.val.2, rfl⟩ p ih
-- now a general estimate on product of F l. Norm budget encountered: powers from filter, including multiplier W≥1 only needed through caller. Then let Perturb take words outside.
def Coined (F:ι→FC n)(γ M:ℝ)(ψ:Wave n):= ∀ l:List ι,‖acts (fo F l) ψ‖ ≤ γ^l.length * M
lemma basisCost (D:ℝ)(d:∀ i, ‖F i‖≤D)(t:0<ε)(u:ε≤1) (h:Pause F k ψ)(p:0<D) : Coined F (ε*D) (‖ψ‖*ε⁻¹^k) ψ:=by
 intro l; by_cases e:k<l.length
 · rw [h l e,norm_zero]; positivity
 have he : ‖fo F l‖ ≤ D^l.length:=by
    induction l with -- h? e depends
    | nil=> simp [fo]
    | cons i l ih=> rw [fo,List.map_cons,List.prod_cons]; apply (norm_mul_le ..).trans; exact (mul_le_mul (d _) (ih (by simp at e; omega)) (norm_nonneg _) p.le).trans_eq (by rw [List.length_cons,pow_succ'])
 apply (Graph.spentS _ (fo F l) ψ).trans ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans ?_)
 rw [mul_pow,inv_pow]; have hp: 1 ≤ ε^l.length *(ε^k)⁻¹:= by rw [←div_eq_mul_inv,one_le_div (pow_pos t k)]; exact pow_le_pow_of_le_one t.le u (Nat.le_of_not_gt e)
 refine (le_mul_of_one_le_left (by positivity) hp).trans_eq ?_; ring
lemma token_prop (L:List (Token n)) : ‖fo use L‖ ≤ 1:= by induction L with|nil=> simp [fo]|cons i l h=> exact (norm_mul_le ..).trans ((mul_le_mul i.property h (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
lemma token_limit (L:List (Token n))(t:‖ψ‖=1): ‖acts (fo use L) ψ‖≤ 1 := (Graph.spentS _ _ ψ).trans (by rw [t,mul_one]; exact token_prop L)
lemma antiCycle (A:FC n)(L:List ι)(q:∀ i∈L,F i * A=-(A * F i)): let g:ℂ:=(-1)^L.length; fo F L*A=g • (A* fo F L):=by
 intro g; unfold g; induction L with
 | nil=> simp [fo]
 | cons i l ih=>
    rw [fo,List.map_cons,List.prod_cons,List.length_cons,pow_succ',mul_assoc,ih (fun i h=>q i (List.mem_cons_of_mem _ h)),Algebra.mul_smul_comm,←mul_assoc, q i List.mem_cons_self,neg_mul];  rw [mul_smul,neg_one_smul,smul_neg,mul_assoc]
-- stronger for mixed prefixes, congr with sign. future move Alpha signs
lemma swapAntiNorm (A:FC n)(l:List ι)(q:∀ i∈l,F i*A= -(A*F i))(ψ:Wave n): ‖acts (fo F l) (acts A ψ)‖ = ‖acts A (acts (fo F l) ψ)‖:=by
 rw [←act_mul,antiCycle A l q,act_smul,norm_smul,act_mul,norm_pow,norm_neg,norm_one]; simp

lemma perturb (J:ι→FC n)(t:0≤ v)(d:∀ i, ‖J i - F i‖ ≤ v)(q:∀ i j:ι, F i*(J j-F j)= - ((J j-F j)*F i)) {γ K:ℝ}(p:0≤γ)(hp:0≤K)(h:Coined F γ K ψ) : Coined J (γ+v) K ψ:=by
 let A:=γ+v
 have hs:0≤A:= add_nonneg p t
 have he(l:List ι) (k:List ι): ‖acts (fo F k) (acts (fo J l) ψ)‖ ≤ γ^k.length *A^l.length * K:=by
    induction l generalizing k with
    | nil=> simpa [fo] using h k
    | cons i l ih=>
       let E:=J i-F i; let η := acts (fo J l) ψ
       change ‖acts (fo F k) (acts (J i*fo J l) _)‖≤ γ^_*A^(l.length+1)*K
       rw [act_mul]; change ‖acts (fo F k) (acts (J i) η)‖≤_; rw [show J i=F i+E by dsimp only [E]; abel,act_add,map_add]
       apply (norm_add_le ..).trans; rw [swapAntiNorm E _ (fun j _=> q j i)]
       let Z:= fo F k; change ‖acts Z _‖+_ ≤_
       rw [←act_mul Z (F i)]; unfold Z; rw [show (fo F k)* F i= _ from (show _=fo F (k++[i]) from (by simp [fo]))];
       apply (add_le_add (ih (k++[i])) ((Graph.spentS _ _ _).trans (mul_le_mul (d _) (ih k) (norm_nonneg _) t))).trans_eq
       simp [pow_succ]; unfold A; ring
 intro l; simpa [fo] using he l []
lemma cashAlong (J:FC n)(s: Coined F t v ψ)(p:∀ i,Commute J (F i)): Coined F t (‖J‖*v) (acts J ψ):=by
 intro l; have h:Commute J (fo F l):=by induction l with|nil=> exact Commute.one_right _| cons i l ih=> exact (p i).mul_right ih
 rw [←act_mul,h.symm.eq,act_mul]; exact (Graph.spentS _ _ _).trans ((mul_le_mul_of_nonneg_left (s l) (norm_nonneg _)).trans_eq (by ring))
lemma deposit (J:FC n)(H:ι→FC n)(D:ℝ)
    (b:Bool)(f:∀ i,Marque b (F i))(g:∀ i,Marque b (H i))(q:∀ i,‖H i-F i‖ ≤ ε)(p:∀ i, Commute J (H i))
    (d:∀ i, ‖F i‖≤D)(t:0<ε)(u:ε≤1) (h:Pause F k ψ)(r:0<D) : Coined F (ε*(D+2)) (‖J‖*(‖ψ‖*ε⁻¹^k)) (acts J ψ):=by
 have e:=perturb H t.le q (fun i j=> same_letter (f i) (can_care (g j) (f j))) (by positivity) (by positivity) (basisCost D d t u h r)
 let x:= perturb F t.le (fun i=>(norm_sub_rev (F i) (H i)).trans_le (q i)) (fun i j=> same_letter (g i) (can_care (f j) (g j))) (by positivity) (by positivity) (cashAlong J e p)
 rw [show ε*(D+2)=ε*D+ε+ε from by ring]; exact x
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.deposit
