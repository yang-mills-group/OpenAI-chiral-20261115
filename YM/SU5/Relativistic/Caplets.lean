import YM.SU5.Relativistic.Colony
/-! # Frame `1-product`, directional steps stencil estimate.
One honored letter per probe/density. Sum rather than demand they all be honored.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace Damask
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I α:Type*}[LinearOrder I][Fintype I][Nonempty I]{l:List α}
-- mass budgets
lemma quantity_list {A:Type*}[NormedRing A][NormOneClass A] (x:α→ A)(p:ℝ)(v:0≤p)(t:List α)(g:∀ i∈t,‖x i‖≤p): ‖(t.map x).prod‖≤p^t.length:=by
 induction t with|nil=>simp| cons i t ih=>rw [List.map_cons,List.length_cons,pow_succ',List.prod_cons]; exact (norm_mul_le ..).trans (mul_le_mul (g i List.mem_cons_self) (ih fun j q=>g j (List.mem_cons_of_mem _ q)) (norm_nonneg _) v)
lemma quantity_exp (X:Fin 5→FC I)(R:ℝ)(h:0≤ R)(u:∀ i,‖X i‖≤R): ‖(List.ofFn X).prod‖≤ R^5:=by
 let K:=List.ofFn (@id (Fin 5)); have ht: List.ofFn X=K.map X:=by rw [show K.map X=_ from List.map_ofFn]; rfl
 rw [ht]; exact (quantity_list X R h K (fun i _=>u i)).trans_eq (by unfold K; rw [List.length_ofFn]) -- tune #lemma
lemma liquidate (X:Ring5→FC I)(R:ℝ)(h:0≤R)(u:∀ i,‖X i‖ ≤ R): ‖prime X‖ ≤ 1+(1+R)^5:= by
 unfold prime; refine (norm_sub_le ..).trans (add_le_add (by simp) (quantity_exp _ _ (by positivity) (fun i=> (norm_sub_le (1:FC I) _).trans (add_le_add (by simp) (u i)))))

section
variable {G:FC I}{S:Finset I}
abbrev fairVAT (S:Finset I) (G:FC I):=Fine S univ false G
-- use complements of product using lists
lemma liable (X:FC I)(p:fairVAT S X):fairVAT S (1-X):=by
 rw [sub_eq_add_neg,←neg_one_smul ℂ X]; exact Reed.Fine.one.add (p.scale (-1)) -- tune order
lemma collect_v {a:ℕ}(H:Fin a→ FC I) (R:ℝ)(p:1≤ R)(U:∀ i,‖1-H i‖≤R)(F:∀ i,fairVAT S (H i)):
    ∃ D:Fin a→FC I,
        1-(List.ofFn (fun i=> (1:FC I)-H i)).prod = ∑ i:Fin a,H i*D i ∧
        (∀ i,‖D i‖≤ R^a) ∧ (∀ i,fairVAT S (D i)) ∧
        ∀ i (X:FC I),(∀ j:Fin a,i ≠ j→ Commute X (H j)) → Commute X (D i):=by
 induction a with
 | zero=> refine ⟨fun i=>Fin.elim0 i,?_, fun i=>Fin.elim0 i,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩; simp
 | succ a ih=>
    let X(i:Fin a):= H i.succ
    obtain ⟨D,e,u,f,t⟩:= ih X (fun i=> U i.succ) (fun i=> F i.succ)
    let Z(i:Fin (a+1)) : FC I:= Fin.cases (1:FC I) (fun i:Fin a => (1-H 0)*D i) i
    refine ⟨Z,?_,fun i=> ?_,fun i=>?_,fun i=>?_⟩
    · rw [Fin.sum_univ_succ, List.ofFn_succ,List.prod_cons]
      let P:FC I:=(List.ofFn (fun i=> (1:FC I)-X i)).prod
      change 1-(1-H 0)*P = _
      have he(i:Fin a):X i*Z i.succ=(1-H 0)*(X i*D i):=by
        rw [show Z i.succ= _ from (show Z i.succ=(1-H 0)*D i from Fin.cases_succ ..),← mul_assoc, (fineWise (F _) (liable _ (F 0))).eq,mul_assoc]
      simp_rw [←show ∀ i,X i=H i.succ from fun _=>rfl,he] -- not syntax?
      rw [← Finset.mul_sum, ← e]; change _=H 0 *Z 0+(1-H 0)*(1-P); rw [show Z 0=1 from Fin.cases_zero ..,mul_one,mul_sub,mul_one]; abel
    · refine Fin.cases ?_ (fun j=>?_) i
      · rw [show Z 0=1 from Fin.cases_zero ..]; simpa using (one_le_pow₀ p)
      rw [show Z j.succ=(1-H 0)*D j from Fin.cases_succ ..]; exact (norm_mul_le ..).trans ((mul_le_mul (U 0) (u j) (norm_nonneg _) (zero_le_one.trans p)).trans_eq (pow_succ' ..).symm)
    · refine Fin.cases ?_ (fun j=>?_) i
      · rw [show Z 0=1 from Fin.cases_zero ..]; exact Fine.one
      rw [show Z j.succ=(1-H 0)*D j from Fin.cases_succ ..]; exact (liable (H 0) (F 0)).grow (f j)
    refine Fin.cases ?_ (fun j=>?_) i
    · intro x _; rw [show Z 0=1 from Fin.cases_zero ..]; exact Commute.one_right x
    intro x v; rw [show Z j.succ=(1-H 0)*D j from Fin.cases_succ ..]; exact ((Commute.one_right x).sub_right (v 0 (Fin.succ_ne_zero j))).mul_right (t j x (fun i h=>v _ (fun e=>h (Fin.succ_injective _ e))))
end

-- premove kernel estimate
variable {S T:Finset I}{W Φ :Wave I}{P:Op I}{b:Bool}{E R B:ℝ}
namespace Pledge
variable {X Y Z:α→Ket I}
local notation "Y₀" i:max=>creed b (cardH b (cutM S) (Y i))
local notation "Y₁" i:max=>creed b (cardH b (cutM S) (Z i))
lemma merger (p:IsStarProjection P)(g:Sea P W)(s: Sea (cutM S) Φ)(q:0<E)(t:E ≤ 1)(r:0<R)
    (x:∀ i, trim (hand (!b) (cutM S)) (X i))(u:∀ i,‖X i‖ ≤ 1)(y:∀ i, trim (hand b P) (Y i))(z:∀ i, ‖Z i-Y i‖ ≤ E^3)(h:∀ i,‖Y i‖≤ R) (c:∀ i, inner ℂ (Y i) (X i)=1)(d:∀ i j,i≠j→ inner ℂ (Y i) (X j)=0)
    (G:FC I) (J:fairVAT S G)(F:∀ i, Commute G (creed b (Z i)))(L:List α)(e:L.Nodup) : Yep E⁻¹ (acts (star (fo (fun i=>handy b S (X i) (Z i)) L*G)) Φ) W ((E*(R+3))^L.length*‖G‖) :=by
 have hv:Sheet S ∅ P (1:FC I) b X Y Z R E:=by
    refine ⟨y,h,?_,z,x,u,c,d,Fine.one⟩; intro i; rw [compl_empty]; exact within_univ _
 let Ω:= fun i=>X i; -- reuse lodging except comm fields
 have Hw:= lodging hv p g s q t
 let U(i):=creed (!b) (X i)
 have hU: Folder U (fun i=> Y₀ i) (fun i=> Y₁ i) (fun i=> creed b (Y i)) (fun i=> creed b (Z i)) b R E Φ W G := by
    refine { pitch:=Hw.pitch, switched:=Hw.switched,change:=Hw.change,price:=Hw.price,standing:=Hw.standing,spare:=Hw.spare,apart:=Hw.apart,occupy:=Hw.occupy,joint:=Hw.joint,fly:=Hw.fly,roar:=Hw.roar,frost:=Hw.frost,near:=Hw.near,lifetime:=Hw.lifetime,mail:=Hw.mail,parcel:=fun i=>?_,box:=F }
    unfold U; rw [show Y₁ i-Y₀ i=creed b (cardH b (cutM S) (Z i - Y i)) from (by unfold cardH; rw [map_sub,courage])]; exact fineWise ((passing S _ (x i) (within_univ _)).grow (passing S _ (raft_trim b (cutM_idp _) _) (within_univ _))) J
 exact hU.earn s.2.le q r t g.2 L e
lemma pledgeJoin {F G :FC I} (p: Yep R (acts (star F) Φ) W E)(q:Yep R (acts (star G) Φ) W B) : Yep R (acts (star (F+G)) Φ) W (E+B) := by
 rw [star_add,act_add]; intro i; rw [inner_add_left,add_mul]; exact (norm_add_le ..).trans (add_le_add (p i) (q i))
lemma pledgeSum (F:α→ FC I)(b:α→ℝ)(S:Finset α)(h: ∀ i∈ S,Yep R (acts (star (F i)) Φ) W (b i)): Yep R (acts (star (∑ i∈S,F i)) Φ) W (∑ i∈S,b i):=by
 classical
 induction S using Finset.induction_on with
 | empty=> intro i; simp
 | @insert i s p ih=> rw [sum_insert p,sum_insert p]; exact pledgeJoin (h i (mem_insert_self ..)) (ih fun i v=>h i (mem_insert_of_mem v))

-- honor whole prime block; across different honored indices choose subset/inj
variable {A Y' Z':α→ Ring5 → Ket I}
local notation "Finet" i:max j:max=> handy b S (A i j) (Z' i j)
local notation "Frame" i:max=>prime (fun k=>Finet i k)
lemma gives [DecidableEq α] (p:IsStarProjection P)(g:Sea P W)(s: Sea (cutM S) Φ)(q:0<E)(t:E≤1)(r:0<R)(d:1 ≤ B)
    (x:∀ i c,trim (hand (!b) (cutM S)) (A i c))(u:∀ i c,‖A i c‖≤1)(y:∀ i c,trim (hand b P) (Y' i c))(z:∀ i c,‖Z' i c-Y' i c‖ ≤ E^3)(f:∀ i c,‖Y' i c‖ ≤ R)(a:∀ i c j h,inner ℂ (Y' i c) (A j h)= if i=j ∧ c=h then 1 else 0)(v:∀ i j l k,i≠l ∨ j≠k → inner ℂ (Z' i j) (A l k)=0)(Z:∀ i j,‖1-Finet i j‖ ≤ B)
    (T:FC I)(V:fairVAT S T)(w:∀ i j,Commute T (creed b (Z' i j))) (l:List α)(e:l.Nodup) : Yep E⁻¹ (acts (star (fo (fun i=>Frame i) l*T)) Φ) W ((5*(E*(R+3)*B^5))^l.length*‖T‖):=by
 classical
 choose D he hu hv ht using fun i=> collect_v (a:=5) (fun k=> Finet i k) B d (Z i) (fun k=>fine_arch S (x i k) (Z' i k))
 let G(i:α)(j:Ring5):= Finet i j
 let C (i:α)(j:Ring5):= creed b (Z' i j)
 have hx(i j l k)(p:i ≠ l ∨ j ≠ k): Commute (C i j) (G l k):=by
    let X:=creed (!b) (A l k); let Y:=creed b (cardH b (cutM S) (Z' l k)); change Commute (C i j) ((1:FC I)+X*Y)
    have he: antiB (C i j) X=0:= by simpa using (siteCar (q:=0) (by simpa using v i j l k p) b)
    have hc:= eq_neg_of_add_eq_zero_left he
    have hs:C i j*Y= -(Y*C i j):=same_letter (b:=b) ⟨_,rfl⟩ ⟨_,rfl⟩
    apply (Commute.one_right _).add_right; change _= _; rw [←mul_assoc,show C i j* X= -(X* C i j) from hc,neg_mul,mul_assoc,hs]; simp only [mul_neg,neg_neg,mul_assoc]
 let K:= E*(R+3); let R':=5*(K*B^5); let F(i:α):=Frame i
 have hs (L:List α)(A':List α)(p':(L++A').Nodup)(ξ:α→Ring5)(G':FC I)(q':fairVAT S G')
      (ρ':∀ i∈L,Commute G' (C i (ξ i)))(t':∀ i∈A',∀ j,Commute G' (C i j)):
        let P0:=fo (fun i=>G i (ξ i)) L
        Yep E⁻¹ (acts (star ((P0* fo F A')*G')) Φ) W (K^L.length * R'^A'.length*‖G'‖):=by
    induction A' generalizing L ξ G' with
    | nil=>
      intro P0 -- tune
      simp only [fo,List.map_nil,List.prod_nil,mul_one,List.length_nil,pow_zero] -- tune
      let H:= {i// i∈L}; let x' (i:H):=A i.val (ξ i.val); let j'(i:H):= Y' i.val (ξ i.val); let z'(i:H):=Z' i.val (ξ i.val)
      have hp:L.Nodup:=by simpa using p'
      have ht':= hp.attach
      have ha: (fo (fun i:H=>handy b S (x' i) (z' i)) L.attach)=P0:=by
        let X:=fun i=>G i (ξ i); change (L.attach.map (X ∘ Subtype.val)).prod=(L.map X).prod; rw [←List.map_map, List.attach_map_subtype_val L]
      have h:= merger p g s q t r (S:=S) (X:=x') (Y:=j') (Z:=z') (fun i=>x ..) (fun i=>u ..) (fun i=>y ..) (fun i=> z ..) (fun i=>f ..) (fun i=>by unfold j' x'; rw [a,if_pos]; simp) (fun i j E=>by unfold j' x'; rw [a,if_neg]; exact fun X=> E (Subtype.ext X.1)) G' q' (fun i=>ρ' _ i.property) L.attach ht'
      rw [ha,List.length_attach] at h; exact h
    | cons i A' ih=>
      let P0:=fo (fun i=>G i (ξ i)) L; let Q:=fo F A'; let J(j:Ring5):= G i j; let Q₁(j:Ring5):= D i j
      have hQ(j:Ring5): Commute (Q₁ j) Q:=by
        have hs (i) : fairVAT S (F i):=by
          have hu(l:List Ring5):fairVAT S (fo (fun j=>1-G i j) l):=by induction l with|nil=>exact Fine.one|cons a l ih=> exact (liable _ (fine_arch _ (x i a) _)).grow ih
          apply liable _; have h:=hu (List.ofFn id); unfold fo at h; rw [List.map_ofFn] at h; exact h
        have hx':∀ l:List α, fairVAT S (fo F l):=by intro l; induction l with| nil=>exact Fine.one| cons i l ih=>exact (hs i).grow ih
        exact fineWise (hv i j) (hx' A')
      let C₀(j:Ring5):= P0*J j*Q*(Q₁ j*G')
      have hj: P0*fo F (i::A')* G'=∑ j:Ring5,C₀ j:=by
        change P0* (F i*Q)* G'= _; rw [show F i=∑ j:Ring5,J j*Q₁ j from he i,sum_mul,Finset.mul_sum,sum_mul]; apply sum_congr rfl; intro j _; unfold C₀
        have hp:= hQ j|>.eq; simp only [mul_assoc]; rw [← mul_assoc (Q₁ j) Q,hp,mul_assoc]
      let Z₀:= K^(L++[i]).length* R'^A'.length * (B^5*‖G'‖)
      have hy(j:Ring5):Yep E⁻¹ (acts (star (C₀ j)) Φ) W Z₀:=by
         let G₁:=Q₁ j*G'; let ξ':=Function.update ξ i j; have hp := List.nodup_append.mp p'
         have hι(a)(p:a∈L): a≠i:=hp.2.2 a p _ List.mem_cons_self
         have hK:fo (fun i=>G i (ξ' i)) (L++[i])=P0*J j:=by
            have hx:(L.map (fun i=>G i (ξ' i)))= L.map (fun i=>G i (ξ i)):= List.map_congr_left (by intro a u; unfold ξ'; rw [Function.update_of_ne (hι a u)]) -- tune
            simp only [fo,List.map_append,List.map_singleton,List.prod_append,List.prod_singleton,hx,show ξ' i=j from Function.update_self ..]; rfl
         have hF:fairVAT S G₁:= (hv i j).grow q'
         have hX:= ih (L++[i]) (by simpa using p') ξ' G₁ hF (fun a u=> ?_) (fun i' u' j'=> ?_) -- hX generates goals
         rw [hK] at hX -- need dsimp only
         apply (show Yep E⁻¹ (acts (star (C₀ j)) Φ) W (K^(L++[i]).length * R'^A'.length *‖G₁‖) from hX).weigh _ (inv_pos.mpr q).le
         apply mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (hu i j) (norm_nonneg _))) (by unfold R' K; positivity)
         -- commuting with unaffected extra debris
         · rcases List.mem_append.mp u with u|u
           · let v:= hι a u
             rw [show ξ' a=ξ a from Function.update_of_ne v ..]; exact ((ht i j _ (fun j' _=>hx _ _ _ _ (Or.inl v))).symm).mul_left (ρ' _ u)
           have h':a=i:=List.mem_singleton.mp u; subst a; rw [show ξ' i=j from Function.update_self ..]; exact ((ht i j _ (fun _ w=> hx _ _ _ _ (Or.inr w))).symm).mul_left (t' _ List.mem_cons_self _)
         have hν:i'≠i:=fun W=> (List.nodup_cons.mp hp.2.1).1 (W ▸ u'); exact ((ht i j _ (fun _ _=>hx _ _ _ _ (Or.inl hν))).symm).mul_left (t' i' (List.mem_cons_of_mem i u') j')
      -- finish
      change Yep _ (acts (star (P0 * _ * G')) Φ) W _; rw [hj]; apply (pledgeSum C₀ (fun _=> Z₀) univ (fun i _=>hy i)).weigh _ (inv_pos.mpr q).le
      apply le_of_eq; simp only [Z₀,Finset.sum_const,nsmul_eq_mul,Fintype.card_fin,Finset.card_univ,Ring5,List.length_cons,List.length_append,List.length_nil,pow_succ]; have he:R'=5*(K*B^5):=rfl; rw [he]; push_cast; ring
 have Ht:= hs [] l (by simpa using e) (fun _=>0) T V (by simp) (fun _ _ _=> w ..)
 exact (show Yep E⁻¹ (acts (star (fo F l*T)) Φ) W (R'^l.length*‖T‖) from by simpa [fo] using Ht)
end Pledge
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.Pledge.gives
