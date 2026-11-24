import YM.SU5.Relativistic.Mistral
/-!
# correcting Z at the sampled X sites. Still finite wind. All finite time.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{A d t w:ℕ}{R e γ:ℝ}
section
variable {α I:Type*}[LinearOrder I][Fintype I]{S:Finset I}
lemma rentX (X:α→ Ket I)(s:Finset α)(q:∀ i∈s,inner ℂ (X i) (X i)=1)(k:∀ i∈s,∀ j∈s,i≠j→ inner ℂ (X i) (X j)=0)(g:α→ℂ): ‖∑ i∈s,g i • X i‖^2=∑ i∈s,‖g i‖^2:=by
 classical
 have he(i)(p:i∈s):inner ℂ (g i • X i) (∑ j∈s,g j • X j)= (↑(‖g i‖^2):ℂ):=by
    rw [inner_sum,sum_eq_single i,inner_smul_left,inner_smul_right,q i p,mul_one]
    · rw [mul_comm]; change g i * (starRingEnd ℂ) (g i)=_; rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
    · intro j t y; rw [inner_smul_left,inner_smul_right,k i p j t (Ne.symm y),mul_zero,mul_zero]
    exact fun v=> (v p).elim
 have h: inner ℂ (∑ i∈s,g i • X i) (∑ i∈s,g i • X i)= (↑(∑ i∈s,‖g i‖^2):ℂ):=by rw [sum_inner, Complex.ofReal_sum]; exact sum_congr rfl he
 rw [inner_self_eq_norm_sq_to_K] at h; have hV: ↑(‖∑ i∈s,g i • X i‖^2)=(↑(∑ i∈s,‖g i‖^2):ℂ):=by push_cast; push_cast at h; exact h
 exact Complex.ofReal_inj.mp hV
end
variable {F:Waxy}{u k:ℕ}
lemma strum_at (T:ℕ)(F:Waxy)(S:Finset Cover)(a:Cover) (s:Ring5)(d:Fin 3) (p:∀ z∈district (TwistT T) a F,nodeC z∈S):withinM (modesIn n (Satin.region S n)) (strum n a T F (barred d s)):=by
 unfold withinM strum gust Finsupp.sum; simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j h; refine sum_congr rfl fun z v=>?_ ;  exact congrArg ((F i j z) • ·) (b_broad n _ _ (p _ (drive_entry a F i _ j h z v)) i _)
lemma pickClamp (d A:ℕ)(n:Side)(F:Waxy)(S T:Finset Cover)(U:Fin k→ Cover)(p:Set.InjOn (wrap n) T) (t:Injective U)(c:Fin 3)(Z V:ℝ)
    (x:∀ t,U t∈T ∧ nodeC (U t)∈S)(a:Fin k) (d':∀ z∈district (TwistT A) (U a) F,z∈ T ∧ nodeC z∈ S)
    (v: ∃ f:Fin k→WalkA, f a=0 ∧ ∀ i, U i=U a+tack ((d:ℤ) • f i) 0)(b:Ring5)(e:0≤ Z)(s:∀ D:Finset WalkA,∑ x∈D,‖F 2 0 ((d:ℤ) • x) - (if x=0 then 1 else 0)‖^2 ≤ Z^2)
    (j:Op (Single n))(q:IsStarProjection j) (m:‖strum n (U a) A F (barred c b)‖ ≤ V) (h:‖acts j (strum n (U a) A F (barred c b)) -strum n (U a) A F (barred c b)‖≤Z) :
      ∃ G: Ket (Single n), cardH false (cutM (Tset n)) G= cardH false (cutM (Tset n)) (strum n (U a) A F (barred c b)) ∧ ‖acts j G-G‖ ≤ 3*Z ∧ ‖G‖ ≤ V+Z ∧ withinM (modesIn n (Satin.region S n)) G ∧ ∀ (y:Fin k)(l:Ring5), inner ℂ (basisC n (U y) 2 (barred c l)) G= if y=a ∧ l=b then 1 else 0:=by
 classical
 let X(i:Fin k)(l:Ring5) := basisC n (U i) 2 (barred c l); let D:=strum n (U a) A F (barred c b)
 have hp(i j:Fin k)(l m: Ring5):inner ℂ (X i l) (X j m)= if i=j ∧ l=m then 1 else 0:=by unfold X; rw [windy_inner n _ _ _ _ _ _ T (x _).1 (x _).1 p]; simp [t.eq_iff, barred]
 obtain ⟨f,ha,hf⟩:=v; let J(z:WalkA):= (d:ℤ) • z; let B(i:Fin k):= F 2 0 (J (f i))
 have hV(i l):inner ℂ (X i l) D= if l=b then B i else 0:=by
   unfold X; rw [hf i, printed_inside n (U a) A F (barred c l) T (J (f i)) 0 (hf i ▸ (x i).1) (fun _ e=>(d' _ e).1) p]; simp [barred,J,B,TwistT] -- tune simp only
 have Hf:Injective f:=by intro i j q; apply t; nth_rw 1 [hf i]; nth_rw 1 [show _ = _ from q]; exact (hf j).symm -- order
 let g(i:Fin k) :ℂ:= B i-(if i=a then 1 else 0); let P:= ∑ i:Fin k,g i • X i b
 have ho:‖P‖ ≤ Z :=by
    apply (sq_le_sq₀ (norm_nonneg P) e).mp
    have hu: ‖P‖^2=∑ i:Fin k,‖g i‖^2:= rentX _ _ (fun i _=>(hp i i b b).trans (if_pos (And.intro rfl rfl))) (fun i _ j _ h=>by simp [hp i j b b,h]) g
    rw [hu]; apply le_trans _ (s (Finset.univ.image f)); rw [Finset.sum_image]; swap; · exact fun i _ j _ p=> Hf p
    apply le_of_eq; refine sum_congr rfl fun i _=>?_ ; unfold g B J; simp only [← ha, Hf.eq_iff] -- rewriting ha changes F 2 0? 0 Walk eq
 let G:= D-P; let W:=modesIn n (Satin.region S n)
 have hG(i):cardH false (cutM (Tset n)) (X i b)=0:= (hand_basis n _ (2:SpinIdx) _).trans (if_neg (by decide))
 have ht:= strum_at (n:=n) A F S (U a) b c (fun z g=>(d' z g).2)
 refine ⟨G,?_,?_,(norm_sub_le D P).trans (add_le_add m ho),?_,fun i l=>?_⟩
 · unfold cardH at hG; unfold G P cardH; rw [map_sub,map_sum]; simp_rw [map_smul]; rw [sum_eq_zero (fun i _=> by rw [hG,smul_zero]),sub_zero]
 · rw [show acts j G-G = (acts j D-D) -(acts j P-P) from (by unfold G; rw [map_sub]; abel)]; refine (norm_sub_le ..).trans ((add_le_add h ((norm_sub_le ..).trans (add_le_add ((shore_cost q P).trans ho) ho))).trans_eq ?_); ring
 · unfold G withinM; rw [map_sub,ht]; congr 1; unfold P; simp_rw [map_sum,map_smul]; exact sum_congr rfl (fun i _=> congrArg ((g i) • ·) (b_broad n (U i) S (x i).2 2 _))
 change inner ℂ (X i l) (D-P)=_; rw [inner_sub_right,hV]; unfold P; rw [inner_sum,sum_eq_single i,inner_smul_right,hp]; by_cases u:l=b; · rw [if_pos u,if_pos (show i=i ∧ l=b from ⟨rfl,u⟩),mul_one]; unfold g; rw [sub_sub_cancel]; simp only [u,and_true]
 · rw [if_neg u,if_neg (fun p=> u p.2),mul_zero,if_neg (fun p=> u p.2),sub_zero]
 · intro j _ w; rw [inner_smul_right,hp,if_neg (fun p=> w p.1.symm),mul_zero]
 simp
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.pickClamp
