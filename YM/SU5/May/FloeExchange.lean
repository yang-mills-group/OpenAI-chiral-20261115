import YM.SU5.May.FloePluck
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Arctic
open Function Filter Finset Fock Emu
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
open NormedSpace
variable {α β:Type*} {B ε:ℝ} (p:1≤B)(t:0 ≤ ε) (x y:α→α→ℂ)(H:∀ i j, ‖x i j‖≤B)(L:∀ i j,‖y i j‖≤B)(d:∀ i j,‖x i j-y i j‖≤ε)
private lemma bin_length (l:List α) (b:Bout α)(p:b∈ picks l): b.back.length+1=l.length:=by
 induction l generalizing b with| nil=> simp [picks] at p | cons i l ih=> simp only [picks,List.mem_cons,List.mem_map] at p; rcases p with rfl|⟨b,p,rfl⟩; rfl; change (_+1)+1=_+1; exact congrArg (·+1) (ih b p) -- tune
private lemma picks_length (l:List α): (picks l).length=l.length:=by induction l with|nil=>rfl|cons i l h=>simp [picks,h]
private lemma kind (l:List α)(c:Cl α)(u:c ∈ claps l): c.up.length*2 +c.term.length = l.length:=by
 induction l generalizing c with
 | nil=> rw [claps,List.mem_singleton] at u; subst c; rfl
 | cons i l ih=> obtain ⟨d,p,e⟩:=List.mem_flatMap.mp u; have hp:=ih d p; rcases (List.mem_cons.mp e) with rfl|f; simp [extendsU,hp,Nat.add_assoc]; omega -- order
                 obtain ⟨b,h,rfl⟩:=List.mem_map.mp f; have ht:=bin_length _ _ h; unfold cites; dsimp; omega
private lemma total_len {γ α:Type*}(M:α→ List γ)(k:ℕ)(l:List α)(h:∀ v∈l,(M v).length≤ k): (l.flatMap M).length ≤ l.length*k:=by
 induction l with
 | nil=> simp
 | cons i l ih=> rw [List.flatMap_cons,List.length_append,List.length_cons, Nat.add_mul,one_mul,add_comm ((M i).length)]; exact Nat.add_le_add (ih fun j v=> h j (List.mem_cons_of_mem i v)) (h i (List.mem_cons_self ..))
private lemma claps_length (n:ℕ)(l:List α)(h:l.length≤ n): (claps l).length≤ (n+1)^l.length:=by
 induction l with
 | nil=>rfl -- le reflexivity.
 | cons i l ih=>
    set k:=l.length; have hk:l.length≤ n:=by rw [List.length_cons] at h; omega
    rw [claps]; apply le_trans (b:=(claps l).length*(n+1));
    · exact total_len _ (n+1) _ fun v p=>by simp only [besideX,picks_length,List.length_map,List.length_cons]; have ht:=kind l v p; omega -- tune
    rw [List.length_cons,pow_succ]; exact Nat.mul_le_mul_right _ (ih hk)
private lemma prod_norm (u:β→ℂ)(g:0≤B)(p:∀ j,‖u j‖ ≤ B)(l:List β): ‖(l.map u).prod‖≤ B ^ l.length:=by induction l with| nil=> simp| cons i l h=> rw [List.map_cons,List.prod_cons,norm_mul,List.length_cons,pow_succ']; exact mul_le_mul (p i) h (norm_nonneg _) g
-- note
include p t
private lemma price_norm (u v:β→ℂ)(a:∀ i,‖u i‖≤ B)(b:∀ i,‖v i‖≤ B)(h:∀ i,‖u i-v i‖≤ ε)(l:List β): ‖(l.map u).prod - (l.map v).prod‖≤ l.length*ε*B^l.length:=by
 have he:0≤B:= zero_le_one.trans p
 induction l with
 | nil=>simp
 | cons i l ih=>
    let Y:=(l.map v).prod; let X:=(l.map u).prod; change ‖u i*X-v i*Y‖≤_;
    calc
    _ ≤ ‖u i*(X-Y)‖+‖(u i-v i)*Y‖:=by nth_rw 1 [show u i*X-v i*Y=u i*(X-Y)+(u i-v i)*Y from (by ring)]; exact norm_add_le ..
    _ ≤ _:=by rw [norm_mul,norm_mul]; refine (add_le_add (mul_le_mul (a i) ih (norm_nonneg _) he) (mul_le_mul (h i) (prod_norm v he b l) (norm_nonneg _) t)).trans ?_; rw [List.length_cons,Nat.cast_succ,pow_succ]; nlinarith [mul_le_mul_of_nonneg_right p (show 0≤ε*B^l.length from by positivity)]
omit p t
private lemma total_norm (u v:β→ℂ)(l:List β)(h:∀ i∈l,‖u i-v i‖≤B): ‖(l.map u).sum-(l.map v).sum‖≤l.length*B:=by
 induction l with
 | nil=> simp
 | cons i l ih=> rw [List.length_cons,List.map_cons,List.map_cons, List.sum_cons, List.sum_cons,show ∀ a b:ℂ,u i+a-(v i+b)=(u i-v i)+(a-b) from fun _ _=>by abel,Nat.cast_succ,add_mul,one_mul]; apply (norm_add_le ..).trans; rw [add_comm (↑_ * B)]; exact (add_le_add (h _ (List.mem_cons_self ..)) (ih (fun j p=> h j (List.mem_cons_of_mem _ p))))
include H L d p t
lemma ballots (l:List α)(n:ℕ)(h:l.length≤ n): ‖runes x l-runes y l‖≤ (↑(n+1:ℕ):ℝ)^n*((n:ℝ)*ε*B^n):=by
 let C:= (n:ℝ)*ε*B^n; have he:0 ≤ B:= zero_le_one.trans p
 have hh(c:Cl α)(u: c∈claps l): ‖spinC x c-spinC y c‖≤ C:=by
    unfold spinC; split; swap; · simp; unfold C; positivity -- tune
    unfold offer; rw [← mul_sub,norm_mul,show ‖cval c.cpos‖=1 from (by unfold cval; split <;> simp),one_mul]
    have hu:c.up.length≤ n:=by have hf:= kind l c u; omega
    apply (price_norm p t (fun i:α × α=> x i.1 i.2) (fun i:α × α=> y i.1 i.2) (fun i=> H ..) (fun i=> L ..) (fun i=> d ..) c.up).trans; unfold C; exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hu) t) (pow_le_pow_right₀ p hu) (by positivity) (by positivity)
 exact (total_norm (spinC x) (spinC y) _ hh).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (claps_length n l h).trans (pow_le_pow_right₀ (by omega) h)) (by unfold C; positivity))
end YM.CF.May.Arctic
#print axioms YM.CF.May.Arctic.ballots
