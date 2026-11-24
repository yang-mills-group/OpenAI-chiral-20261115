import YM.CF.Stilo.Rig
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {ι I J A n:Type*}[LinearOrder n][Fintype n]
open Scree Pastry
lemma resetC(L:ι→n→ℂ)(K:ι→ι→ℂ)(p q:List ι)(i j:ι)[LinearOrder ι][Fintype ι]:let W:=taskC (lank L) (price K n)
 W (p++i::j::q)+W (p++j::i::q)=(K i j+K j i) • W (p++q):=by
 intro W; let B:ι→ FC (LinkI ι n):= largeH L + smallH K
 have h(t):spanP n (W t):=rent_m L K t
 apply borderE (sumB (h _) (h _)) (spanS (h _) _); rw [act_add,act_smul]; simp_rw [W,pitchA]; rw [← map_add, ← map_smul (pailL ..)];
 apply congrArg; change chime B _ _ + chime B _ _= _ • chime B _ _; unfold chime; rw [←act_add,←act_smul]; apply congrArg (fun x:FC (LinkI ι n)=> acts x _); simp only [rollC,List.map_append,List.prod_append,List.map_cons,List.prod_cons]
 rw [←mul_add, ←mul_assoc (B i), ←mul_assoc (B j),←add_mul, show B i* B j+B j*B i = (K i j+K j i) • 1 from (clash L K i j).trans (add_smul _ _ _).symm, Algebra.smul_mul_assoc,one_mul, Algebra.mul_smul_comm]
lemma picks_apps (K L:List ι) :∃ F:Bout ι→Bout ι, picks (K++L)= ((picks K).map (fun x=>⟨x.neg,x.front,x.back++L⟩))++ (picks L).map F ∧∀ i,(F i).front=i.front:=by
 induction K with
 | nil=> exact ⟨id,by simp [picks],fun i=>rfl⟩
 | cons i k ih=>
    obtain ⟨F,h,p⟩:=ih; refine ⟨beside i ∘ F,?_, fun x=>p x⟩; rw [List.cons_append,picks,h,picks]; simp only [List.map_cons,List.map_append,List.map_map, List.cons_append]; rfl
lemma pick_wear {x:Bout ι}(L:List ι)(p:x∈ picks L): x.front∈L ∧ x.back ⊆ L:=by
 induction L generalizing x with
 | nil=>simp [picks] at p
 | cons i l ih=> rw [picks,List.mem_cons] at p; rcases p with rfl|p; exact ⟨List.mem_cons_self ..,fun a h=>List.mem_cons_of_mem _ h⟩; obtain ⟨x,h,rfl⟩:=List.mem_map.mp p; obtain ⟨l,v⟩:=ih h; exact ⟨List.mem_cons_of_mem _ l,List.cons_subset_cons _ v⟩
lemma zoo[Ring A](f:List A)(x:A):f.sum*x=(f.map (·*x)).sum:= map_list_sum (AddMonoidHom.mulRight x) _
lemma cuttable [Ring A] (F:ι→A)(G:ι→ι→A)(L R:List ι)(h:∀ x∈L,∀ y∈R,G x y=0): taskC F G (L++R)= taskC F G L * taskC F G R:=by
 suffices T:∀ u (L:List ι), L.length < u→ (∀ x∈ L,∀ y∈ R,G x y=0) → taskC F G (L++R)=taskC F G L*taskC F G R from T (L.length+1) L (by omega) h
 intro n; induction n with
 | zero=>intro _ _; omega
 | succ n ih=>
    intro L v ht; cases L with
    | nil=> simp only [List.nil_append,task_zero,one_mul]
    | cons i L=>
       let W:= taskC F G; have hx :∀ x∈ L,∀ y∈R,G x y=0:= fun x h=> ht x (List.mem_cons_of_mem _ h)
       have hp := ih L (by simp only [List.length_cons] at v; omega) hx; obtain ⟨X,Y,H⟩:= picks_apps L R
       rw [List.cons_append,task_one,task_one,Y,hp,add_mul,mul_assoc,List.map_append,List.sum_append,List.map_map,List.map_map]; congr 1 -- should add first equal choose (_+·)
       rw [List.sum_eq_zero (l:= (picks R).map ((fun x=>(if x.neg then -G i x.front else G i x.front)*taskC F G x.back) ∘ X)) ?_,add_zero,zoo]; swap; · rintro a x; obtain ⟨u,p,rfl⟩:=List.mem_map.mp x; dsimp only [Function.comp_apply]; rw [H,ht _ (List.mem_cons_self ..) _ (pick_wear R p).1]; split <;> simp
       rw [List.map_map]; apply congrArg List.sum; apply List.map_congr_left; intro x p; obtain ⟨hb,hg⟩:=pick_wear L p; dsimp only [Function.comp_apply]; rw [ih _ (by simp only [List.length_cons] at v; have hh:=picks_mem p; omega) (fun x p=>hx x (hg p)),mul_assoc]
end YM.CF.Stilo
