import GaugeFieldConstruction.Halloma4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n: Side}
variable (v:I↪ J)
section
variable {M E A:Type}[Fintype M][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](σ:J→Site n)
-- extension by zero coordinates. lift key jets
abbrev happyQ (z:Key I): Key J:= Function.extend v z 0
lemma etaμ(i:I)(x:Key I): happyQ v x (v i)=x i:= v.injective.extend_apply .. -- tune
lemma outsideμ (x:Key I)(j:J)(p:j∉Set.range v): happyQ v x j=0 := extend_apply' _ _ _ p
lemma baseμ: happyQ v 0=0:=by funext i; by_cases g:i∈Set.range v; obtain ⟨j,rfl⟩:=g; rw [etaμ]; rfl; exact outsideμ _ _ _ g
private lemma lup{i:Key I}{j:I}(s:ℂ):happyQ v (update i j s)= update (happyQ v i) (v j) s:=by
 funext k; by_cases h:k∈Set.range v
 · obtain ⟨l,rfl⟩:=h; rw [etaμ]; by_cases t:l=j; · subst l; simp
   rw[update_of_ne t, update_of_ne (v.injective.ne t),etaμ]
 rw [update_of_ne (fun t:k=v j=>h ⟨_,t.symm⟩), outsideμ v i k h,outsideμ _ _ _ h]
lemma Trimμ(f:Key J→E)(L:List I):lance (f∘happyQ v) L=lance f (L.map v)∘ happyQ v:=by
 induction L generalizing f with
 | nil=>rfl
 | cons i L ih=>
    change lance (cutI _ i) L = _; rw[show cutI (f∘happyQ v) i=(cutI f (v i))∘ happyQ v from ?_, ih]; rfl -- tune
    funext x; unfold cutI; simp only [comp_apply,lup]
lemma Tipμ (f:Key J→ E) (g:Key I→ E)(S:List I)(p: ∀ i,g i=f (happyQ v i)):tipI g S=tipI f (S.map v):=by
 rw [show g=f ∘ happyQ v from funext p, tipI,Trimμ,comp_apply,baseμ]
-- project retained.B table masked. weights. 
def Shrinky {F:Type}(U:Finset J → F): Finset I→ F:=fun i=>U (i.image v)
def squeezeD{E M:Type}(F: dues J M→ E): dues I M→ E:=fun x=>F (x.1.image v,x.2)
local notation "σ'"=> σ ∘ v
lemma travel_l (S:List I):ψS σ (S.map v)↔ψS (σ∘v) S:=by simp [ψS,List.map_map]
lemma voltδ (T:Finset I):T.image v ∈ realm_C σ ↔ T∈realm_C (σ∘v):= by
 rw [realm_C,realm_C, mem_filter,mem_filter]; simp only [mem_univ, true_and]; constructor
 · intro h; exact fun i t j u a=> v.injective (h (mem_image_of_mem v t) (mem_image_of_mem _ u) a)
 intro h i t j u a; obtain ⟨k,i',rfl⟩:= mem_image.mp t; obtain ⟨l,t',rfl⟩:= mem_image.mp u; exact congrArg _ (h i' t' a)
lemma Imageσ (x:Finset (Finset I)): Set.InjOn (fun i:Finset I=> i.image v) (x:Set (Finset I)):=by
 intro i _ j _ h; dsimp only at h; rw [←Finset.map_eq_image,←Finset.map_eq_image] at h; exact Finset.map_injective v h
lemma sight_r (Y:Cornea M A E n){r a T:ℝ} {Q:Finset J→ M→A→ E}{p:ℕ}(u:BookT Y Q p (realm_C σ) a r T)(s:0 ≤r): BookT Y (Shrinky v Q) p (realm_C (σ ∘ v)) a r T:=by
 obtain ⟨Q',m,t⟩:= u; refine ⟨Shrinky v Q',fun i x j=>m _ ((voltδ v σ i).2 x) j,fun x=> le_trans ?_ (t x)⟩
 let G:= (realm_C (σ∘v)).image (fun S=> S.image v)
 apply le_trans _ (sum_le_sum_of_subset_of_nonneg (show G⊆realm_C σ from (fun i h=>by obtain ⟨i,v,rfl⟩:=mem_image.mp h; exact (voltδ _ _ _).2 v)) (fun i h _=>mul_nonneg (pow_nonneg s _) (sum_nonneg fun j _=> mul_nonneg (Real.exp_pos _).le (Y.posG _ _ _ (m _ h j)))))
 apply le_of_eq; unfold G; rw[sum_image]; apply Finset.sum_congr rfl; intro i _; rw [card_image_of_injective _ v.injective]; rfl
 exact Imageσ v _
lemma sawP (Y: Cornea M A E n)(Q: Finset J→ M→A→ E)(p:Ledges Y σ Q): Ledges Y (σ∘v) (Shrinky v Q) :=by
 intro j y v' x t; have h:=p j y v' (x.image v) t; refine ⟨?_,fun i t=> h.2 _ (mem_image_of_mem v t)⟩; exact (voltδ v σ x).1 h.1
lemma pine_R (S:Finset I)(x:Key I):pine (S.image v) (happyQ v x)=pine S x:=by
 unfold Mew.pine; rw[prod_image]; apply prod_congr rfl; exact fun j _=> etaμ v j x; exact v.injective.injOn
lemma shock {E:Type}[AddCommMonoid E][Module ℂ E](U:dues J M→E)(x:Key I): Canz (σ ∘ v) _ (squeezeD v U) x=Canz σ _ U (happyQ v x):=by
 funext i; unfold Canz
 let G:= (realm_C (σ∘v)).image (fun S=> S.image v)
 apply Eq.trans _ (Finset.sum_subset (show G⊆ realm_C σ from (fun i h=>by obtain ⟨i,t,rfl⟩:=mem_image.mp h; exact (voltδ _ _ _).2 t)) ?_)
 · unfold G; rw [sum_image]; apply Finset.sum_congr rfl; intro i _; rw[pine_R]; rfl
   exact Imageσ v _
 intro j hj p; by_cases h:∀ i∈j, i∈Set.range v
 · exfalso; apply p; let S:=(univ:Finset I).filter fun i=>v i∈j
   have e:S.image v=j:=by ext i; rw[mem_image]; constructor; rintro ⟨a,b,rfl⟩; exact (mem_filter.mp b).2; intro g; obtain ⟨x,t⟩:= h _ g; exact ⟨x,mem_filter.mpr ⟨mem_univ _, t ▸ g⟩,t⟩
   exact mem_image.mpr ⟨S,(voltδ _ _ S).1 (e ▸ hj),e⟩
 push Not at h; obtain ⟨k,b,h⟩:=h; rw[show pine j (happyQ v x)=0 from Finset.prod_eq_zero b (outsideμ _ _ _ h),zero_smul] -- push Not? neq order
end
end Iona
end YM.CF.Scree.Ing
end
