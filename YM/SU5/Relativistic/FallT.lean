import YM.SU5.Relativistic.NodalT
/-! # Annihilator polynomial. Before shifting pulse to positive lattice times. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I

variable (r:ℝ) (hr:0<r)
local notation "U"=>Set.univ
local notation "L"=>Set.Icc (-π) π

-- list simply tuple(Finset integer ids, coefficient λ continuous transverse from U0). model USC.
-- at τ cost depends only on compact-set at that height.
def swell (s:Finset ℤ)(c:Behind → ℤ → ℝ)(k:Behind)(t:ℝ):ℂ:= ∑ j∈s,(c k j:ℂ)*surge j t
def speaker (s:Finset ℤ)(c:Behind → ℤ → ℝ)(k:Behind)(j:WalkA)(b:Bool):ℝ:= ∑ i∈s,c k i*nodes b k j i
abbrev scoring (f:Behind→ℂ→ℂ) (s:Finset ℤ)(c:Behind→ℤ→ℝ) := (∀ i, Continuous fun k=> c k i) ∧ ∀ k:Behind,∀ z:ℂ, z≠0→ ∑ j∈s,(c k j:ℂ)*z^j=f k z
section
variable {f g:Behind→ℂ→ℂ}{s t:Finset ℤ}{c d:Behind→ℤ→ℝ}
lemma tally_int (s:Finset ℤ)(c:Behind→ℤ→ℝ)(k:Behind)(i:WalkA)(b:Bool): ∑ j∈s,(c k j:ℂ)*(nodes b k i 1:ℂ)^j=(speaker s c k i b:ℂ):=by
 unfold speaker; push_cast; apply Finset.sum_congr rfl; intro j _; congr 1
 unfold nodes; simp only [Complex.ofReal_exp, ←Complex.exp_int_mul,Int.cast_one,mul_one]; congr 1; push_cast; ring
lemma scores_one : scoring (fun _ _=>1) {0} (fun _ _=>1):=⟨fun i=>continuous_const,fun _ _ _=>by simp⟩
lemma scores_mul (h:scoring f s c) (w:scoring g t d) : ∃ (S:Finset ℤ)(c':Behind→ℤ→ℝ), scoring (fun k z=> f k z*g k z) S c':=by
 classical
 let V:= s ×ˢ t; let G:=fun p:ℤ×ℤ=>p.1+p.2; let C:Behind→ℤ×ℤ→ℝ:=fun k p=> c k p.1*d k p.2
 let c₀:=fun k i=>∑ j∈ V,C k j * if G j=i then 1 else 0
 refine ⟨V.image G, c₀, fun i=>continuous_finsetSum _ fun j _=> ((h.1 j.1).mul (w.1 j.2)).mul continuous_const, fun k z hp=>?_⟩
 dsimp only; rw [← h.2 k z hp,←w.2 k z hp, sum_mul_sum]; unfold c₀; push_cast; simp_rw [sum_mul]; rw [sum_comm]; change ∑ x∈V,_=∑ i∈ s,∑ j∈t,_; unfold V; rw [sum_product]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj
 rw [sum_eq_single (i+j)]
 · dsimp only [C,G]; simp only [if_true,mul_one, Complex.ofReal_one,mul_one,Complex.ofReal_mul, zpow_add₀ hp]; ring
 · intro x _ g; have ht: G (i,j)≠x:=g.symm; simp [ht]
 exact fun m=> (m (mem_image_of_mem G (mem_product.mpr ⟨hi,hj⟩ : (i,j)∈ s ×ˢ t))).elim

lemma score_roots (W:Finset (WalkA × Bool)): ∃ s c, scoring (fun k z=>∏ p∈W,(z-(nodes p.2 k p.1 1:ℂ))^2) s c:=by
 induction W using Finset.induction_on with
 | empty=> simpa using (show ∃ s c, scoring (fun _ _=>1) s c from ⟨_,_,scores_one⟩)
 | @insert i W t ih=>
    obtain ⟨s,c,h⟩:=ih
    let f(k):= nodes i.2 k i.1 1
    have hc: Continuous f:=by unfold f nodes; fun_prop
    let d:= fun (k:Behind)(j:ℤ)=> if j=0 then -(f k) else 1
    let g:=fun (k:Behind)(z:ℂ)=> z- (f k)
    have hv:scoring g {0,1} d:=by
       refine ⟨fun j=>?_, fun k z _=>?_⟩
       · by_cases t:j=0; · simp only [d,t,if_true]; exact hc.neg
         simp only [d,if_neg t]; exact continuous_const
       simp [d,g]; ring
    obtain ⟨u,l,e⟩:= scores_mul hv hv; obtain ⟨a,b,p⟩:=scores_mul e h; refine ⟨a,b,p.1,fun k z hp=>?_⟩; dsimp only; rw [prod_insert t,p.2 k z hp,sq]

lemma bounds (b:Bool){n:ℤ}{k:Behind}(p:k∈sunshine)(s:Finset ℤ)(c:Behind→ℤ→ℝ)(f:ℝ→ℂ) (h:IntegrableOn f screen)(y:WalkA→ℂ)(r:∀ i∈s, HasSum (fun j=> y j* nodes b k j i) (pluse (n+i) f)) : HasSum (fun i=> (speaker s c k i b:ℂ)*y i) (pluse n (fun t=> swell s c k t*f t)) := by
 induction s using Finset.induction_on with
 | empty=> simp [swell,speaker,pluse,hasSum_zero]
 | @insert i s hi ih =>
    have hf: IntegrableOn (fun t=> (c k i:ℂ)*surge i t*f t) screen:= by
       simp_rw [mul_assoc]; exact (pluse_integrable h i).const_mul (c k i:ℂ)
    have hg:IntegrableOn (fun t=>swell s c k t*f t) screen:=by
       unfold swell; simp_rw [sum_mul]; refine integrable_finsetSum _ fun i _=>?_ ; simp_rw [mul_assoc]; exact (pluse_integrable h i).const_mul (c k i:ℂ)
    rw [show (fun t=>swell (insert i s) c k t*f t)=(fun t=> (c k i:ℂ)*surge i t*f t+swell s c k t*f t) from funext fun t=> by unfold swell; rw [sum_insert hi,add_mul]]
    rw [pluse_add n hf hg]; simp_rw [mul_assoc (c k i:ℂ)]; rw [pluse_const, pluse_after]
    have ht:= ((r i (mem_insert_self ..)).mul_left (↑(c k i):ℂ)).add (ih (fun z p=>r _ (mem_insert_of_mem p)))
    rw [show (fun x:WalkA=> (speaker (insert i s) c k x b:ℂ)*y x)=(fun x=> (c k i:ℂ)*(y x*nodes b k x i)+(speaker s c k x b:ℂ)*y x) from funext fun x=> by unfold speaker; rw [sum_insert hi]; push_cast; ring]; exact ht
end
end YM.CF.Crest.Sleet
