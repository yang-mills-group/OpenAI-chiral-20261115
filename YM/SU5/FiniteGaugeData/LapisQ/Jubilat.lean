import YM.SU5.FiniteGaugeData.LapisQ.EPOCH
set_option autoImplicit false
set_option maxHeartbeats 610000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
set_option quotPrecheck false
namespace Cordon
open Tulipe Vulcan Willow Nosh
variable {n:Side}{ρ C Δ ε σ K:ℝ}
variable {u:Stage}{P:Bed}
variable {A:Matrix (Body 2 n) (Body 2 n) ℝ}(g:Gate u P ρ C σ K n A)(p: Site n)
include g
lemma even_song (x:Site n): songV A (-x)= songV A x:=by
 have he:=congrFun (congrFun (g.stands x) (0,f0)) (-x,f0); change A (0+x,f0) (-x+x,f0)=_ at he; rw [zero_add,neg_add_cancel] at he; exact Eq.trans he.symm (congrFun (congrFun g.pays.1 (0,f0)) (x,f0))
lemma life_span : ρ^2*(∑ x:Site n,songV A x^2) ≤ 1 := by
 let o:Body 2 n:=(0,f0); let x: Body 2 n→ℝ:= Pi.single o 1; let G:=A*ᵥ x; have hh: dotProduct x x=1:=by unfold x; rw [single_one_dotProduct]; simp
 have ht:=sun_rays (d 1 n) g.pays g.cost (fun i=> (g.F.uniform.1 i).1) g.F.symmetric.1 x; change ρ^2* dotProduct G G≤ _ at ht; refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)) (ht.trans_eq hh); unfold dotProduct; rw [Fintype.sum_prod_type]; apply sum_le_sum; intro i _; have he:G (i,f0)=_:= Eq.trans (show G (i,f0)=A (i,f0) o from dotProduct_single_one _ _) ((show A (i,f0) o=songV A i from congrFun (congrFun g.pays.1 (0,f0)) (i,f0))) -- tune
 rw [← he,pow_two]; exact single_le_sum (fun a _=> mul_self_nonneg (G (i,a))) (mem_univ _)
lemma life_spend (x:Site n): |songV A x|≤1/ρ:=by
 have hp:=g.cost; refine (le_div_iff₀ hp).2 ((sq_le_sq₀ (by positivity) zero_le_one).1 ?_); rw [mul_pow,sq_abs,one_pow,mul_comm (_^2)]; exact le_trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun x _=>sq_nonneg (songV A x)) (mem_univ x)) (sq_nonneg ρ)) (life_span g)
omit g
-- mandates far second. later still root. stream by a physical tick size χ. flexible lag of request, uniformly bounded number of hops.
abbrev leapU(x:Cover)(i: Axis)(χ k:ℕ): Cover:= x+(χ*k) • step i
variable (D s χ:ℕ)(b:Axis)(z:Cover)
def missionV (i:Fin D):Site n:= wrap n (leapU z b χ i.val)
lemma triumph (v:0<χ)(e:D*χ ≤ n.val) : Injective (missionV (n:=n) D χ b z):=by
 intro k i h; apply Fin.ext; let g:= (wrap n z); have hf(j:Fin D): missionV D χ b z j (n:=n) b=g b+(j.val*χ:ℕ):=by unfold missionV leapU g; rw [map_add, map_nsmul,wrap_step]; change _+((χ*j.val) • step b:Site n) b=_; rw [Pi.smul_apply, nsmul_eq_mul, step_apply,if_pos rfl,mul_one,Nat.mul_comm] -- `(n:=)` pos syntax
 have hx:= congrFun h b; rw [hf,hf] at hx; have hu(j:Fin D):(j.val*χ:ℕ)<n.val:=lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right j.isLt v) e
 have he:= congrArg ZMod.val (add_left_cancel hx); rw [ZMod.val_natCast_of_lt (hu _),ZMod.val_natCast_of_lt (hu _)] at he; exact mul_right_cancel₀ v.ne' he
include g
lemma dilution (v:0<ε)(d:0<χ)(e:D*χ≤ n.val)(h:1<ρ^2*D*ε^2) :∃ i:ℕ, i<D ∧ |songV A (wrap n (leapU z b χ i))| < ε:=by
 by_contra! Z; let V:=univ.image (missionV (n:=n) D χ b z); have he: V.card=D:=by unfold V; rw [card_image_of_injective _ (triumph D χ b z d e),card_univ]; simp -- tune
 have hz:(D:ℝ)* ε^2≤ ∑ x:Site n,songV A x^2 := calc
    _=∑ i∈V, ε^2:=by rw [sum_const,nsmul_eq_mul,he]
    _≤∑ i∈V,songV A i^2:= sum_le_sum fun i p=> by
       obtain ⟨u,_,rfl⟩:=mem_image.mp p; rw [←sq_abs (songV A (missionV (n:=n) D χ b z u))]; -- `rw ←sq_abs` chooses eps lhs? intend
       refine pow_le_pow_left₀ v.le (Z u.val u.isLt) _
    _≤ _:= sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>sq_nonneg _)
 linarith only [h, mul_le_mul_of_nonneg_left hz (sq_nonneg ρ), life_span g]
omit g
lemma day_neg (i:ℤ)(d:ℕ): -i∈day d↔ i∈day d:=by simp only [day,mem_Icc,neg_le_neg_iff,neg_le]; omega
lemma day_wall(r:ℕ) {x:Cover}(p:x∈marketZ r): -x∈ marketZ r:= by
 refine Fintype.mem_piFinset.mpr fun i=> (day_neg ..).mpr (show x i∈day r from Fintype.mem_piFinset.mp p i) -- tune dependent inference x
lemma lap_wall(r:ℕ) {x:Cover}(p:lapse r x): lapse r (-x):=fun i=> (mt (day_neg (x i) r).mp (p i)) -- check
lemma bright (p:0<ρ) (v:0<ε):∃ D:ℕ,1< ρ^2*D*ε^2:=by
 obtain ⟨D,z⟩:= exists_nat_gt (1/(ρ^2 * ε^2)); exact ⟨D,(by nlinarith only [(div_lt_iff₀ (by positivity:0<ρ^2*ε^2)).mp z])⟩
lemma steamQ (ρ σ K:ℝ)(p:0<ρ)(h:0<χ):∃ c:ℝ,0<c∧∃ L J r:ℕ,∀ A':Side, L≤ A'.val → ∀ A:Matrix (Body 2 A') (Body 2 A') ℝ,∀ {C:ℝ}{u:Stage}{P:Bed}, Gate u P ρ C σ K A' A →∃ (x:Cover), x ∈ marketZ r ∧ lapse s x ∧ 0<x b ∧ c ≤ |songV A (wrap _ x)| ∧ ∃ i:ℕ,0< i ∧ i<J ∧ |songV A (wrap _ (leapU x b χ i))| ≤ c/2 :=by
 obtain ⟨w,u,r,M,U⟩:= fleetMX s σ ρ K; obtain ⟨J,t⟩:= bright p (half_pos u)
 refine ⟨w,u, M+J*χ,J,r,@fun n a A C u' P g=>?_⟩
 obtain ⟨z,h0,v,e⟩:=U g (Nat.le_trans (by omega) a); let x:= if z b≤0 then -z else z; suffices he:x∈ marketZ r ∧ lapse s x∧ 0<x b∧ w< |songV A (wrap _ x)| by
    obtain ⟨i,p,q⟩:= dilution g J χ b x (half_pos u) h (by omega) t -- order tune
    refine ⟨x,he.1,he.2.1,he.2.2.1,he.2.2.2.le,i, ?_,p,q.le⟩
    apply Nat.pos_of_ne_zero; intro k; apply absurd (le_trans (he.2.2.2.le) ?_) (not_le_of_gt (half_lt_self u)); refine le_of_lt ?_; subst i; simpa [leapU] using q
 unfold x; split_ifs with v0; swap; · exact ⟨h0,v,lt_of_not_ge v0,e⟩
 rw [map_neg, even_song g, Pi.neg_apply]; refine ⟨day_wall r h0,lap_wall s v,neg_pos.mpr (lt_of_le_of_ne v0 ?_),e⟩; intro t; apply v b; simp [day,t]
end Cordon
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Cordon.steamQ
