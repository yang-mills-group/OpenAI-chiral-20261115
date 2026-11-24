import YM.CF.Cour.Salt
import YM.CF.Cour.Hue
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet Pec MeasureTheory
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
variable {n:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{u a C K b t:ℝ}{k:ℕ}
open Push.Uniform (Decay countCost)
def zoom(x:Orig n)(W: Pride n)(b C:ℝ)(i:BaseV n):ℝ:= let s:= home i; if x∈s then Branch.rent b s*(C*Real.exp (b*earY i)*‖oil W i‖) else 0
lemma hearth(W:Pride n)(p:0<b)(h:18*b ≤ a)(hv:0≤C)(v:BaseV n)(x:Orig n): let K:=C*Real.exp (36*b); zoom x W b C v ≤ K* Decay b x (vood v) * (nick a (earY v) * ‖oil W v‖):=by
 intro K; have hx:0≤ earY v:=ct_pos ..; have hh:0≤ K:=mul_nonneg hv (Real.exp_pos _|>.le); have hK:=Decay b x; unfold zoom; dsimp only; split; swap; · exact mul_nonneg (mul_nonneg hh (Push.Uniform.decay_pos ..).le) (mul_nonneg (nick_pos _ hx|>.le) (norm_nonneg _))
 next t=>
    have ht:Real.exp (b*(home v).card) * Real.exp (b*earY v) ≤ Real.exp (36*b)* Decay b x (vood v) * nick a (earY v):=by
       unfold Font.nick; apply le_trans _ (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _|>.le) (le_add_of_nonneg_right hx)) (mul_nonneg (by positivity) (Push.Uniform.decay_pos ..|>.le))); unfold Decay; simp_rw [←Real.exp_add]; apply Real.exp_monotone
       have he:(separation x (vood v):ℝ) ≤ ↑(home v).card:= Nat.cast_le.mpr ((((home_p v).1).lim _ t _ (home_p v).2).le : separation _ _ ≤ _)
       nlinarith only [p, mul_le_mul_of_nonneg_right h hx,mul_le_mul_of_nonneg_left (home_l v) p.le,mul_le_mul_of_nonneg_left he p.le, mul_nonneg p.le hx]
    unfold Branch.rent K
    apply le_trans ?_ ((mul_le_mul_of_nonneg_left ht (mul_nonneg hv (norm_nonneg (oil W v)))).trans_eq ?_ ) <;> first|apply le_of_eq; ring|ring
lemma ten (s:Signed)(x:Orig n)(hp:0<a) : (∑ y:Site n, Decay a x ((incX s).anon n (node y))) ≤ countCost a:=by
 let F:= (incX s).anon n ∘ node; let Y(y):=Decay a x y; have hf:Injective F:= ((incX s).anon_b ).1.comp (fun x y h => (assembly n).embed_injective (add_right_cancel (show _ + (1:Site (More n))=_+_ from h)))
 change ∑ i,Y (F i)≤ _; rw [← Finset.sum_image (g:=F) (f:=Y) (fun i _ j _ h=> hf h)]; refine le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ (Finset.image F Finset.univ)) (fun a _ _=> (Push.Uniform.decay_pos ..|>.le))) (Push.Uniform.decay_count hp _)
lemma cacao (W:Pride n)(p:0<b)(h:18*b ≤ a)(hv:0 ≤ C)(ht:∀ x,cents (node x) (W x) a ≤ t)(x:Orig n)(he:0 ≤ t): (∑ i:BaseV n,zoom x W b C i) ≤ Fintype.card Signed * (C*Real.exp (36*b)*t*countCost b):=by
 let U:= C*Real.exp (36*b); have hu:0 ≤U:=mul_nonneg hv (Real.exp_pos _|>.le)
 apply le_trans (sum_le_sum (s:=univ) fun i _=> hearth W p h hv i x); unfold BaseV; simp_rw [Fintype.sum_prod_type]; apply le_trans (sum_le_sum (s:=univ) (g:=fun _i:Signed=> U*t*countCost b) fun i _=>?_); rw [sum_const,card_univ,nsmul_eq_mul]
 let f(y: Site n):=Decay b x ((incX i).anon n (node y)); let G(j:Site n)(k l):=nick a (contour (node j) k l)*‖W j k l‖
 change ∑ j:Site n,∑ k,∑ l, U*f j*G j k l ≤ _; simp_rw [←Finset.mul_sum]; apply (sum_le_sum (s:=univ) (g:=fun j=> U*f j*t) (fun j _=> mul_le_mul_of_nonneg_left (ht _) (mul_nonneg hu (Push.Uniform.decay_pos ..|>.le)))).trans; simp_rw [mul_right_comm U (f _),←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (ten i x p) (mul_nonneg hu he)
lemma lumpP(a:ℝ)(p:0<a)(u:ℝ)(v:1≤u)(k:ℕ)(w:ℝ)(ht:0 ≤ w):∃ C:ℝ,0 ≤ C∧∀ (m B:Side)(U:Pride (CSide m B)), (∀ x,cents (node x) (U x) a≤ w) →∀ e:ℝ, Screen (Spire.soar m B e) (aether k u e m B) k (fun x=>pigment U x.val) (a/18) C:=by
 let b:=a/18; have hb:0<b:=div_pos p (by norm_num); obtain ⟨A,h,H⟩:=brassA k v hb
 have he:=Push.Uniform.count_pos hb; refine ⟨Fintype.card Signed*(A*Real.exp (36*b)*w*countCost b),(by positivity),fun m B U hU e=>?_⟩; let N:=CSide m B; let V(i:BaseV N):=A*Real.exp (b*earY i)*‖oil U i‖
 let J(S):= dest (@home N) S
 have hh S p (hp:p∈J S):Flash (Spire.soar m B e) (aether k u e m B) k S (bead U p∘ Subtype.val) (V p):= (mem_filter.mp hp).2 ▸ H e m B U p
 let f(i: BaseV N)(x:CapX m B e):=bead U i x.val
 refine ⟨_,_,fun S=> Flash.collects (J S) f V (hh S),fun i=>?_,fun x=>(shore_P U x.val).trans (lump _ _)⟩
 apply le_trans ?_ (cacao U hb (show 18*b ≤ a from by unfold b; linarith) (zero_le_one.trans h) hU i ht); rw [lump home]; unfold hitE hit0; rw [sum_filter]; apply sum_le_sum; intro S _; rw [mul_sum]; split
 next t => apply sum_le_sum; intro z h; unfold zoom; dsimp only; rw [(mem_filter.mp h).2,if_pos t]
 next t => apply Finset.sum_nonneg; intro z h; unfold zoom; dsimp only; rw [(mem_filter.mp h).2,if_neg t]
end YM.CF.Cour
