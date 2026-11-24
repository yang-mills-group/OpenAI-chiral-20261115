import YM.CF.Peaks.Guide
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
lemma leakspan {N:Side}{a: Site N}(p:Walk) : separation a (stop a p)≤p.length:=by
  induction p generalizing a with
  | nil=> simp [stop]
  | cons d p ih=>
    have ht:separation a (a+d.vec)≤1:= Nat.le_of_lt_succ (( (trace_g a [d]).lim a (trace_source ..) _ (show (a+d.vec)∈traceP a [d] from trace_last ..)).trans_le (trace_k ..) ) -- adjust lt
    change separation a (stop _ p)≤_; exact (separation_triangle a _ _).trans ((Nat.add_le_add ht (ih (a:=a+d.vec))).trans_eq (by simp [add_comm]))
lemma compNear {e:ℝ}(he:0≤e)(U:Nom N P)(h:JointB G U e) (m:ℕ)(o:Site (More P))(hw:2*(m+G.count.val)+2<(More P).val):
  let g:=hue U.1 o; let Q:=july G g U; let V:=priceF (m+G.count.val) e
  (∀ i∈leaks (bay (terr _) o m), ‖brand (Q.1 i)-1‖≤V) ∧ ∀ i∈leaks (cloudG G (bay (terr _) o m)), ‖brand (Q.2 i)-1‖≤ e+G.count.val*V :=by
  intro g Q V; let n:=m+G.count.val
  let S:=bay (terr _) o m; let T:=bay (terr _) o n
  have he(x: Site (More P))(i:Axis) (p:x∈T)(l:x+step i∈T): ‖brand (Q.1 (x,i))-1‖ ≤ V:=gauge_light o x i n p l hw _ e he h.fg
  have hx:S⊆ T:=fun x p=> (bay_mem _).mpr ((bay_mem _).mp p |>.trans (Nat.le_add_right ..))
  constructor
  · rintro ⟨x,i⟩ h; exact he _ _ (hx (mem_filter.mp h).2.1) (hx (mem_filter.mp h).2.2)
  rintro ⟨x,i⟩ l
  let F:=travel Q.1 ((ratio G).embed x) (pathL G i)
  have hy : ‖brand F-1‖≤ G.count.val*V :=by
    have hq (k:ℕ)(x:Site (More P))(a:Axis)(h:separation o x+k≤n): ‖brand (travel Q.1 x (List.replicate k (posDir a)))-1‖≤ k * V := by
      induction k generalizing x with
      | zero => simp [travel,brand_one]
      | succ k ih =>
        let y:=x+step a
        have hh: separation o y+k≤ n:=by have ht:=oneTouch (N:=More P) x a; have hx:=separation_triangle o x y; change separation x y≤_ at ht; omega
        have hm:= ih y hh
        have ha:= he x a ((bay_mem _).mpr (Nat.le_trans (Nat.le_add_right ..) h)) ((bay_mem _).mpr (Nat.le_trans (Nat.le_add_right ..) hh))
        rw [List.replicate_succ,travel, brand_mul, Step.pos_read,Step.vec_pos]
        let A:=brand (Q.1 (x,a)); let W:=brand (travel Q.1 y (List.replicate k (posDir a))); change ‖A*W-1‖≤_
        rw [show A*W-1=A*(W-1)+(A-1) by rw [mul_sub,mul_one]; abel]; refine (norm_add_le ..).trans ?_; rw [brand_lef]
        push_cast; rw [add_mul,one_mul]; exact add_le_add hm ha
    have hm : (ratio G).embed x ∈ S := (mem_filter.mp (show x∈cloudG G S from (mem_filter.mp l).2.1)).2
    have hu: pathL G i = List.replicate G.count.val (posDir i):=by simp [pathL,straight,show ¬ (↑(G.count.val):ℤ)<0 by simp,posDir]
    unfold F; rw [hu]; exact hq _ _ _ (Nat.add_le_add_right (show separation o ((ratio G).embed x)≤ _ from (bay_mem _).mp hm) _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (brand F) 1).trans (add_le_add ((joint_g G U h g).follow _) hy)
-- cash with lengths fixed L
lemma payment (U:Bkg N)(x:Stem N)(σ μ:ℝ)(he:‖x-profile U‖<σ)(S:Seal (Site N))(H:∀ i∈leaks S, ‖brand (U i)-1‖ ≤ μ): fare S x 1≤ (leaks S).card*(σ+μ):=by
  unfold fare; rw [← nsmul_eq_mul,← Finset.sum_const]; refine sum_le_sum fun i h=> (norm_sub_le_norm_sub_add_norm_sub _ (profile U i) _).trans ?_
  refine add_le_add ((norm_le_pi_norm (x-profile U) i).trans he.le) ?_
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (H i h))).2 fun b=>?_
  cases b; swap; exact H i h
  change ‖star (brand _)-1‖≤μ
  rw [show ∀ X:Twig,‖star X-1‖= ‖X-1‖ from fun X=>by rw [← norm_star (X-1),star_sub,star_one]]; exact H i h

def windowC (m:ℕ):=64*((m:ℝ)+1)^4
lemma leak_size (S: Seal (Site N)): ((leaks S).card:ℝ)≤ S.card*4:=by
  have he:(leaks S).card≤(S ×ˢ (Finset.univ: Finset Axis)).card:=card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1,mem_univ _⟩
  simp [Axis] at he; exact_mod_cast he

def bushpr (m L:ℕ)(e:ℝ) := windowC m * (3*e +(1+(L:ℝ))*priceF (m+L) e)
lemma border (e:ℝ)(he:0<e)(x:Coil N P)(hp:x∈legal G e)(m:ℕ)(o:Site (More P))(hw:2*(m+G.count.val)+2<(More P).val):
  ∃ g, deal G (bay (terr _) o m) (jazz G g x) 1 ≤ bushpr m G.count.val e :=by
  obtain ⟨U,h,f⟩:= hp
  let L:=G.count.val; let g:=hue U.1 o; let Q:=july G g U; let V:=priceF (m+L) e; have hv:0≤V:=by unfold V priceF; positivity
  refine ⟨g,?_⟩
  let S:= bay (terr _) o m; let T:= jazz G g x
  obtain ⟨hl,hT⟩:= compNear G he.le U h m o hw
  have h1:‖T.1-profile Q.1‖<e:=by change ‖relayg g x.1-profile (gauge g _)‖<_; rw [profile_g,relayg_eq]; exact (norm_fst_le (x-unionP U)).trans_lt f
  have h2:‖T.2-profile Q.2‖<e:=by change ‖relayg _ _-profile (gauge _ _)‖<_; rw [profile_g,relayg_eq]; exact (norm_snd_le (x-unionP U)).trans_lt f
  have hs : (S.card:ℝ)*4≤ windowC m:=by have h:=Tenant.reach o m; unfold windowC; change (S.card:ℝ)≤_ at h; linarith
  have hc:(cloudG G S).card ≤ S.card:=by
    rw [← Finset.card_image_of_injective _ (ratio G).embed_injective]; exact card_le_card fun x hx=> by obtain ⟨y,hy,rfl⟩:= mem_image.mp hx; exact (mem_filter.mp hy).2
  have ht:(↑(cloudG G S).card:ℝ)*4≤windowC m:= le_trans (by exact mul_le_mul_of_nonneg_right (show (↑(cloudG G S).card:ℝ)≤ S.card by exact_mod_cast hc) (by norm_num)) hs
  apply (add_le_add (payment Q.1 T.1 e V h1 S hl) (payment Q.2 T.2 e (e+L*V) h2 (cloudG G S) hT)).trans
  exact (add_le_add (mul_le_mul_of_nonneg_right ((leak_size S).trans hs) (by positivity)) (mul_le_mul_of_nonneg_right ((leak_size (cloudG G S)).trans ht) (by positivity))).trans_eq (by unfold V L bushpr; ring)
end YM.CF.Peaks
