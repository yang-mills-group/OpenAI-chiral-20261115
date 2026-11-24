import YM.CF.Mesa.Planar
import YM.CF.Lattice.Local

/-! Combine data from all boundary frames with a single uniform margin schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B N:Side} {a b c:Index m}
abbrev GDist (g h:SU.E):=dist (SU.group.mat g) (SU.group.mat h)
abbrev Fa (m B:Side):=Site (Domain m B)→SU.E
def HintX (a:Index m)(K:ℝ)(f:Fa m B):=∀ x:Site (Domain m B),∀ i,x∈room m B a→ x+ step i∈room m B a→ GDist (f x) (f (x+step i))≤K/B.val
lemma seed_touch {K:ℝ} (hk:0≤K){a:Index m} (hm:2≤m.val)(f:Fa m B)(h:HintX a K f) {x y}(hx:x∈room m B a)(hy:y∈room m B a): GDist (f x) (f y)≤ 4*K*(separation x y/(B.val:ℝ)) :=by
  have H (l:Walk)(x:Site (Domain m B)) (hu:∀ z∈visits x l,z∈room m B a) : GDist (f x) (f (stop x l))≤l.length*(K/B.val) :=by
    induction l generalizing x with
    | nil => simp [stop]
    | cons j l ih =>
      let z:=x+j.vec; have he:=ih z (fun i g=>hu i (List.mem_cons_of_mem _ g)); have hs:= hu x List.mem_cons_self; have ht:=hu z (List.mem_cons_of_mem _ (by cases l <;> exact List.mem_cons_self))
      rw [stop, List.length_cons, Nat.cast_add, Nat.cast_one,add_mul,one_mul,add_comm _ (K/B.val)]
      apply (dist_triangle _ (SU.group.mat (f z)) _).trans; apply add_le_add _ he
      rcases j with ⟨i,n|n⟩; exact h x i hs ht
      have hb : z+step i=x:=by unfold z;simp [Step.vec]
      rw [dist_comm]; exact hb ▸ h z i ht (by rw [hb]; exact hs) -- tune
  have he:=H (march x y 1) x (visit_patch hx hy hm); rw [arrive] at he
  apply he.trans; have hy:=march_len x y 1 ((separation_comm ..).le :separation y x ≤ separation x y)
  have hk : 0≤K/(B.val:ℝ):=by positivity
  calc
    _ ≤ ((4*separation x y:ℕ):ℝ)*(K/B.val):=by gcongr
    _ = _ := by push_cast; ring

def Lesser (b a:Index m):=Fits m b a∧ b≠a
lemma lowt (h:Fits m b c)(g:Lesser c a):Lesser b a:=by
  refine ⟨fits_trans h g.1,fun E=>?_⟩; have hx:=fits_degree g.1 g.2; rw [E] at h; exact hx.not_ge (Finset.card_le_card (fits_os h))
private lemma off_both (m B:Side) {p q t}(h:p≠q)(hp:FitsX p t)(hq:FitsX q t)(l:p≠t)(g:q≠t){x y}(hx:roomX m B p x)(hy:roomX m B q y):2*B.val≤delta1 (Domain m B) x y :=by
  have he:= Or.resolve_left hp l; have hf:=Or.resolve_left hq g
  rw [(room_e _ _ _ _ he.1).mp hx,(room_e _ _ _ _ hf.1).mp hy,d_high,Nat.mul_comm 2]; apply Nat.mul_le_mul_left; exact d_even_sep (iff_of_false he.1 hf.1) h
lemma joined_step {x y:Site (Domain m B)}(h:Fits m b a)(g:Fits m c a)(hx:x∈room m B b)(hy:y∈room m B c)(t:separation x y < 2*B.val):
    ∃ z:Site (Domain m B), z∈room m B b ∧ z∈room m B c∧ separation x z≤separation x y ∧ separation z y ≤ separation x y:=by
  have he : x∈room m B a:=room_in h hx
  have hk : y∈room m B a:=room_in g hy
  let z : Site (Domain m B):=fun i=> if b i=a i then y i else x i
  refine ⟨z,(room_mem ..).mpr (fun i=>?_), (room_mem ..).mpr (fun i=>?_),?_,?_⟩
  · unfold z; split
    next l => rw [l]; exact (room_mem ..).mp hk i
    exact (room_mem ..).mp hx i
  · unfold z; split; exact (room_mem ..).mp hy i
    next l =>
      by_cases w:c i=a i; rw [w]; exact (room_mem ..).mp he i
      by_cases v:b i=c i; rw [←v]; exact (room_mem ..).mp hx i
      exact False.elim (t.not_ge ((off_both m B v (h i) (g i) l w ((room_mem ..).mp hx i) ((room_mem ..).mp hy i)).trans (component_le (x-y) i)))
  all_goals
    unfold separation pdist; apply Finset.sup_le; intro i _; first|change delta1 _ _ (z i)≤_|change delta1 _ (z i) _≤_
    unfold z; split <;> first | exact component_le (x-y) i | exact (d_id _).trans_le (Nat.zero_le _)
lemma rim_lip (d:ℕ)(K:ℝ)(hk:0≤K) : ∃ L:ℝ≥0,∀ m B (a:Index m)(f:Fa m B), 2≤m.val→degree m a=d→(∀ b,Lesser b a→ HintX b K f)→∀ x y:Site (Domain m B), Rim a x→Rim a y→ GDist (f x) (f y) ≤ L*dist (skull a x) (skull a y):=by
  let k:=Real.sqrt (SU.group.repDim:ℝ)
  use ⟨8*K+k,by unfold k; positivity⟩
  rintro m B a f h -- shape
  intro w v x y
  rintro ⟨b,hb,V,hx⟩ ⟨c,hc,J,hy⟩
  have hk' : 0≤ k:=Real.sqrt_nonneg _
  rw [skull_dist (room_in hb hx) (room_in hc hy) h]; change _ ≤ (8*K+k)*(separation x y/(B.val:ℝ))
  by_cases W : separation x y< 2*B.val
  · obtain ⟨z,ht,hV,ha,hu⟩:=joined_step hb hc hx hy W; have hQ:=seed_touch hk h f (v b ⟨hb,V⟩) hx ht; have hh:=seed_touch hk h f (v c ⟨hc,J⟩) hV hy
    have ge : 0≤separation x y/(B.val:ℝ) :=by positivity
    have H : 4*K*(separation x z/(B.val:ℝ))≤4*K*(separation x y/(B.val:ℝ)) :=by gcongr
    have hS : 4*K*(separation z y/(B.val:ℝ))≤4*K*(separation x y/(B.val:ℝ)) :=by gcongr
    exact (dist_triangle _ (SU.group.mat (f z)) _).trans ((add_le_add (hQ.trans H) (hh.trans hS)).trans (by nlinarith [mul_nonneg hk' ge]))
  push Not at W
  have he:2 ≤ separation x y/(B.val:ℝ) := (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast W)
  unfold GDist; rw [dist_eq_norm]; apply (norm_sub_le ..).trans
  rw [Gauge.unitary_frob (SU.group.mat_mul_star _), Gauge.unitary_frob (SU.group.mat_mul_star _)]
  change k+k≤_; nlinarith [mul_nonneg hk hk']
lemma rim_room {x} (h:Rim (m:=m) (B:=B) a x): x∈room m B a:=by obtain ⟨b,h,g,t⟩:=h; exact room_in h t
lemma extract_K (K:ℝ)(hk:0≤K) (d:ℕ) :∃ n:ℕ,∃ L:ℝ,0≤L ∧ ∀ (m B:Side) (a:Index m)(f:Fa m B),n≤B.val→2≤m.val→degree m a=d→d≤3→(∀ b,Lesser b a→HintX b K f)→ ∃ g:Fa m B, HintX a L g ∧ ∀ x, Rim a x→g x=f x:=by
  classical
  by_cases X:d≤3
  swap
  · exact ⟨0,0,le_rfl,fun _ _ _ _ _ _ _ h=> (X h).elim⟩
  obtain ⟨V,H⟩:=rim_lip d K hk; obtain ⟨r,U,t,h⟩:= lav X V
  obtain ⟨n,hn⟩:=exists_nat_gt (1/r)
  refine ⟨n,U,U.coe_nonneg,fun m B a f w hm he hD hv=>?_⟩
  let S :Set (Board (degree m a)):= skull (B:=B) a '' {x|Rim a x}
  have Hs:S⊆Peri _:= by rintro _ ⟨x,q,rfl⟩; exact (skull_rim (rim_room q)).mp q
  let F (z:Board (degree m a)):=if hx:z∈ S then f ((show ∃ x, Rim a x ∧ skull a x=z from hx).choose) else 1
  have hQ x (hx:Rim (B:=B) a x): F (skull a x)=f x:=by
    let v:=skull a x; have he:v∈S:= ⟨x,hx,rfl⟩
    let H :∃ z:Site (Domain m B),Rim a z∧ skull a z=v:=he
    change F v=_; rw [show F v=f H.choose from dif_pos he]; rw [skull_inj a hm (rim_room H.choose_spec.1) (rim_room hx) H.choose_spec.2]
  have hp : LipschitzOnWith V (SU.group.mat ∘ F) S:= LipschitzOnWith.of_dist_le_mul (by
    rintro z ⟨x,hx,rfl⟩ y ⟨u,g,rfl⟩; rw [Function.comp_apply,Function.comp_apply,hQ x hx,hQ u g]; exact H m B a f hm he hv _ _ hx g)
  have ha : ∀ z∈Peri _,∃ y∈S, dist z y ≤ r :=by
    intro z hx; obtain ⟨y,hy,hb,hh⟩:= stone_close B _ z hx; obtain ⟨x,ht,p⟩:=stone_reaches a hb hm
    refine ⟨y,⟨x,(skull_rim ht).mpr (p.symm ▸ hy),p⟩,hh.trans ?_⟩
    rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ t] at hn
    have hx:(n:ℝ)≤B.val:=by exact_mod_cast w
    nlinarith
  subst d
  obtain ⟨W,hW,Q⟩:=h S Hs (Set.toFinite _|>.image (skull a)) ha F hp -- ha maybe ∀ required
  refine ⟨W ∘ skull a,fun x i hx hy=> ?_,fun x hx=>by simp [Q (show skull a x∈S from ⟨x,hx,rfl⟩),hQ x hx]⟩
  have he:=hW.dist_le_mul _ (skull_ter hx) _ (skull_ter hy)
  exact he.trans (by rw [skull_dist hx hy hm]; calc
    _ ≤ (U:ℝ)*(1/B.val) := by apply mul_le_mul_of_nonneg_left _ U.coe_nonneg; gcongr; exact_mod_cast oneTouch x i
    _ = _:=by ring)
lemma extract_all (K:ℝ)(hk:0≤K): ∃ n:ℕ,∃ L:ℝ,0≤L ∧∀(m B:Side)(a:Index m)(f:Fa m B),n≤B.val→2≤m.val→degree m a≤3→(∀ b,Lesser b a→HintX b K f)→∃ g:Fa m B,HintX a L g ∧∀ x,Rim a x→g x=f x:=by
  choose n L hL H using extract_K K hk
  let A (x:ℕ) := Finset.range (x+1)
  refine ⟨∑ d∈A 3,n d,∑ d∈ A 3,L d,Finset.sum_nonneg (fun i _=>hL i),fun m B a f g hm he p=> ?_⟩
  have hg:degree m a∈A 3:=Finset.mem_range.mpr (by omega)
  obtain ⟨w,hW,t⟩:= H (degree m a) m B a f (le_trans (Finset.single_le_sum (f:=n) (fun i _=>Nat.zero_le _) hg) g) hm rfl he p
  exact ⟨w,fun x i hx hp=> le_trans (hW _ _ hx hp) (div_le_div_of_nonneg_right (Finset.single_le_sum (fun i _=>hL i) hg) (by positivity)),t⟩
end YM.CF.Mesa
