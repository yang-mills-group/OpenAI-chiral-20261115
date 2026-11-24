import YM.CF.Dial.Skin
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
def vacancyY(N P:Side):Bale N P:=post (1,vacuumW P,vacuumW N)
lemma vacant(e:ℝ)(h:0<e): vacancyY N P∈zoneP G e:= ⟨_,tone G e h,by unfold vacancyY; simp [h]⟩
def feeG(m:ℕ) :ℝ:=16*((m:ℝ)+1)^4
def feeB(m L:ℕ)(e ε:ℝ): ℝ := feeG m*(4*(e+priceF (m+L) e) + 4*(2*e+L*priceF (m+L) e)+2*(e+ε))
lemma cloud_count(S:Seal (Site (More P))) :(cloudG G S).card ≤ S.card:=by
  rw [← Finset.card_image_of_injective _ (ratio G).embed_injective]; exact card_le_card fun x hx=> by obtain ⟨y,hy,rfl⟩:= mem_image.mp hx; exact (mem_filter.mp hy).2
omit G
lemma leading(m L:ℕ)(δ:ℝ)(h:0<δ): ∃ d ε:ℝ,0<d∧0<ε∧ feeB m L d ε≤δ ∧ ∀ {N:Side}(x:Stun N)(i:Site (More N)), ‖hook x i-apex.val‖≤(4*m:ℕ)*d+d → ‖palt x i-palt (vacuumW N) i‖ ≤ ε :=by
  let E:=feeG m; have he:0<E:=by unfold E feeG; positivity
  let ε:=δ/(4*E); have hp:0<ε:=by unfold ε; positivity
  have hV : feeB m L 0 ε<δ:=by unfold feeB priceF; unfold ε E at *; field_simp; grind
  obtain ⟨e,r,hR⟩:=close_tick ε hp
  have ht : ContinuousAt (fun i=>feeB m L i ε) 0:=by unfold feeB priceF; fun_prop
  let f(i:ℝ):=((4*m:ℕ):ℝ)*i+i
  have hh: ContinuousAt f 0 := by unfold f; fun_prop
  have he: ∀ᶠ i in 𝓝[>] (0:ℝ), feeB m L i ε<δ ∧ f i<e:= Eventually.and (ht.continuousWithinAt (gt_mem_nhds hV)) (hh.continuousWithinAt (gt_mem_nhds (show f 0<e by simpa [f]))) -- tune
  have hh : ∀ᶠ i in 𝓝[>] (0:ℝ), (0:ℝ) < i := self_mem_nhdsWithin
  obtain ⟨d,hd,p⟩:= (hh.and he).exists
  exact ⟨d,ε,hd,hp,p.1.le,fun {N} x i he=> (hR (N:=N) x (vacuumW N) i i (he.trans_lt p.2)).le⟩
lemma sluice(m:ℕ)(L:Side)(δ:ℝ)(h:0<δ): ∃ d:ℝ, 0<d ∧ ∀ {N P:Side}(G:Ratio N P), G.count=L→2*(m+L.val)+2<(More P).val →∀ x∈zoneP G d, ∀ o:Site (More P), ∃ g, bookK G (novel G g x) (vacancyY N P) (bay (terr _) o m)≤ δ:=by
  obtain ⟨d,ε,hs,hε,hR,r⟩:=leading m L.val δ h; refine ⟨d,hs,?_⟩; intro N P G he hp x hx o; subst L
  obtain ⟨u,h,hh⟩:=hx; obtain ⟨g,ge⟩:= apex_eq (u.2.1 o)
  let y:=novel G (hueK g o u) x; let V:= frost G (hueK g o u) u; let Z:= post V
  have he: ‖y-Z‖<d:=by unfold y Z V; rwa [←speak,novel_r]
  refine ⟨hueK g o u,le_trans ?_ hR⟩;
  obtain ⟨hu,hQ⟩:=hear G g o u ge V rfl d hs h m; obtain ⟨hL,ht⟩:=prism_g G u g o m d h hs hp
  let S:=bay (terr _) o m; let W:=cloudG G S; let R:=feeG m; let t:=priceF (m+G.count.val) d; have hz:0≤t:= by unfold t priceF; positivity
  have hs': (↑S.card:ℝ)≤R:= Tenant.reach ..; have hW: (↑W.card:ℝ)≤R:=(by exact_mod_cast cloud_count G S : (↑W.card:ℝ)≤ S.card) |>.trans hs'
  have h1 : ‖y.1.1-Z.1.1‖<d:=(norm_fst_le (y-Z).1).trans_lt ((norm_fst_le (y-Z)).trans_lt he)
  have hb := payment V.1.1 _ _ t h1 S hL
  have hx := payment V.1.2 y.1.2 d (d+G.count.val*t) ((norm_snd_le (y-Z).1).trans_lt ((norm_fst_le (y-Z)).trans_lt he)) W ht
  have hk: deal G S y.1 1≤ R*(4*(d+t)+4*(2*d+G.count.val*t)) :=by
    have hl := (leak_size S).trans (mul_le_mul_of_nonneg_right hs' (by norm_num))
    have hu := (leak_size W).trans (mul_le_mul_of_nonneg_right hW (by norm_num))
    have he := add_le_add (hb.trans (mul_le_mul_of_nonneg_right hl (by positivity))) (hx.trans (mul_le_mul_of_nonneg_right hu (by positivity)))
    apply he.trans; exact le_of_eq (by ring)
  have h3: ∑ i∈S, ‖y.2.1 i-palt (vacuumW P) i‖≤R*(d+ε):=by
    calc
      _ ≤ ∑ _∈S,(d+ε):=by
        refine sum_le_sum fun i p=> (norm_sub_le_norm_sub_add_norm_sub _ (Z.2.1 i) _).trans ?_
        exact add_le_add ((le_trans (norm_le_pi_norm (y-Z).2.1 i) ((norm_fst_le (y-Z).2).trans (norm_snd_le (y-Z)))).trans he.le) (r _ _ ((hu i p).trans (le_add_of_nonneg_right hs.le)))
      _ ≤ _:=by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hs' (by positivity)
  have h4:∑ i∈W,‖y.2.2 i - palt (vacuumW N) i‖ ≤ R*(d+ε):=by
    calc
      _ ≤∑ i∈W,(d+ε):=sum_le_sum fun i p=> (norm_sub_le_norm_sub_add_norm_sub _ (Z.2.2 i) _).trans (add_le_add ((norm_le_pi_norm (y-Z).2.2 i).trans ((norm_snd_le (y-Z).2).trans ((norm_snd_le (y-Z)).trans he.le))) (r _ _ (hQ i p)))
      _ ≤ _:=by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hW (by positivity)
  have hT : (vacancyY N P).1=1:=by unfold vacancyY post unionP; simp only [Prod.fst_one, Prod.snd_one, profile_trivial]; rfl
  rw [bookK,hT]; exact (add_le_add (add_le_add hk h3) h4).trans (le_of_eq (by unfold feeB; change _= R * (4*(d+t)+4*(_+G.count.val*t)+_); ring))
end YM.CF.Dial
