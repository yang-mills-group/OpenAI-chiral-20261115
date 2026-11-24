import YM.SU5.Reconstruction.Anvil.Chart
/-! # Merge chart analytic session. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {H H':Hilbert} (a:Axis)
local notation "χ" => onlyTime a
local notation "I"=> Complex.I
namespace Price
def axon (t:ℂ)(x:Wage): Wage:= facet (RealAge x)+ t • facet (Deeper x)
variable (Q:Price) (y:Bool)
private lemma axon_f (t:ℂ)(x:Meter): axon t (facet x)=facet x:=by simp [axon]
private lemma axon_add (t:ℂ)(x z:Wage): axon t (x+z)=axon t x+ axon t z:= by unfold axon; rw [show RealAge (x+z)= RealAge x+ RealAge z from rfl,deeper_add,facet_add,facet_add,smul_add]; abel
private lemma axon_sub (t:ℂ)(x z:Wage): axon t (x-z)=axon t x- axon t z:= by apply eq_sub_of_add_eq; rw [← axon_add, sub_add_cancel]
lemma axon_budget (x:Wage)(t:ℂ): Q.entry a y (axon t x)= axon t (Q.entry a y x) ∧ Q.compare a y (axon t x)= axon t (Q.compare a y x) ∧ Q.leaves a y (axon t x)= axon t (Q.leaves a y x):= by cases y<;>simp only [entry,compare,leaves, if_true,reduceCtorEq,if_false,axon_add,axon_sub,← facet_t,axon_f,and_self]
private lemma tunnel_ax (x:Wage)(u:x∈ Tunnel a)(t:ℝ)(v:t∈ Icc 0 1): axon ((t:ℂ)*I) x∈ Tunnel a:=by
 have H: Deeper (axon ((t:ℂ)*I) x)= t • Deeper x:=by ext i; simp [Deeper,axon,Complex.mul_im]
 have ht: (axon ((t:ℂ)*I) x a).re=(x a).re := by simp [axon,RealAge,Complex.mul_re]
 unfold Tunnel; rw [mem_setOf_eq,H,ht,rimPay_smul,norm_smul]; refine lt_of_le_of_lt ?_ u
 simp only [Real.norm_eq_abs, abs_of_nonneg v.1]; exact mul_le_of_le_one_left (norm_nonneg _) v.2
lemma axon_cost (x:Wage)(u:Q.permeates a y x)(t:ℝ)(v:t∈ Icc 0 1): Q.permeates a y (axon ((t:ℂ)*I) x):= by
 unfold permeates; rw [(Q.axon_budget a y x _).1,(Q.axon_budget a y x _).2.1,(Q.axon_budget a y x _).2.2]; exact ⟨tunnel_ax _ _ u.1 _ v,tunnel_ax _ _ u.2.1 _ v,tunnel_ax _ _ u.2.2 _ v⟩
variable {a b:Axis}(P:Price)(z:Bool)(S:OS.Semigroup H a) (T:OS.Semigroup H' b)
variable (A B:H.Op)(C D:H'.Op) (L R:H)(X Y:H')
local notation "f"=> Q.sale y S A B L R
local notation "g"=> P.sale z T C D X Y
lemma plank (U:Set Meter)(w:Dense U)
    (e:∀ x∈U,Q.permeates a y (facet x)→ P.permeates b z (facet x)→ Q.sale y S A B L R (facet x)= P.sale z T C D X Y (facet x))(x:Wage)(t:Q.permeates a y x)(v:P.permeates b z x) : f x = g x:= by
 -- tangent line filling vertical
 let W:Set Wage:= {q|Q.permeates a y q ∧ P.permeates b z q}; have h:IsOpen W:= IsOpen.inter (Q.permeates_open a y) (P.permeates_open b z)
 have hre (x:Meter)(p:facet x∈ W) : f (facet x)=g (facet x):= by
   let ℓ:=𝓝[facet⁻¹'W∩U] x; letI:ℓ.NeBot:= mem_closure_iff_nhdsWithin_neBot.mp (w.open_subset_closure_inter (h.preimage c_f) p)
   refine tendsto_nhds_unique (l:=ℓ) (( (Q.saleCont y S A B L R (And.left (show Q.permeates a y (facet x)∧ P.permeates b z (facet x) from p))).comp c_f.continuousAt).mono_left nhdsWithin_le_nhds) (Tendsto.congr' (f₁:=g ∘ facet) ?_ (((P.saleCont z T C D X Y ((show _∧ _ from p).2)).comp c_f.continuousAt).mono_left nhdsWithin_le_nhds))
   exact (show ∀ᶠ i in ℓ,facet i∈ W ∧ i∈ U from self_mem_nhdsWithin).mono fun i ⟨a,b⟩=>Eq.symm (e i b ((show _∧ _ from a).1) ((show _∧ _ from a).2))
 let M (t:ℂ):= axon t x; let V:= M⁻¹'W; have hM:Continuous M:=by unfold M axon; fun_prop
 let L':=fun t:ℝ=> (t:ℂ)*I
 have hx(T:ℝ)(p:T∈Icc 0 1) : M (L' T)∈ W:= ⟨Q.axon_cost a y x t T p, P.axon_cost b z x v T p⟩
 let V':= L' '' Icc 0 1; have he:= h.preimage hM; have H: V'⊆V:= by rintro _ ⟨i,a,rfl⟩; exact hx i a
 have c:IsPreconnected V':= isPreconnected_Icc.image L' (by unfold L'; fun_prop)
 have c0:(0:ℂ) ∈ V':= ⟨0,by simp, by simp [L']⟩; have hd(i):DifferentiableOn ℂ (fun z=>M z i) V:=by unfold M axon; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; fun_prop
 have E1:AnalyticOnNhd ℂ (f ∘ M) V:= Q.saleHol y S A B L R V M hd he (fun i h=> (And.left (show Q.permeates a y (M i) ∧ P.permeates b z (M i) from h)))
 have E2:AnalyticOnNhd ℂ (g ∘ M) V:= P.saleHol z T C D X Y V M hd he (fun i h=> And.right (show Q.permeates a y (M i) ∧ P.permeates b z (M i) from h))
 have hi:M I=x:=by ext i : 1; simp only [M,axon, facet_apply, Pi.add_apply,RealAge,Deeper,Pi.smul_apply,smul_eq_mul]; rw [mul_comm]; exact Complex.re_add_im _
 have he' : EqOn (f ∘ M) (g ∘ M) V':= by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (E1.mono H) (E2.mono H) c c0; intro o
    have ht:Tendsto (fun i:ℝ=> (i:ℂ)) (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)):= by
       apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; · simpa using (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))
       exact (show ∀ᶠ i in 𝓝[>] (0:ℝ), 0 < i from self_mem_nhdsWithin).mono (fun i v=> Complex.ofReal_ne_zero.mpr v.ne') -- coe
    obtain ⟨t,a,u⟩:= (ht.eventually (o.and (show ∀ᶠ i in 𝓝[≠] (0:ℂ),i∈V from mem_nhdsWithin_of_mem_nhds (he.mem_nhds (H c0))))).exists
    apply a; let q:= RealAge x+t • Deeper x; change f (M (t:ℂ)) = g (M (t:ℂ)); have hm: M (t:ℂ)= facet q:= by ext; simp [M,axon,q] -- test
    rw [hm]; exact hre _ (hm ▸ (show M _∈W from u))
 rw [← hi]; exact he' (show I∈V' from ⟨1,by simp,by simp [L']⟩)
end Price
end YM.Anvil
