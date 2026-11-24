import YM.SU5.Lamour.Glaze
/-! # uniform Langley, low and high f offsets. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.CF.Lamour
open Function Filter Metric NormedSpace Lattice Wilson Laurent Finset Lat Ember Jill Rush Cube Fock Peaks
open Fir Next.Free Bloch SU Tulip Dial Spire Flare Kea Velvet Pannier.Chancel
open Window (polarWork polarLift polarClad polarMetric projector_norm_fact)
open Onyx Emu Buffered
open scoped Topology NNReal ENNReal Matrix Matrix.Norms.L2Operator BigOperators MatrixOrder Kronecker ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable (N:Side)(j:ℕ)(M:Jill.Male)(z:ℝ)
abbrev sill (P:Bkg (More N)):=slant (tickA N) (draft (spar j M P) (tickA N) z) z
def slateL (i:Stag N):=slant Aop (draft (field (too N) j M i) Aop z) z
def garnish(b:Bool) (i:Stag N):=wish Aop (draft (field (too N) j M i) Aop z) z b
variable {N j z}
lemma arcReach (g: Pad j N)(p:0<z)(l:z≤1) : let P:= spar j M (1:Bkg (More N)); let F:= field (too N) j M; draft P (tickA N) z=Dofu N (fun i=>draft (F i) Aop z):=by
 intro P F; let A:=fun _:Stag N=> Aop; let G:= A+ z^2 •(1-A); let U:= F*(G*G)*F+(1-F); let Q:=Dofu N
 have he: tickA N= Q A:= landP N; have hu:P= Q F:= coasting g M; have hp:∀ i, IsUnit (U i):=fun i=> hinge_unit (crestQ j M (too N) g.1 i).1 A_id p l
 let B:= fun i=> (U i)⁻¹
 have hh:A*F + B*U = A*F+1:=by congr 1; funext i; exact (live (hp i)).2 -- tune
 have ht:Q G= Velvet.gate (tickA N) z:=by unfold G Velvet.gate; rw [map_add,map_smul,map_sub,map_one,he]
 have hf:(hinge P (tickA N) z)⁻¹=Q B:=by
    have hm:Q U=hinge P (tickA N) z:=by unfold U; rw [map_add,map_mul,map_mul,map_mul,map_sub,ht,hu,map_one]; rfl
    apply Matrix.inv_eq_right_inv; rw [←hm,←map_mul,show U * B=1 from funext fun i=> (live (hp i)).1,map_one]
 change draft P (tickA N) z= Q (G*F*B*(F*G)); rw [draft,Velvet.panel,hf, hu,map_mul,map_mul,map_mul,map_mul,ht]
lemma sill_eq (g: Pad j N)(p:0<z)(l:z≤1): sill N j M z 1=Dofu N (slateL N j M z):=by
 let A:=fun _:Stag N=> Aop; rw [sill,slant,arcReach M g p l,landP, ←map_one (Dofu N),←map_sub,←map_mul, ←map_mul,←map_smul]; rfl
lemma decorate_eq (b:Bool) (g: Pad j N)(p:0<z)(l:z≤1): wish (tickA N) (draft (spar j M (1:Bkg (More N))) (tickA N) z) z b=Dofu N (garnish N j M z b) :=by
 rw [wish, arcReach M g p l,landP]; cases b <;> simp only [hand, Bool.not_true,Bool.not_false,ite_true, Bool.false_eq_true,ite_false] <;> rw [←map_one (Dofu N),←map_sub, ←map_mul,←map_smul]<;> rfl
lemma pays_coin (p:1≤j)(c:0<z)(l:z≤1)(g:Even N.val)(i:Stag N): let d:= freckles N j M i.1
 ‖slateL N j M z i-lakeP N j M i‖^2 ≤ (1-d/coin d z)^2 * d⁻¹:=by
 let P:=field (too N) j M i; intro d; let e:= meadow_stats N j p M g i; let H:= polarWork P d; have he:0<d:= falls_down p i.1 M; let u:=coin d z; have hv:0<u:= coin_p he e.2.2.1
 rw [slateL, slant_diag e.1 e.2.2.2.2.1 c l he e.2.2.1]; change ‖(d/u) • H-H‖^2 ≤ _; rw [norm_sub_rev]; nth_rw 1 [←one_smul ℝ H]; rw [←sub_smul, norm_smul,mul_pow, Real.norm_of_nonneg (show 0≤1-d/u from sub_nonneg.mpr ((div_le_one hv).mpr (le_add_of_nonneg_right (show 0≤z^4*(1-d) from mul_nonneg (by positivity) (sub_nonneg.mpr e.2.2.1)))))]
 exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right zero_le_one).trans_eq (polarMetric e.1 e.2.2.2.1 he)) (by positivity)
omit M
abbrev bill (f:Stag N→Op SpinIdx)(i:Slot):=∑ k:Site N,‖f (k,i)‖^2
lemma garnish_air (p:1≤j)(C:ℝ)(u:0<C) : ∀ᶠ z:ℝ in 𝓝[>] 0,∀ (b:Bool)(N:Side),Even N.val→∀ M:Jill.Male,∀ i:Slot,bill (garnish N j M z b) i≤ C*N.val^4:=by
 obtain ⟨c,v,L⟩:= fret_budget p;
 let f(z:ℝ):= z^2*(c*Real.pi^2)
 have ht:Continuous f:=by unfold f; fun_prop
 have hu:∀ᶠ z:ℝ in 𝓝[>] 0,f z ≤ C:= (((ht.continuousAt.continuousWithinAt).tendsto).eventually (ge_mem_nhds (by simpa [f]))) -- tune filter
 filter_upwards [hu,self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one)] with z hv hz hx b N n0 M i
 let d:= freckles N j M; let g:= garnish N j M z b; have he:0<z:=hz
 unfold bill; apply le_trans (sum_le_sum (g:=fun x=> z^2*(d x)⁻¹) (fun x _=>?_)) _; swap
 · let r:Stag N:=(x,i); let h:= meadow_stats N j p M n0 r; let v:= falls_down p x M; exact wish_diag h.1 h.2.2.2.2.1 he hx v h.2.2.1 h.2.2.2.1 h.2.2.2.2.2 b
 rw [←mul_sum]; have h0: binSc N Real.pi=univ:=Finset.ext fun i=> by rw [binSc,mem_filter]; exact ⟨And.left, fun u=>⟨u,mass_valid i⟩⟩
 let y:=binSc N Real.pi; have hg:= L N Real.pi M Real.pi_pos; rw [h0] at hg; let Z:ℝ:=N.val; apply (mul_le_mul_of_nonneg_left hg (sq_nonneg z)).trans; rw [show z^2*(c*Real.pi^2*Z^4)=f z*Z^4 from (by unfold f; ring)]; exact mul_le_mul_of_nonneg_right hv (by positivity)
lemma coin_h (t:ℝ)(p:0<t)(z d:ℝ)(h:t≤d)(e:d≤1): (1-d/coin d z)^2 * d⁻¹ ≤ (z^4/t)^2 * t⁻¹:=by
 let u:=coin d z; have hD:0<d:=p.trans_le h; have hu:d≤u:=le_add_of_nonneg_right (mul_nonneg (by positivity) (sub_nonneg.mpr e)); have hc:0<u:= hD.trans_le hu; have hg:0≤1-d/u:=sub_nonneg.mpr ((div_le_one hc).mpr hu)
 let f:=1-d/u; have hx:f≤z^4/t:= by
    rw [show f=(z^4*(1-d))/u from (by unfold f; rw [sub_div' hc.ne']; unfold u coin; ring)] -- tune sub_div
    gcongr; exact mul_le_of_le_one_right (by positivity) (sub_le_self _ hD.le); exact h.trans hu
 exact mul_le_mul (pow_le_pow_left₀ hg hx _) (inv_anti₀ p h) (by positivity) (by positivity)
lemma sill_air (p:1≤j)(C:ℝ)(u:0<C) : ∀ᶠ z:ℝ in 𝓝[>] 0,∀ (N:Side),Even N.val→∀ M:Jill.Male,∀ i:Slot,bill (slateL N j M z-lakeP N j M) i≤ C*N.val^4:=by
 obtain ⟨c,hc,L⟩:= fret_budget p; obtain ⟨d,k,hd,l,X⟩:= Jill.zip p
 obtain ⟨s,hs,y⟩: ∃ s:ℝ,0<s ∧ c*s^2≤ C/2:= ((show ∀ᶠ x:ℝ in 𝓝[>] 0,0<x from self_mem_nhdsWithin).and (show ∀ᶠ x:ℝ in 𝓝[>] 0,c*x^2 ≤ C/2 from ((continuousAt_const.mul (continuous_id.continuousAt.pow 2)).continuousWithinAt.tendsto.eventually (ge_mem_nhds (by simpa using half_pos u))))).exists -- continuous type
 let t:=d*s^2; let f(z:ℝ):= (z^4/t)^2*t⁻¹; have ht:0<t:=mul_pos hd (pow_pos hs 2); have hu:Continuous f:=by unfold f; fun_prop
 filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one), hu.continuousAt.continuousWithinAt.tendsto.eventually (ge_mem_nhds (show f 0<C/2 by simpa [f] using half_pos u))] with z hz h g N t0 M i
 let d':=freckles N j M; let Q:= binSc N s; have hv:0<z:=hz; let F:(Stag N→ Peb):=slateL N j M z-lakeP N j M; let E(x):=‖F (x,i)‖^2
 let Y:ℝ:=N.val; have hx(x):0<d' x:=falls_down p x M; have he(x): E x≤ (1-(d' x)/coin (d' x) z)^2 * (d' x)⁻¹:= pays_coin M p hv h t0 (x,i)
 have hg(x)(u:x∈ Qᶜ):E x ≤ C/2:=by
    have h1:=meadow_stats N j p M t0 (x,i); have hp:s≤‖pm x‖:= by apply le_of_lt; simpa [Q,binSc] using u
    exact ((he x).trans (coin_h t ht z (d' x) ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hp _) hd.le).trans (X M _ (mass_valid x)).1) h1.2.2.1)).trans g
 have hc(x):E x ≤(d' x)⁻¹:=by
    apply (he x).trans; let y:=d' x; let v:=coin y z; have ht:y≤v:=le_add_of_nonneg_right (mul_nonneg (by positivity) (sub_nonneg.mpr (meadow_stats N j p M t0 (x,i)).2.2.1)); have hh:=hx x; have he:0<v:=(hx x).trans_le ht
    apply mul_le_of_le_one_left (inv_nonneg.mpr (hh.le)); apply pow_le_one₀ (sub_nonneg.mpr ((div_le_one he).mpr ht)); exact sub_le_self _ (div_nonneg (hx x).le he.le)
 change ∑ x,E x≤C*Y^4; rw [← sum_add_sum_compl Q]
 apply (add_le_add ((sum_le_sum (g:=fun i=> (d' i)⁻¹) (fun k _=> hc k)).trans (L N s M hs)) (sum_le_sum (g:=fun _ => C/2) hg)).trans; rw [sum_const,nsmul_eq_mul]; have hq:(Qᶜ.card:ℝ)≤Y^4:=by unfold Y; exact_mod_cast (card_le_univ Qᶜ).trans_eq (site_card N)
 refine (add_le_add (mul_le_mul_of_nonneg_right y (show 0≤Y^4 by positivity)) (mul_le_mul_of_nonneg_right hq (by positivity))).trans_eq ?_; ring
lemma full_bill (θ:Stag N→Op SpinIdx) (C:ℝ) (h:∀ i,bill θ i≤ C^2*N.val^4) (p:0≤ C): Buffered.Glaze.Billow C (Dofu N θ):=by
 intro i; have he:=nPos N; constructor
 · apply (sq_le_sq₀ (norm_nonneg _) p).1; apply (Gall.wave θ i).trans; exact (div_le_iff₀ (pow_pos he _)).mpr (h i.2)
 rw [←Dofu_s]; apply (sq_le_sq₀ (norm_nonneg _) p).1; apply (Gall.wave _ i).trans; apply (div_le_iff₀ (pow_pos he _)).2; simp_rw [Pi.star_apply,norm_star]; exact h i.2
theorem pollen (p:1≤j)(C:ℝ)(u:0<C) : ∀ᶠ z:ℝ in 𝓝[>] 0,∀ (N:Side)(g:Pad j N)(M:Jill.Male), Glaze.Billow C (sill N j M z 1-lake N j M) ∧∀ b:Bool,Glaze.Billow C (wish (tickA N) (draft (spar j M (1:Bkg (More N))) (tickA N) z) z b):=by
 filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds zero_lt_one), garnish_air p _ (pow_pos u 2), sill_air p _ (pow_pos u 2)] with z hz ht G H N g M
 have he:0<z:=hz; rw [sill_eq M g he ht,lake,←map_sub]; refine ⟨full_bill _ C (H N g.1 M) u.le,fun b=>?_⟩; rw [decorate_eq M b g he ht]; exact full_bill _ C (G b N g.1 M) u.le
end YM.CF.Lamour
#print axioms YM.CF.Lamour.pollen
#print axioms YM.CF.Lamour.sill_eq
