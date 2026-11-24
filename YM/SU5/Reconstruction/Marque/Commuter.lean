import YM.SU5.Reconstruction.Marque.Detector
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Passage
open Function Set Filter Real Complex Metric
open scoped Topology Classical
variable {H:Type*} [MetricSpace H] (P:Passage H)
local notation "W"=> Wander H
abbrev spokes := ∀ {g:Two},∀ u: W, u∈P.ok 1 → ∀ v:W,v∈P.ok g→ Commute u v
abbrev drum := ∀ (t:ℝ)(p:ℂˣ) (u v:W),u∈P.ok (Tuning t)→ v∈P.ok (Pole p)→ Commute u v
structure Centre : Prop where
 spoke : P.spokes
 pole : P.drum
 pinBack : (1:W) ∈ P.ok bezel
local notation "κ"=> P.ok
variable {P} (c:P.Centre) (h:P.Upright)
def chit{G:Type*}[Group G](u v:G):= u*v*u⁻¹*v⁻¹
omit c h in lemma barter{G:Type*}[Group G](u v:G): Commute u v↔chit u v=1:= by
 rw [commute_iff_eq]; constructor;· intro t; unfold chit; rw [t];group
 intro t; rw [show u*v=chit u v*(v*u) from (by unfold chit; group),t, one_mul]
variable {g1 g2:Two}{u u' v v': H≃ᵢ H}(p : u∈P.ok g1)(p' : u'∈P.ok g1)(q : v∈P.ok g2)(q' : v'∈P.ok g2)
include c p p' q
lemma sameAdj: rehome u v=rehome u' v:= by
   have ht: Commute (u'⁻¹*u) v:= c.spoke _ (show (u'⁻¹*u)∈P.ok 1 from (by simpa only [inv_mul_cancel] using P.plus (P.opp p') p)) _ q -- tune
   conv_lhs => arg 1; rw [show u=u'*(u'⁻¹*u) by group]
   rw [rehome_comp]; unfold rehome; rw [ht.eq];group
lemma chit_left : chit u v=chit u' v:= by unfold chit; rw [show u*v*u⁻¹=u'*v*u'⁻¹ from sameAdj c p p' q]
omit p' in
include q' in
lemma chit_right : chit u v=chit u v':= by
 rw [show chit u v=(chit v u)⁻¹ from (by unfold chit;group), show chit u v'=(chit v' u)⁻¹ from (by unfold chit;group),chit_left c q q' p]
include q'
lemma restate : Commute u v ↔ Commute u' v' := by rw[barter, barter,chit_left c p p' q,chit_right c p' q q']
omit p p' q q'
include h
variable (t s:ℂ)
lemma chit_form (p:u∈P.ok (Head t))(q:v∈P.ok (Head s)) : Commute u v:= by
   let z(n:ℕ):=- (n:ℝ); let g(n):=Tuning (z n)
   have hp(a:ℂ) n: rehome (g n) (Head a)=Head (((Real.exp (z n))^2:ℝ)*a) := by unfold g Tuning; rw [scales,rich_val,ofReal_pow] -- cast may simplify? tune
   have he(a:ℂ): Tendsto (fun n=> rehome (g n) (Head a)) atTop (𝓝 1):= by
      simp_rw [hp]; rw [← Head_one]; apply (cH.continuousAt.tendsto).comp (f:=fun n=> ((Real.exp (z n)^2:ℝ):ℂ)*a) -- tune
      have hx:Tendsto (fun n:ℕ=> Real.exp (z n)^2) atTop (𝓝 0):= by simpa using (Real.tendsto_exp_atBot.comp (show Tendsto z atTop atBot from tendsto_neg_atTop_atBot.comp (show Tendsto (fun x:ℕ=> (x:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop))).pow 2
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hx).mul_const a
   let d:=chit u v; have hx: d∈P.ok 1:= by rw[← (barter _ _).mp (Head_comm t s)]; exact P.plus (P.plus (P.plus p q) (P.opp p)) (P.opp q)
   obtain ⟨U,U0,hU,x,pU⟩:= h.cross 1 (he t); obtain ⟨V,V0,hV,y,pV⟩:= h.cross 1 (he s)
   rw [barter,← show chit U0 V0=1 from (barter _ _).mp (c.spoke U0 x V0 y)]
   let k0:= stackLimit (stackLimit (stackLimit hU hV) (backLimit hU)) (backLimit hV)
   ext1 a; refine tendsto_nhds_unique_of_eventuallyEq (plainLimit atTop d a) (k0 a) ?_
   filter_upwards[pU,pV] with n pU pV; change d a=chit (U n) (V n) a
   obtain ⟨R,hr⟩:=h.always (g n); apply DFunLike.congr_fun
   rw [chit_left c pU (circles hr p) pV,chit_right c (circles hr p) pV (circles hr q)]
   have he: chit (rehome R u) (rehome R v)=rehome R d:=by unfold d chit rehome;group
   rw[he,rehome,(c.spoke _ hx _ hr).symm.eq];group
-- torus via angular rational roots. continuum choose.
omit h in
lemma root_comm (p q:Two)(n:ℕ)(g:q=p^n)(f:u∈P.ok p)(t:v∈P.ok q) : Commute u v:= by
 apply (restate c f f t (show u^n∈P.ok q from g.symm ▸ powerLift f n)).mpr; exact Commute.self_pow ..
private lemma pole_units (p q:ℝ)(f:u∈P.ok (Pole (GUnit p)))(g:v∈P.ok (Pole (GUnit q))) : Commute u v:=by
   have hp:0<2*Real.pi:= by positivity
   let k(n:ℕ):=((n+1):ℕ); let w(n:ℕ):= ((n+1:ℕ):ℝ); let x(n):=(q * w n - p)/(2*Real.pi); let a(n:ℕ):=((⌊x n⌋:ℤ):ℝ); let z(n):= (a n*(2*Real.pi)+p)/w n
   have hw(n:ℕ):0<w n:= by unfold w; positivity
   have he(n):|q-z n| ≤ 2*Real.pi/w n:= by
      have e:a n≤x n:=Int.floor_le _; have t:x n< a n+1:= Int.lt_floor_add_one _; unfold x at e t
      unfold z; rw [abs_le]; have hp₁:= (div_lt_iff₀ hp).mp t; have hp₂:=(le_div_iff₀ hp).mp e
      constructor
      · apply le_trans (neg_nonpos.mpr (by positivity)) (sub_nonneg.mpr ?_); apply (div_le_iff₀ (hw n)).mpr; linarith
      rw [sub_le_iff_le_add, ← add_div,le_div_iff₀ (hw n)]; linarith
   have ht:Tendsto (fun n=>Pole (GUnit (z n))) atTop (𝓝 (Pole (GUnit q))):= by
      apply ((cP.comp G_cont).continuousAt.tendsto).comp (show Tendsto z atTop (𝓝 q) from ?_)
      apply tendsto_iff_dist_tendsto_zero.mpr; refine squeeze_zero' (g:=fun n=> 2*Real.pi/w n) (Eventually.of_forall fun _=>dist_nonneg) (Eventually.of_forall fun n=> (dist_comm (z n) q).trans_le (by rw[Real.dist_eq]; exact he n)) ?_
      exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) -- tune
   have hα (n:ℕ):Pole (GUnit p)= Pole (GUnit (z n))^(k n):= by
      rw [← Pole_nat]; congr 1; apply Units.ext; simp only [Units.val_pow_eq_pow_val,G_val,← Complex.exp_nat_mul];
      have hw0(n): (w n:ℂ)=(k n:ℕ):= rfl
      unfold z; rw [Complex.ofReal_div,← hw0];
      rw [show (w n:ℂ)* (((((a n * (2*Real.pi)+p:ℝ):ℂ)/(w n:ℂ)) * I))= (p:ℂ)*I + ((⌊x n⌋:ℤ):ℂ)*(2* (Real.pi:ℂ)*I) by
          unfold a; have h₀:(w n:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (hw n).ne'; push_cast; field_simp; ring]
      rw [Complex.exp_add, exp_int_mul_two_pi_mul_I,mul_one]
   obtain ⟨G,u0,hG,v0,pG⟩:= h.cross _ ht
   refine (restate c f f g v0).mpr ?_; rw[commute_iff_eq]; ext1 a
   apply tendsto_nhds_unique_of_eventuallyEq (stackLimit (plainLimit _ u) hG a) (stackLimit hG (plainLimit _ u) a)
   exact pG.mono (fun n t=>DFunLike.congr_fun ((root_comm c _ _ _ (hα n) t f).eq.symm) a)
omit c h in
lemma along(v:ℂˣ):∃ a p,v=rich a* GUnit p:= by
    use Real.log ‖(v:ℂ)‖, Complex.arg v; ext1; simp only [Units.val_mul, rich_val,G_val,Real.exp_log (norm_pos_iff.mpr v.ne_zero), norm_mul_exp_arg_mul_I]
-- commuting on full torus
lemma costume (p q:ℂˣ)(u v:W)(hu:u∈P.ok (Pole p))(hv:v∈P.ok (Pole q)) : Commute u v:= by
 obtain ⟨a,r,rfl⟩:=along p; obtain ⟨b,s,rfl⟩:=along q
 rw [← Pole_pow] at hu hv
 obtain ⟨x1,u1⟩:=h.always (Pole (rich a)); obtain ⟨x2,u2⟩:=h.always (Pole (GUnit r)); obtain ⟨y1,v1⟩:=h.always (Pole (rich b)); obtain ⟨y2,v2⟩:= h.always (Pole (GUnit s))
 exact (restate c hu (P.plus u1 u2) hv (P.plus v1 v2)).mpr (((c.pole a (rich b) x1 y1 u1 v1).mul_right (c.pole a (GUnit s) x1 y2 u1 v2)).mul_left ((c.pole b (GUnit r) y1 x2 v1 u2).symm.mul_right (pole_units c h r s u2 v2)))
omit h in lemma reverseLock (p:u∈P.ok g1){x:Two}(t:x∈ Wrap g1): u ∈ P.ok x:= by
 rcases wrap_case _ t with e|e; exact e ▸ p
 rw [e]; simpa only [one_mul] using P.plus c.pinBack p
end YM.Marque.Passage
