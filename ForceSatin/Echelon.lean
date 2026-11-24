import ForceSatin.Filament
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
local notation "π" => Real.pi
-- Gem registration arbitrary family, even-angle grids
structure Lyra (ι:Type*) where
 N : ι→Side
 S(i:ι):Offset (N i)
 even(i:ι):Even (N i).val
namespace Lyra
variable {ι:Type*}(T:Lyra ι)
abbrev steps(i:ι)(s:Site (T.N i)):=glen (T.S i) s
structure Herb (T:Lyra ι) where
 era:ι
 site:Site (T.N era)
 fresh: 0<‖T.steps era site‖
namespace Herb
variable {T}(a:T.Herb)
abbrev go:= T.steps a.era a.site
lemma cap : ‖a.go‖≤ π:= orb _ _ (T.even a.era)
end Herb
abbrev Hint : Ember.Tax T.Herb :=⟨fun i=> ‖i.go‖,π,fun i=>i.fresh,fun i=>i.cap⟩
abbrev amber(T:Lyra ι)(x:Axis)(u:T.Herb)(z:ℂ):Momentum:= tmap u.go+spark x (raf T.Hint u z)
lemma amethyst (x:Axis):Move T.Hint (T.amber x):= Move.add (go_b _ (fun _=>rfl) (fun i=>i.cap)) (sparkBud _ (raft ..) x) (fun i=> by simp [raf,spark])
lemma thread (u:T.Herb)(x:Axis)(v:ℝ):T.amber x u v=tmap (u.go+beam x (v*‖u.go‖)):=by funext i; by_cases h:i=x <;> simp [amber,spark,tmap,raf,beam,Lattice.step,h] <;> ring
variable (V:ι→Momentum→ℂ) (G:Momentum→ℂ) (m:ℕ)
-- payment on arbitrary orientation at angle. latticeFieldEstimates: periodic within cone.Spin. need no z not near. 
structure Singer(T:Lyra ι)(m:ℕ)(V:ι→Momentum→ℂ)(G:Momentum→ℂ) :Prop where
 Act(x:Axis): Act T.Hint ((m:ℤ)-1) (fun i z=>V i.era (T.amber x i z))
 bill(x:Axis): Ember.Act T.Hint (m:ℤ) (fun i z=> V i.era (T.amber x i z)-G (T.amber x i z))
 rate(x:Bin) : x≠0 → ContDiffAt ℝ ∞ (G ∘ tmap) x
 summit(i:ι): V i 0=G 0
 peers(x y:Bin)(i:ι): Jill.peers x y → tmap x∈realCube zone → tmap y∈realCube zone→ V i (tmap x)= V i (tmap y)
abbrev mango (G:Momentum→ℂ)(x:Bin):ℂ:=(fog x:ℂ)*G (tmap x)
abbrev mistC (i:ι)(w: Site (T.N i)):ℂ:= V i (tmap (T.steps i w))-mango G (T.steps i w)
variable {T V G m} (S:Singer T m V G)
section Cap
include S
lemma mossCap : ∃ C:ℝ, 0<C ∧ ∀ i j, ‖T.mistC V G i j‖ ≤ C*‖T.steps i j‖^m:=by
 obtain ⟨u,v,c,d,p⟩:= S.Act 0; obtain ⟨e,f,g,h,Q⟩:= S.bill 0
 let C:= f+ (4 / Real.pi)*v
 have hP:=Real.pi_pos
 refine ⟨C,by unfold C; positivity,fun i k=>?_⟩
 let x:= T.steps i k; let r:= ‖x‖; let V':=V i (tmap x); let G':=G (tmap x)
 change ‖V'-(fog x:ℂ)*G'‖≤C*r^m
 by_cases a:x=0
 · rw [show V'=V i 0 from (by unfold V'; rw [a]; rfl),show G'=G 0 from (by unfold G'; rw [a]; rfl),S.summit,show fog x=1 from fog_s _ (by rw [a,norm_zero]; positivity)]; simp only [Complex.ofReal_one,one_mul,sub_self,norm_zero]; unfold C r; positivity
 let F:T.Herb:= ⟨i,k,norm_pos_iff.mpr a⟩; have hr:0<r:= F.fresh
 have hx:T.amber 0 F 0=tmap x:=by rw [←Complex.ofReal_zero, thread]; simp [x,F]
 have he:= (Q F 0 (by simpa)).2; simp only [hx] at he; change ‖V'-G'‖≤ f*r^(m:ℤ) at he; rw [zpow_natCast] at he
 by_cases w:r≤ Real.pi/4
 · rw [fog_s x w,Complex.ofReal_one,one_mul]; exact he.trans (by unfold C; gcongr; have ht: 0≤4/Real.pi *v:=(by positivity); linarith)
 have ht:= (p F 0 (by simpa)).2; simp only [hx] at ht; change ‖V'‖≤ v*r^((m:ℤ)-1) at ht; rw [zpow_sub₀ hr.ne',zpow_natCast,zpow_one] at ht
 let y:= fog x; have h₁:0≤y:= ContDiffBump.nonneg fog; have h₂:y≤1:= ContDiffBump.le_one fog
 rw [show V'-(fog x:ℂ)*G'= ((y:ℂ)*(V'-G'))+(↑(1-y):ℂ)*V' from (by push_cast; unfold y; ring)]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg h₁,Real.norm_of_nonneg (by linarith : 0≤1-y),show C=f+4/π*v from rfl,add_mul]; refine add_le_add ((mul_le_of_le_one_left (norm_nonneg _) h₂).trans he) ((mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans (ht.trans ?_)); apply (show v*(r^m/r) ≤ v*(r^m/(π/4)) by gcongr; linarith).trans_eq; field_simp
end Cap
section geometry
-- use small steps, ensure not rolled through 0. clearance measured from true torus.
variable (k:ℕ)
abbrev ticketϕ (k:ℕ):= min (π/32) (zone/2)/(k+1:ℕ)/π
lemma tint_p:0<ticketϕ k:=by unfold ticketϕ; have h:=Real.pi_pos; have hp:=zone_pos; exact div_pos (div_pos (lt_min (by positivity) (half_pos hp)) (by positivity)) h
private lemma withinSteps (u: T.Herb)(a:Axis)(v j:ℤ)(p:|(j:ℝ)|≤k)(hv:|extent (T.N u.era) v| < ticketϕ k * ‖u.go‖): |(j:ℝ)*extent (T.N u.era) v| ≤ min (π/32) (zone/2) :=by
 rw [abs_mul]; apply (mul_le_mul p (hv.le.trans (mul_le_mul_of_nonneg_left u.cap ((tint_p k).le))) (abs_nonneg _) (by positivity)).trans; apply le_trans (b:=((k+1:ℕ):ℝ)*(ticketϕ k*π)) ?_ (le_of_eq ?_)
 · gcongr; positivity [tint_p k, Real.pi_pos]; omega -- tune tint positivity
 unfold ticketϕ; have he:=Real.pi_pos; push_cast; field_simp
lemma tiptoe (u:T.Herb)(a:Axis)(j v:ℤ)(p:|(j:ℝ)|≤k)(hv:|extent (T.N u.era) v| < ticketϕ k*‖u.go‖):
 let X:= u.go+beam a ((j:ℝ)*extent (T.N u.era) v); let Y:= T.steps u.era (u.site+ march (T.N u.era) a (j*v))
 tmap X∈realCube zone ∧ tmap Y∈realCube zone ∧ peers X Y ∧ ((X≠Y)→π/2≤‖X‖∧π/2≤‖Y‖) ∧ |‖X‖-‖u.go‖|≤π/32 ∧ |‖Y‖-‖u.go‖|≤π/32:=by
 intro X Y; let f:= extent (T.N u.era) v; let g:= (j:ℝ)*f; let m:=min (π/32) (zone/2); let r:= ‖u.go‖
 have hp: |g|≤m := withinSteps k u a v j p hv; have hK:m ≤ π/32:= min_le_left ..; have hz:m≤zone/2:=min_le_right ..
 have he:Bound π Y:= orb _ _ (T.even _)
 have hh: peers X Y:= by unfold X Y; rw [← march_t]; exact march_a ..
 have ht : ‖X-u.go‖≤m:= by unfold X; rw [add_sub_cancel_left]; exact (beam_cost ..).trans hp
 have hV: |‖X‖-r|≤ m:=(abs_norm_sub_norm_le ..).trans ht; have hv': ‖X‖≤π+m:=by linarith only [show ‖X‖-r≤ m from (abs_le.mp hV).2,(show r≤π from u.cap)]; -- tune semicolon
 have hY: |r-‖Y‖|≤m:= within_d (T.even _) u.site a (j*v) _ (by rw [march_t]; exact hp)
 refine ⟨⟨tmap_physical _,fun j=>?_⟩,base_subset_realCube zone_pos (b_base he),hh,fun h=> ?_,hV.trans hK, (abs_sub_comm r ‖Y‖) ▸ hY.trans hK⟩
 · change |((X j:ℂ).re)| < _; rw [Complex.ofReal_re]; exact lt_of_le_of_lt ((b_abs X j).trans hv') (by linarith only [hz,zone_pos])
 have he':= not_lt.mp (mt (fun z=> peerBond z hh) h); unfold Bound at he; constructor <;> linarith only [Real.pi_pos,he,hK,he',hv']
lemma call (T:Lyra ι)(u:T.Herb)(a:Axis)(v:ℝ)(j:ℤ): T.amber a u ((j:ℂ)*(↑(v/‖u.go‖):ℂ))= tmap (u.go+beam a ((j:ℝ)*v)):=by
 have hx:=u.fresh; rw [←Complex.ofReal_intCast, ←Complex.ofReal_mul, thread]; congr 2; field_simp
lemma glenning (u:T.Herb) (F : Site (T.N u.era)→ℂ)(Y:ℤ→ℂ)(a:Axis)(v:ℤ)(p:0<k)(e:∀ i:ℤ,|(i:ℝ)|≤k→ F (u.site+march (T.N u.era) a (i*v))=Y i) : brink k F a v u.site=Y (-1)-∑ i∈range k,debtM k i*Y i:=by
 unfold brink; congr 1
 · simpa using e (-1) (by simp only [Int.cast_neg,Int.cast_one,abs_neg,abs_one]; exact_mod_cast p)
 apply sum_congr rfl; intro i h; rw [e i (by simp only [Int.cast_natCast,abs_of_nonneg (by positivity : 0≤ (i:ℝ))]; exact_mod_cast (mem_range.mp h).le)]
end geometry
include S
lemma amplitude (a:Axis): ∃ b C:ℝ,0 < b ∧ 0<C ∧ ∀ (U:T.Herb)(v:ℤ), let x:= extent (T.N U.era) v; let r:= ‖U.go‖; |x| < b*r → ‖brink (m+6) (T.mistC V G U.era) a v U.site‖ ≤ C*r^m * (|x|/r)^(m+6):=by
 let hF:= offFog (mango G); let n:= m+6; have h:0<n:=by unfold n; omega
 obtain ⟨u,v,c,d,P⟩:= Jill.plunge (S.Act a) n h; obtain ⟨e,f,g,t,Q⟩:= Jill.plunge (S.bill a) n h
 have ht(x:Bin)(p:x≠0):ContDiffAt ℝ ∞ (mango G) x:= ((Complex.ofRealCLM.contDiff.comp fog_c).contDiffAt).mul (S.rate x p) -- tune syntax
 obtain ⟨y,hV,Z⟩:= verdant n h hF (offDiff _ ht) a; let W:=max f (v*8/Real.pi + y*Real.pi^6); let b:= min u (min e (ticketϕ n)); have hb:0<b:=lt_min c (lt_min g (tint_p n)); have hq:= Real.pi_pos
 refine ⟨b,W,hb,lt_max_of_lt_left t,?_⟩; intro i j x r hx
 have hr:0<r:=i.fresh; have hp := (abs_div x r); rw [abs_of_pos hr] at hp
 let R:= T.amber a i; let m':=x/r; let F:= T.steps i.era
 let χ(j':ℤ):=(j':ℂ)*(m':ℂ)
 have hm : ‖(m':ℂ)‖ = |x|/r:= (Complex.norm_real ..).trans hp
 have he : |x|/r < b:= (div_lt_iff₀ hr).mpr hx; have hX: |x| < ticketϕ n*r:= hx.trans_le (mul_le_mul_of_nonneg_right ((min_le_right ..).trans (min_le_right ..)) hr.le)
 rcases le_total r (π/8) with h'|h'
 · let moss(p:ℂ):= V i.era (R p)- G (R p)
   have hz(k:ℤ)(p:|(k:ℝ)|≤n): T.mistC V G i.era (i.site+march (T.N i.era) a (k*j)) = moss (χ k):=by
      let v:= F (i.site+march (T.N i.era) a (k*j)); obtain ⟨hx,hu,hv,w,u',v'⟩:= tiptoe n i a k j p hX; have hk:= v'; change |‖v‖-r|≤ π/32 at hk; have hg:‖v‖≤π/4:=by linarith only [show ‖v‖-r ≤ π/32 from (abs_le.mp hk).2,hq,h']
      have hs: R (χ k)=tmap v:=by unfold R χ m' r; rw [call]; congr 1; apply Classical.byContradiction (fun e=>(by have hh:= (w e).2; change π/2 ≤ ‖v‖ at hh; linarith))
      change _-mango G v=_; unfold moss mango; rw [fog_s v hg,Complex.ofReal_one,one_mul,hs]
   have hw:= Q i (-1) (by norm_num) (m':ℂ) (hm.trans_lt (he.trans_le ((min_le_right ..).trans (min_le_left ..)))); change ‖moss _-∑ j∈range n, debtM n j *moss _‖ ≤ f * _*_ at hw; simp only [Complex.ofReal_neg,Complex.ofReal_one,hm,zpow_natCast] at hw; rw [glenning n i _ (moss ∘ χ) a j h hz]; simp only [Function.comp_apply,χ,Int.cast_neg,Int.cast_one, Int.cast_natCast]; exact hw.trans (by gcongr; exact le_max_left ..)
 let pre:=fun k:ℤ=>V i.era (R (χ k)); let post(k:ℤ):= hF (i.go+beam a ((k:ℝ)*x)); let N:=T.N i.era
 have hz(k:ℤ)(p:|(k:ℝ)|≤n): T.mistC V G i.era (i.site+march N a (k*j))=pre k-post k:=by
    obtain ⟨he,hh,hE,hF₀,hg,hK⟩:= tiptoe n i a k j p hX; let y:= i.go+beam a ((k:ℝ)*x); let z:=F (i.site+march N a (k*j))
    unfold mistC pre post; congr 1
    · unfold R χ m' r; rw [call]; exact (S.peers _ _ i.era hE he hh).symm
    change mango G z=offFog (mango G) y; rw [offClear]; by_cases hx:y=z; · rw [hx]
    · obtain ⟨hv,hj⟩:= hF₀ hx; unfold mango; rw [fog_far y hv,fog_far z hj]; simp
    have hL:= (abs_le.mp hg).1; change _ ≤ ‖y‖-r at hL; linarith only [hL,hq,h']
 change ‖brink n _ _ _ _‖≤_; rw [glenning n i _ (fun k=> pre k-post k) a j h hz, sum_congr (g:=fun k=> debtM n k*pre k-debtM n k*post k) rfl (fun i h=>by ring), sum_sub_distrib,sub_sub_sub_comm]; apply (norm_sub_le ..).trans; apply (add_le_add (show ‖pre (-1)-_‖≤ v*(r^m/r)*(|x|/r)^n from ?_) (show ‖post (-1)-_‖≤ y*|x|^n from ?_)).trans
 · apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show v*8/π+y*π^6≤W from le_max_right ..) (pow_nonneg hr.le _)) (show 0 ≤ (|x|/r)^n by positivity))
   rw [add_mul (v*8/π),add_mul]; apply add_le_add
   · apply mul_le_mul_of_nonneg_right _ (by positivity); refine (mul_le_mul_of_nonneg_left (show r^m/r ≤ r^m/(π/8) by gcongr) d.le).trans_eq ?_; field_simp
   let W:= (|x|/r); rw [show y*|x|^n= y*r^n*W^n from (by unfold W; rw [div_pow]; field_simp)]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold n; rw [pow_add]; apply le_trans _ (le_of_eq (a:=y*(r^m*π^6)) (by ring)); gcongr; exact i.cap
 · have hh:= P i (-1) (by norm_num) (m':ℂ) (hm.trans_lt (he.trans_le (min_le_left ..))); unfold pre χ; simp only [Complex.ofReal_neg,Complex.ofReal_one,hm,zpow_sub₀ (show T.Hint.r i≠0 from hr.ne'),zpow_natCast,zpow_one, smul_eq_mul, Int.cast_neg,Int.cast_one, Int.cast_natCast] at *; exact hh
 let l:= T.steps i.era; have hk:= withinSteps n i a j 1 (by simp only [Int.cast_one,abs_one]; exact_mod_cast h) hX
 unfold post; rw [Int.cast_neg,Int.cast_one,neg_one_mul]; simp_rw [Int.cast_natCast]; exact Z i.go (by linarith [i.cap]) x (by have hp : |x| ≤ π/32:= le_trans (by simpa using hk) (min_le_left ..); linarith)

lemma ratioPromise :∃ b C:ℝ,0<b∧0<C∧∀ i:ι,Aria (T.N i) (T.S i) (T.mistC V G i) m b C:=by
 choose c d p u P using amplitude S; obtain ⟨f,h,hf⟩:= mossCap S
 obtain ⟨x,e,k⟩:= exists_min_image univ c univ_nonempty; let C:= f+ ∑ i,d i; refine ⟨c x,C,p _,by unfold C; linarith [sum_nonneg (s:=univ) (f:=d) (fun i _=>(u i).le)],fun i=> ⟨T.even i,fun j=>(hf i j).trans ?_,fun a v j t=>?_⟩⟩
 · refine mul_le_mul_of_nonneg_right ?_ (by positivity); exact le_add_of_nonneg_right (sum_nonneg fun i _=>(u i).le)
 let r:= ‖T.steps i j‖; have hr:0<r := pos_of_mul_pos_right (lt_of_le_of_lt (abs_nonneg _) (show _< c x*r from t)) ((p x).le) -- tune
 let X:T.Herb:= ⟨i,j,hr⟩; let b:=extent (T.N i) v
 have hp:= P a X v (show |b|< c a*r from t.trans_le (mul_le_mul_of_nonneg_right (k a (mem_univ a)) hr.le)); exact hp.trans (by change d a*r^m* (|b|/r)^(m+6)≤C*r^m*(|b|/r)^(m+6); gcongr; exact (single_le_sum (s:=univ) (fun i _=>(u i).le) (mem_univ a)).trans (le_add_of_nonneg_left h.le))
lemma perchLines :∃ C:ℝ,0<C∧ ∀ z:Cover,z≠0 → ∀ N:ℕ→Side,Tendsto (fun i=>(N i).val) atTop atTop→ ∀ᶠ j:ℕ in atTop, ∀ i:ι, T.N i=N j → ‖skyPrice (T.S i) (T.mistC V G i) z‖ ≤ C/(rally z)^(4+m):=by
 obtain ⟨b,C,hc,u,Q⟩:= ratioPromise S; obtain ⟨A,e,U⟩:= radiant m hc u; refine ⟨A,e,fun z v N d=>?_⟩; filter_upwards [U z v N d] with n p; intro i hh; rw [← hh] at p; exact p _ _ (Q _)
end Lyra
#print axioms Lyra.perchLines
end YM.Regis.Circuit.SpringDay
