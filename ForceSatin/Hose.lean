import YM.SU5.FiniteGaugeData.Indigo.Sweat
import YM.SU5.Thin.Avalanche.Shelter
-- dimension independent. use all powers. Wick price recursion.
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Regis.Resonance.Lull
open Function Filter Metric MeasureTheory ProbabilityTheory NormedSpace InnerProductSpace Finset
open scoped Topology BigOperators InnerProductSpace ENNReal NNReal Classical ContDiff
open SU5.FiniteGaugeData.Indigo.Sweat
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable (k:ℕ) {p M:ℝ} {n m:ℕ}
local notation "μ"=> stdGaussian E
local notation "ℭ"=> Valued μ
-- with mathlib bump functions
noncomputable abbrev scarf : ContDiffBump (0:ℝ):=⟨1,2,zero_lt_one,one_lt_two⟩
noncomputable abbrev scarfLens (u x:ℝ):=scarf (x/u)*x
lemma velvetBound (u x:ℝ)(h:0<u): |scarfLens u x| ≤ |x| ∧ |scarfLens u x| ≤ 2*u ∧ (|x|≤u→scarfLens u x=x):=by
 have e:dist (x/u) 0=|x|/u:= by simp [abs_of_pos h]
 have z:|scarfLens u x|≤ |x|:= by unfold scarfLens; rw [abs_mul,abs_of_nonneg (ContDiffBump.nonneg _)]; exact mul_le_of_le_one_left (abs_nonneg _) scarf.le_one
 refine ⟨z,?_,fun k=>?_⟩
 · rcases le_total |x| (2*u) with s|s; exact z.trans s
   unfold scarfLens; rw [scarf.zero_of_le_dist (show (2:ℝ)≤_ from ((le_div_iff₀ h).2 s).trans_eq e.symm),zero_mul]; simp; positivity
 unfold scarfLens; rw [scarf.one_of_mem_closedBall (Metric.mem_closedBall.mpr (_ : dist (x/u) 0≤1)),one_mul]; exact e.trans_le ((div_le_one h).2 k)
lemma scarfDiff (u): ContDiff ℝ 1 (scarfLens u) := ((scarf.contDiff).comp (contDiff_id.div_const u)).mul contDiff_id
lemma template : ∃ C:ℝ≥0,LipschitzWith C (scarfLens 1):=by
 apply (scarfDiff 1).lipschitzWith_of_hasCompactSupport _ (by norm_num) -- test
 apply HasCompactSupport.intro (isCompact_closedBall 0 (2:ℝ)); intro i v
 unfold scarfLens; rw [div_one,scarf.zero_of_le_dist (le_of_not_ge (show ¬dist i 0≤2 from v)), zero_mul]
def loan:ℝ≥0:= template.choose
lemma hose_lp (u x y:ℝ)(h:0<u):|scarfLens u x-scarfLens u y| ≤ loan*|x-y|:=by
 have e(x):scarfLens u x=u*scarfLens 1 (x/u):=by unfold scarfLens; rw [div_one]; field_simp
 rw [e,e,←mul_sub,abs_mul,abs_of_pos h,← Real.dist_eq]
 refine (mul_le_mul_of_nonneg_left (template.choose_spec.dist_le_mul _ _) h.le).trans_eq ?_
 rw [Real.dist_eq,←sub_div, abs_div,abs_of_pos h]; unfold loan; field_simp
-- cutoff in product with exact comparison on diagonal full set. ℓ support calculus uses contour
abbrev PBound (B:ℝ) (p:ℕ) := B^p * teatime p
-- payoff price of length ≤m. Integrability & tail.
variable (J:Type*) [DecidableEq J]
-- general list products in supports. allow settings K→ι.
section
variable {F:Type*}[NormedField F] (g h:J→F)
 {η:ℝ} (V:List J)
local notation "I(h)"=>(V.map h).prod
variable {J}
lemma low (u:0≤M)(p:∀ i∈V, ‖g i‖≤M): ‖(V.map g).prod‖≤M^V.length:=by induction V with| nil=>simp| cons i V ih=> simp only [List.map_cons,List.prod_cons,norm_mul,List.length_cons,pow_succ']; exact mul_le_mul (p i List.mem_cons_self) (ih (fun i a=> p i (List.mem_cons_of_mem _ a))) (norm_nonneg _) u
lemma compareAt (a:1≤M)(u:0≤η)(p:∀ i∈V,‖g i‖≤M) (q:∀ i∈V,‖h i‖≤M)(e:∀ i∈V,‖g i-h i‖≤η): ‖(V.map g).prod-(V.map h).prod‖≤ (V.length:ℝ)*M^V.length*η:=by
 induction V with
 | nil=>simp
 | cons i V ih=>
   let x:=(V.map g).prod; let y:=(V.map h).prod; let d:ℝ:=V.length
   have hp : ‖x-y‖ ≤ d*M^V.length*η:= ih (fun i a=>p i (List.mem_cons_of_mem _ a)) (fun i a=>q i (List.mem_cons_of_mem _ a)) (fun i a=>e i (List.mem_cons_of_mem _ a)); have w:(0:ℝ)≤M:=zero_le_one.trans a
   have ht: ‖y‖≤M^V.length:=low h V w (fun i a=>q i (List.mem_cons_of_mem _ a))
   simp only [List.length_cons,List.map_cons,List.prod_cons,Nat.cast_add,Nat.cast_one,pow_succ']; change ‖g i*x-h i*y‖ ≤ (d+1)*(M*M^V.length)*η
   rw [show g i*x-h i*y=g i*(x-y)+(g i-h i)*y from (by ring)]; apply (norm_add_le ..).trans; simp_rw [norm_mul]; have he:= add_le_add (mul_le_mul (p i List.mem_cons_self) hp (norm_nonneg _) w) (mul_le_mul (e i List.mem_cons_self) ht (norm_nonneg _) u); refine he.trans ?_; have hu:M^V.length*η≤ M*(M^V.length*η):= le_mul_of_one_le_left (mul_nonneg (pow_nonneg w _) u) a; linarith only [hu]
end
variable {J}
lemma earning (L:List E)(x:E): payday L x=(L.map (fun i=> spanX i x)).prod:=by induction L with| nil=>rfl| cons i L ih=>change spanX i x*payday L x=spanX i x*_; rw[ih]; rfl
variable (L:Finset J)(f:J→E) (u:0≤p) (v:∀ i∈L,‖f i‖≤p)
local notation "A"=> f '' (L:Set J)
local notation "𝒴"=> ((L.card:ℝ)* PBound p k)
def trellis (k:ℕ) (V:List J) (f:J→E) (x:E):=∑ i∈V.toFinset, |inner ℝ (f i) x|^k
lemma flower (k:ℕ)(V:List J): Valued μ (trellis k V f):=by rw [show trellis k V f=∑ i∈V.toFinset, fun x=> |inner ℝ (f i) x|^k from funext (fun v=>by simp [trellis,Finset.sum_apply])]; exact Valued.finMore V.toFinset (fun i x=>|inner ℝ (f i) x|^k) (fun i=> Valued.upward (f:=fun x=> |inner ℝ (f i) x|) ⟨fun q=> ((fromV (f i)).charge q).norm⟩ k) 
variable (W:List J)
include u
omit v in
lemma earn (b:∀ i∈W, ‖f i‖ ≤ p)(x:W.length≤ m): (∫ v,trellis k W f v∂μ) ≤ ↑m*PBound p k:=by
 unfold trellis; rw [integral_finsetSum _ (fun i _=>peg_b ..)]; simp_rw [pli]; exact (sum_le_sum (g:=fun _=>PBound p k) fun i v=> mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (b i (List.mem_toFinset.mp v)) _) (L0 _)).trans ((by simp : (∑ _i ∈ W.toFinset,PBound p k)=(W.toFinset.card:ℝ)*PBound p k).le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (W.toFinset_card_le.trans x)) (mul_nonneg (pow_nonneg u _) (L0 _))))
omit u v
noncomputable def scarfView (W:List J)(f:J→E)(p:ℝ)(x:E):ℝ := (W.map (fun i=>scarfLens p (inner ℝ (f i) x))).prod
lemma scarf_smooth (p:ℝ): ContDiff ℝ 1 (scarfView W f p):=by induction W with| nil=>exact contDiff_const| cons j W ih=> exact ((scarfDiff p).comp (innerSL ℝ (f j)).contDiff).mul ih
lemma innerU (x:E):payday (W.map f) x=(W.map fun i=> inner ℝ (f i) x).prod:=by rw [earning,List.map_map]; rfl
lemma innerV (x:E) (h:1≤M)(b:∀ i∈W, |inner ℝ (f i) x| ≤ M): |payday (W.map f) x| ≤ M^W.length:=by rw [innerU,←Real.norm_eq_abs]; exact low _ _ (zero_le_one.trans h) b
lemma scarfComfort (t:ℝ)(h:1≤t)(x:E)(m:W.length≤n): |scarfView W f t x| ≤ (2*t)^n:= ((low (fun i=>scarfLens t (inner ℝ (f i) x)) W (mul_nonneg (by norm_num) (zero_le_one.trans h)) (fun i _=>(velvetBound _ _ (zero_lt_one.trans_le h)).2.1))).trans (pow_le_pow_right₀ (by linarith only [h]) m)
variable (u':1 ≤ M)(a:M≤p)
lemma innerT (x:E)(m':W.length ≤ m): |payday (W.map f) x| ≤ 1+ trellis m W f x:=by
 by_cases h:∀ i∈W,|inner ℝ (f i) x|≤ 1; exact (innerV f W x (M:=1) le_rfl h).trans (by simp; apply Finset.sum_nonneg fun i _=> by positivity)
 push Not at h; obtain ⟨i,hi,v⟩:=h
 let g(j):= |inner ℝ (f j) x|; let V:=W.toFinset; let y:= List.mem_toFinset.mpr hi; obtain ⟨b,f',p⟩:= exists_max_image V g ⟨i,y⟩; let d:=g b; have hp:1 ≤ d:=v.le.trans (p i y)
 exact (innerV f W x hp (fun i a=>p i (List.mem_toFinset.mpr a))).trans ((pow_le_pow_right₀ hp m').trans ((single_le_sum (f:=fun i=> (g i)^m) (fun i _=> by unfold g; positivity) f').trans (le_add_of_nonneg_left zero_le_one)))
include u
omit v in
lemma innerPrice (w:∀ i∈W, ‖f i‖ ≤ p) (m':W.length ≤ m): |memo (W.map f)|≤ 1+ ↑m * PBound p m:=by
 rw [←Real.norm_eq_abs]; refine (norm_integral_le_of_norm_le ((integrable_const (1:ℝ)).add (flower f m W).accepted) (f:=payday (W.map f)) (Eventually.of_forall fun x=>innerT f W x m')).trans ?_; rw [show (∫ x, (_+trellis m W f) x∂μ) = 1+∫ x, trellis m W f x∂μ from ?_] -- tweak
 exacts [add_le_add le_rfl (earn m f u W w m'), (by rw [show _+trellis m W f=(fun x:E=>1+ trellis m W f x) from rfl, integral_add (integrable_const _) (flower f m W).accepted]; simp)]
omit u v
lemma tremble (h:1≤M)(x:E)(m':W.length ≤ m): |payday (W.map f) x- scarfView W f M x| ≤ (M^k)⁻¹ * (2 * trellis (m+k) W f x):=by
 let g(j):= inner ℝ (f j) x; let h':=zero_lt_one.trans_le h; by_cases e:∀ i∈W, |g i|≤M
 · have he: scarfView W f M x=payday (W.map f) x:=by rw [innerU]; apply congrArg List.prod; apply List.map_congr_left; exact fun i a=>(velvetBound M (g i) h').2.2 (e i a)
   rw [he,sub_self,abs_zero]; unfold trellis; positivity
 push Not at e; obtain ⟨i,hi,e⟩:=e
 let V:= W.toFinset; let r(j):=|g j|; let y:=List.mem_toFinset.mpr hi; obtain ⟨b,f',p⟩:= exists_max_image V r ⟨_,y⟩; let S:=r b; have hs:M ≤ S:=e.le.trans (p i y); have hz:=h.trans hs
 have h0(i)(a:i∈W): |g i|≤ S:=p i (List.mem_toFinset.mpr a); have hv:=pow_le_pow_right₀ hz m'; have hp: |payday (W.map f) x|≤S^m:=(innerV f W x hz h0).trans hv; have hw:|scarfView W f M x| ≤ S^m:= (low (fun i=>scarfLens M (g i)) W (zero_le_one.trans hz) (fun i a=>(velvetBound M _ h').1.trans (h0 i a))).trans hv
 refine (abs_sub _ _).trans ((add_le_add hp hw).trans ?_); have hu:S^(m+k) ≤ trellis (m+k) W f x:= single_le_sum (f:=fun i=> (r i)^(m+k)) (fun i _=>pow_nonneg (abs_nonneg _) _) f'; apply (le_inv_mul_iff₀ (by positivity : 0<M^k)).mpr; rw [pow_add] at hu; nlinarith only [hu,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h'.le hs k) (pow_nonneg (zero_le_one.trans hz) m)]
lemma scarf_val (h:1≤M): Valued μ (scarfView W f M):= ⟨fun i=> MemLp.of_bound (scarf_smooth f W M|>.continuous.aestronglyMeasurable) ((2*M)^W.length) (Eventually.of_forall fun x=> scarfComfort f W M h x le_rfl)⟩
include u
omit v in
lemma fare (w:∀ i∈W, ‖f i‖ ≤ p) (a:M≥1)(m':W.length ≤ m): |memo (W.map f) - ∫ i,scarfView W f M i∂μ| ≤ (M^k)⁻¹ * (2*(↑m* PBound p (m+k))):=by
 unfold memo; rw [←integral_sub (payday_val _|>.accepted) (scarf_val _ _ a|>.accepted),←Real.norm_eq_abs]; have h:=zero_lt_one.trans_le a
 refine (norm_integral_le_of_norm_le (g:=fun x=>(M^k)⁻¹*(2*trellis (m+k) W f x)) (((flower f (m+k) W).accepted.const_mul _).const_mul _) (Eventually.of_forall fun x=> tremble k f W a x m')).trans ?_; rw [integral_const_mul,integral_const_mul]; gcongr; exact earn (m+k) f u W w m'
omit u
abbrev pairP (f:J→E)(i j:J):= inner ℝ (f i) (f j)
-- Gaussian power-scripts. separate from odd Wick.
section
variable (g:J→J→ℝ)
def candle (b:J)(F: List J→ℝ)(Z V:List J) :ℝ:= match V with| []=> 0| i::V=> g b i * F (Z++V) + candle b F (Z++[i]) V
-- `g` parameter? recursion needs pass explicitly?
def candles (k:ℕ)(V:List J):ℝ:= match V with
 | []=>1
 | i::L => match k with| 0=> 0| k+1=>candle g i (candles k) [] L
termination_by k
lemma stirs {f:J→E}(V Z:List J)(b:J)(F:List J→ℝ) (u:∀ i j,g i j=inner ℝ (f i) (f j))(w:∀ L:List J,L.length < V.length+Z.length → F L=memo (L.map f)):
    candle g b F Z V= roster (f b) (Z.map f) (V.map f):=by induction V generalizing Z with
 | nil=>rfl
 | cons i V ih=>
    rw [List.map_cons,candle,roster,w (Z++V) (by simp; omega),ih (Z++[i]) (fun t p'=>w t (by simp at p' ⊢; omega)), List.map_append,List.map_append,List.map_singleton,u]
lemma shining {f:J→E} (z:∀ i j,g i j=inner ℝ (f i) (f j))(h:W.length ≤ k): candles g k W=memo (W.map f):=by induction k generalizing W with
 | zero => cases W <;> simp at * ; unfold memo; rw [candles]; simp [payday] -- maybe `simp at *` problem
 | succ k ih=> cases W with
   | nil=> rw [candles]; simp [memo,payday]
   | cons i W=>
    rw [candles, List.map_cons,gramStein] -- change roster from []
    exact stirs g W [] i _ z (fun L p=> ih L (by simp only [List.length_cons,Nat.add_le_add_iff_right] at h; simp only [List.length_nil,add_zero] at p; omega))
abbrev priceW (g:J→J→ℝ)(V:List J):ℝ:= candles g V.length V
variable {α:Type*} (f':Filter α)(K:α→J→J→ℝ)(p0:∀ i j,Tendsto (fun x=>K x i j) f' (𝓝 (g i j)))
include p0
lemma tending (k:ℕ)(V:List J): Tendsto (fun i=> candles (K i) k V) f' (𝓝 (candles g k V)):=by induction k generalizing V with
 | zero=>cases V <;> simp_rw [candles] <;> exact tendsto_const_nhds
 | succ k ih=>cases V with
   | nil=> simp_rw [candles]; exact tendsto_const_nhds
   | cons j V=> simp_rw [candles]; have he(L P:List J): Tendsto (fun i=> candle (K i) j (candles (K i) k) L P) f' (𝓝 (candle g j (candles g k) L P)):= by
                  induction P generalizing L with| nil=>exact tendsto_const_nhds| cons i V e=> exact ((p0 j i).mul (ih _)).add (e _)
                exact he [] V
end
#print axioms shining
#print axioms fare
#print axioms innerPrice
#print axioms hose_lp
#print axioms compareAt
end YM.Regis.Resonance.Lull
