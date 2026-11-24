import YM.SU5.Relativistic.Minot
/-! # finite translations and continuable *symbol seed* rigidity. Does not use continuation of theory. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free Asymptotics
open Laurent Bloch Fir Jill Ember Shore UnitAddTorus
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
-- Finite escape.
private def Vecs:=Cover -- remove
private def windH (i:Cover):Bin:=fun j=> (i j:ℝ)
private lemma windH_add (i j:Cover):windH (i+j)=windH i+windH j:=by unfold windH; ext; simp
@[simp] private lemma windH_zero: windH 0=0:=by unfold windH; ext; simp
private lemma cuteds (i : Axis)(n n':Cover)(h:n i=n' i)(x:ℝ):mode (tmap (x • windH (step i))) (-n) = mode (tmap (x • windH (step i))) (-n'):=by
 have hw(n:Cover): mode (tmap (x • windH (step i))) (-n)= Complex.exp (-(I*↑x*(n i:ℂ))):=by
    unfold mode; rw [Finset.sum_eq_single i]; congr 1; simp [tmap,windH,Pi.smul_apply]; ring -- tune
    · intro j _ k; simp [k,windH,tmap]
    simp
 rw [hw, hw,h]
-- topological pulse annihilator. weights function f continuous and finite shift bubble. Separate constant representing zero.
private lemma topping (s:List (Axis×ℤ)) : ∃ S:Finset Cover, ∃ A:Cover→ℝ→ℂ,
     (∀ i∈S, 0 < i) ∧ (∀ i∈S,Continuous (A i)) ∧
     ∀ n:Cover,(∃ k,(k,n k)∈ s)→∀ x:ℝ, 1+∑ j∈S,A j x*mode (tmap (x • windH j)) (-n)=0 :=by
 classical
 induction s with
 | nil=> exact ⟨∅,fun _ _=>0,by simp,by simp,by simp⟩
 | cons i L ih=>
    obtain ⟨k,z⟩:= i; obtain ⟨S,A,hp,he,h⟩:=ih; let F(u:Cover) (n:Cover)(x:ℝ):= mode (tmap (x • windH u)) (-n); let q:Cover:= step k; let e:Cover:= z • q
    let B(x:ℝ):= -(F q e x)⁻¹; have hc: Continuous B:=by
       unfold B; apply Continuous.neg; unfold F; apply Continuous.inv₀; · unfold tmap mode; fun_prop
       intro x t; exact Complex.exp_ne_zero _ t
    have hq:0<q:=lt_of_le_of_ne (fun i=>by by_cases h:i=k <;> simp [q,h]) (by intro h; have he:=congrFun h k; simp [q] at he)
    let g(i:Cover):= i+q; let T:=S.image g; let K:=T∪insert q S
    let Z(i:Cover)(x:ℝ):=(if i∈ S then A i x else 0)+(if i∈ T then A (i-q) x* B x else 0)+(if i=q then B x else 0)
    have ht:S⊆ K:= subset_trans (subset_insert ..) Finset.subset_union_right; have hx:T⊆ K:= subset_union_left
    refine ⟨K,Z,fun i hi=>?_,fun i hi=>?_,fun n u t=>?_⟩
    · rcases mem_union.mp hi with h|h
      · obtain ⟨i,hu,rfl⟩:=mem_image.mp h; exact add_pos (hp i hu) hq
      exact (mem_insert.mp h).elim (fun v=>v ▸ hq) (hp i)
    · apply Continuous.add; apply Continuous.add; split_ifs with h; exact he i h; exact continuous_const
      · split_ifs with h
        · obtain ⟨y,v,rfl⟩:= mem_image.mp h; simpa only [g,add_sub_cancel_right] using (show Continuous (fun x=>A y x * B x) from (he y v).mul hc)
        exact continuous_const
      split_ifs <;> first|exact continuous_const|exact hc
    let X(i):=F i n t
    have hf(i):X (g i)=X i* X q:=by unfold X F g; rw [windH_add, smul_add,show ∀ x y:Bin,tmap (x+y)=tmap x+tmap y from fun i j=> funext fun _=>Complex.ofReal_add ..,mode_phase]
    change 1+ ∑ i∈K,Z i t* X i= _; simp only [Z,add_mul,Finset.sum_add_distrib]
    have hk:{q}⊆K:=singleton_subset_iff.mpr (mem_union_right _ (mem_insert_self ..))
    let E:=∑ i∈S,A i t* X i
    have hX : ∑ i∈K,(if i∈S then A i t else 0)*X i=E:=by
       rw [←Finset.sum_subset ht (fun i _ v=> by rw [if_neg v,zero_mul])]; exact Finset.sum_congr rfl fun i u=> by rw [if_pos u]
    rw [hX,← Finset.sum_subset hx (fun i _ v=> by rw [if_neg v,zero_mul]),← Finset.sum_subset hk (fun i _ v=> by rw [if_neg (fun u=>v (mem_singleton.mpr u)),zero_mul]),sum_singleton,if_pos rfl]
    have hh:∑ i∈T,(if i∈T then A (i-q) t*B t else 0)*X i= E*(B t* X q):=by -- parentheses
       unfold E; rw [Finset.sum_mul,show ∑ i∈T,_=_ from Finset.sum_image (g:=g) (s:=S) (f:=fun i=>(if i∈T then A (i-q) t*B t else 0)*X i) (fun _ _ _ _ p=>add_right_cancel p)]; exact Finset.sum_congr rfl fun i hv=>by rw [if_pos (show g i∈T from Finset.mem_image_of_mem _ hv),hf]; unfold g; rw [add_sub_cancel_right]; ring
    rw [hh, show 1+(E+E*(B t * X q)+ B t * X q)=(1+E)*(1+B t*X q) from by ring]
    obtain ⟨l,w⟩:= u; rcases List.mem_cons.mp w with v|v
    · have ht:l=k ∧ n l=z:= Prod.mk.inj v; unfold B X; rw [show F q n t= F q e t from cuteds k n e (by simp [e,q,←ht.2, ht.1]) t,neg_mul,inv_mul_cancel₀ (show F q e t≠0 from Complex.exp_ne_zero _),add_neg_cancel,mul_zero]
    rw [show 1+E=0 from h n ⟨l,v⟩ t, zero_mul]
-- leads of origins
abbrev UA:Axis:= (2:Fin 3).castSucc
private abbrev Trumbull (d:ℕ)(v:Bin):= ((↑(v TA):ℂ)/2)^(2*d)*(2*(↑(v UA):ℂ) - I*2*(v TA))/radius v
private abbrev Coval (d:ℕ)(b:Cover)(z:ℂ):=
  let u:= z+(b TA:ℂ); (u/2)^(2*d)*(2*(b UA:ℂ)-I*2*u)
private def plane (b:Cover) (t:ℝ): Bin:= step (0:Axis)+ t • step TA + windH b
private def hem (b:Cover):ℝ := ∑ i:Fin 3, plane b 0 i.castSucc^2
private abbrev Rate (b:Cover)(z:ℂ):ℂ:= hem b +(z+(b TA:ℂ))^2
private lemma planeH (b:Cover)(t:ℝ):plane b t TA=t+ (b TA:ℝ) :=by unfold plane; simp [TA,step,windH]
private lemma planeG (b:Cover)(i:Fin 3)(t:ℝ):plane b t i.castSucc= (if i=0 then 1 else 0)+(b i.castSucc:ℝ):=by
 unfold plane; fin_cases i <;> norm_num [TA,step,windH,Fin.isValue] <;> right <;> (apply Pi.single_eq_of_ne; decide)
private lemma tuneH (b:Cover)(t:ℝ): radius (plane b t)=hem b+(t+(b TA:ℝ))^2:=by
    unfold radius hem; simp only [Axis,Fin.sum_univ_castSucc]; -- rew in hem undesired
    simp_rw [show ∀ i:Fin 3, plane b t i.castSucc=plane b 0 i.castSucc from fun i=>(planeG b i t).trans (planeG b i 0).symm]; rw [← show TA=(Fin.last 3) from rfl,planeH]
private lemma faces (b:Cover)(t:ℝ): (↑(radius (plane b t)):ℂ)=Rate b t:=by rw [tuneH]; unfold Rate; push_cast; rfl
private lemma posing (d:ℕ)(b:Cover)(t:ℝ): Trumbull d (plane b t)= Coval d b t / Rate b t:=by
 unfold Trumbull Coval; rw [planeH,faces,planeG]; push_cast; simp; rfl -- UA implicit tune
private lemma hem_basic (b:Cover)(p:0≤b) : 1≤hem b ∧ (hem b=1→ b TA=0 → b=0):=by
 have he(x:Axis): (0:ℝ) ≤ (b x:ℝ):=by exact_mod_cast p x
 let h(i:Fin 3):ℝ:= b i.castSucc
 have hx(i):0≤h i:=he i.castSucc
 have hp:hem b=(1+h 0)^2+(h 1)^2+(h 2)^2:=by unfold hem h; simp_rw [planeG]; rw [Fin.sum_univ_succ, Fin.sum_univ_two]; simp only [↓reduceIte,add_assoc]; norm_num [show (2:Fin 3) ≠0 by decide]
 rw [hp]; refine ⟨by nlinarith only [hx 0, sq_nonneg (h 1),sq_nonneg (h 2)],fun x v=>?_⟩
 have hz(i): h i=0:=by have u:=hx i; fin_cases i <;> dsimp at u ⊢ <;> nlinarith [hx 0,sq_nonneg (h 2),sq_nonneg (h 1)]
 funext j; induction j using Fin.lastCases
 exact v
 rename_i i
 change b _=0; specialize hz i; unfold h at hz; exact_mod_cast hz
private lemma beamPole (b:Cover)(p:0≤ b)(x: Rate b I=0): b=0:=by
 have he:=congrArg Complex.im x; have hp:=congrArg Complex.re x
 simp only [Rate,sq,Complex.add_im,Complex.add_re,Complex.mul_im, Complex.mul_re,Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im,Complex.ofReal_im, Complex.intCast_im,Complex.intCast_re, Complex.ofReal_re] at he hp
 have hv:(↑(b TA):ℝ)=0:=by linarith only [he]
 apply (hem_basic b p).2 _ (by exact_mod_cast hv); rw [hv] at hp; linarith only [hp]
private lemma uniqueBeam (f:ℂ→ℂ)(g:AnalyticOnNhd ℂ f Set.univ)(p:∀ t:ℝ,f t=0):f I=0:=by
 apply g.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) _ (Set.mem_univ _) -- tune
 let L:=𝓝[≠] (0:ℂ); have hx:Tendsto ((↑):ℝ→ℂ) (𝓝[≠] 0) L:= tendsto_nhdsWithin_iff.mpr ⟨by simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds), (show ∀ᶠ x:ℝ in 𝓝[≠] 0,x∈({0}:Set ℝ)ᶜ from self_mem_nhdsWithin).mono (fun x (h:x∈ ({0}:Set ℝ)ᶜ)=> Complex.ofReal_ne_zero.mpr h)⟩
 intro w; obtain ⟨t,h'⟩:=(hx.eventually w).exists; exact h' (p t)
private lemma becomes (d:ℕ)(S:Finset Cover)(a:Cover→ℂ)(p:∀ i∈S,0 < i) (x:∀ t:ℝ, Trumbull d (plane 0 t) + ∑ i∈ S,a i*Trumbull d (plane i t) =0):False:=by
 let D(z:ℂ):= Coval d 0 z*(∏ i∈S,Rate i z)+ ∑ i∈S,a i*Coval d i z*(Rate 0 z*(∏ j∈S.erase i,Rate j z))
 have he: AnalyticOnNhd ℂ D Set.univ:=by intro y _; apply ContDiffAt.analyticAt; unfold D Coval Rate; fun_prop
 have hp:D I=0:=by
    apply uniqueBeam _ he; intro t
    let T(z:Cover):=Rate z t; let q:=∏ i∈ S,T i
    have hv(i:Cover)(g:0 ≤ i): T i ≠ 0 := by
       rw [show T i= (↑(radius (plane i t)):ℂ) from (faces ..).symm]; apply Complex.ofReal_ne_zero.mpr; rw [tuneH]; have he:1 ≤ hem i:=(hem_basic i g).1; positivity
    have hk(i)(h:i∈S):q= T i*(∏ j∈S.erase i,T j):=(Finset.mul_prod_erase _ _ h).symm -- tune
    unfold D; have hx:=x t; simp_rw [posing] at hx; rw [←zero_mul (T 0*q),←hx, add_mul, Finset.sum_mul] -- zero occurrences rw caution
    have hAl(c b a j k:ℂ)(p:a≠0): c*b*(j*k)=(c*(b/a))*(j*(a*k)):=by field_simp
    congr 1; swap; · exact Finset.sum_congr rfl fun i e=> (show _=(a i*(Coval d i t/T i))*(T 0*q) from by rw [hk i e]; exact hAl _ _ _ _ _ (hv i (p i e).le))
    change Coval _ _ _*q=_/(T 0)*(T 0*q); rw [←mul_assoc, div_mul_cancel₀ _ (hv 0 le_rfl)]
 unfold D at hp; have hx:Rate 0 I=0:=by unfold Rate hem; simp_rw [planeG]; norm_num [Fin.sum_univ_succ]
 have ha:Coval d 0 I≠0:=by unfold Coval; simp -- I*2 nonzero
 have hv:∏ i∈S,Rate i I≠0:= Finset.prod_ne_zero_iff.mpr fun i t u=>(p i t).ne' (beamPole i (p i t).le u)
 simp_rw [hx,zero_mul,mul_zero, Finset.sum_const_zero,add_zero] at hp; exact mul_ne_zero ha hv hp
abbrev damper (d:ℕ)(x:Bin):ℂ:= sparrow d x*(tough x UA - I*tough x TA)
lemma liftedLife (d n:ℕ)(p:2*(1+n)+2 ≤ 2*d) : ContDiff ℝ (↑n) (damper d):=by
 rw [show damper d=fun x=> sparrow d x*tough x UA-I*(sparrow d x*tough x TA) from funext fun i=>by unfold damper; ring]; exact (parade d n UA p).sub (contDiff_const.mul (parade d n TA p))
lemma lilt (d:ℕ) : Pouch (damper d):=fun x z=> by unfold damper; rw [graze,sieved]
private lemma ferric (x:Bin)(i:Axis) : Tendsto (fun r:ℝ=>(r:ℂ)*tough (r • x) i) (𝓝[≠] 0) (𝓝 (2*(x i:ℂ)/(radius x:ℂ))) :=by
 let T:= 𝓝[≠] (0:ℝ); have he:Tendsto (fun r:ℝ=>r • x) T (𝓝 0):=by simpa using (tendsto_id.mono_left nhdsWithin_le_nhds|>.smul_const x : Tendsto _ T (𝓝 _)) -- tune
 let g:= weave; have hp:g 0=1:=by unfold g weave skirt; simp
 have ht:Tendsto (fun r:ℝ=>g (r • x)) T (𝓝 1):=by
    rw [←hp]; exact ((contDiff_prod (f:=fun (i:Axis) (b:Bin)=>skirt (b i)) (t:=Finset.univ) (fun i _=>(evenSkirt.comp (show ContDiff ℝ ω (fun b:Bin=> b i) by fun_prop)))).continuous.tendsto 0).comp he
 let K:= 2*(x i:ℂ)/radius x
 have h0:(0:Bin)∈Pasture:= Metric.mem_ball_self (by positivity)
 have hx:Tendsto (fun r:ℝ=>feast i (r • x)) T (𝓝 (feast i 0)):= ((buffet i 0).contDiffAt (isOpen_ball.mem_nhds h0)).continuousAt.tendsto.comp he
 have hc:Tendsto ((↑):ℝ→ℂ) T (𝓝 0):=by simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds)
 have hY:Tendsto (fun r:ℝ=>g (r • x)^8 * K+(r:ℂ)*feast i (r • x)) T (𝓝 K) :=by simpa only [one_pow,one_mul,zero_mul,add_zero] using! (((ht.pow 8).mul_const K).add (hc.mul hx))
 refine hY.congr' ?_; filter_upwards [he.eventually (isOpen_ball.mem_nhds h0), show ∀ᶠ i:ℝ in T,i∈ ({0}:Set ℝ)ᶜ from self_mem_nhdsWithin] with r v e; have he:(r:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (show r≠0 from e); rw [convene _ i v,mul_add,slat,stem_0,add_zero]
 rw [show radius (r • x)=r^2*radius x from (by unfold radius; simp_rw [Pi.smul_apply,smul_eq_mul,mul_pow]; rw [Finset.mul_sum])]
 unfold g K; simp only [Pi.smul_apply,smul_eq_mul]; push_cast
 by_cases t:x=0
 · subst x; simp
 field_simp [Complex.ofReal_ne_zero.mpr (radius_pos x t).ne']
private def tick (d:ℕ)(r:ℝ) := (r:ℂ) / (r:ℂ)^(2*d)
private lemma shopping (d:ℕ)(x:Bin): Tendsto (fun y:ℝ=> tick d y*damper d (y • x)) (𝓝[≠] 0) (𝓝 (Trumbull d x)):=by
 let T:= 𝓝[≠] (0:ℝ); let K:ℂ:=↑(x TA:ℝ)/2; have hp:Tendsto (fun y:ℝ=> sparrow d (y • x)/(y:ℂ)^(2*d)) T (𝓝 (K^(2*d))) :=by
    let w (y:ℝ):ℝ:= y*x TA/2
    have he:Tendsto (fun y:ℝ=> (↑(Real.sinc (w y)):ℂ)) T (𝓝 1):=by
       have ht: Continuous (fun y:ℝ=> (↑(Real.sinc (w y)):ℂ)) := by unfold w; fun_prop
       simpa [w] using ((ht.tendsto 0).mono_left nhdsWithin_le_nhds)
    refine Tendsto.congr' ?_ (show Tendsto (fun y:ℝ=> ((↑(Real.sinc (w y)):ℂ)*K)^(2*d)) T (𝓝 (K^(2*d))) from by simpa only [one_mul] using (he.mul_const K|>.pow (2*d)))
    filter_upwards [show ∀ᶠ i:ℝ in T,i∈ ({0}:Set ℝ)ᶜ from self_mem_nhdsWithin] with i t; have hf:(i:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (show i≠0 from t)
    change _= (↑(Real.sin (w i)):ℂ)^(2*d)/(i:ℂ)^(2*d)
    have hx(y:ℝ):Real.sin y=Real.sinc y*y:=by
       by_cases r:y=0; · subst y; simp
       rw [Real.sinc_of_ne_zero r,div_mul_cancel₀ _ r]
    rw [←div_pow]; congr 1; rw [hx,Complex.ofReal_mul]; unfold K w; push_cast; field_simp
 have hs:= hp.mul ((ferric x UA).sub ((ferric x TA).const_mul I))
 unfold tick damper Trumbull; unfold K at hs; ring_nf at hs ⊢; apply Tendsto.congr _ hs; intro i; ring -- expensive

set_option maxHeartbeats 120000 in
lemma opened (d:ℕ)(h: 10 ≤ d)(M:ℕ):∃ x:Cover, (∀ i,(M:ℕ)<(x i).natAbs) ∧ chipPay (damper d) x ≠ 0:=by
 by_contra e
 classical
 let T: List (Axis×ℤ):= ((Finset.univ:Finset Axis) ×ˢ TwistT M).toList
 obtain ⟨S,A,p,t,g⟩:=topping T
 let b:=fun i=> A i 0
 let f:= damper d
 have hg (x:Bin)(y:ℝ): f x+∑ j∈S,A j y*f (x+y • windH j)=0:=by
    have he(n):chipPay f n≠0→ ∃ k,(k,n k)∈ T:=by
       intro v; by_contra! u; apply e; refine ⟨n,fun i=> ?_,v⟩; specialize u i; simp only [T, Finset.mem_toList,Finset.mem_product, Finset.mem_univ,true_and, TwistT,Finset.mem_Icc] at u; omega
    let Z(n:Cover)(x:Bin):= chipPay f n*mode (tmap x) (-n)
    have ht(x:Bin):HasSum (fun n=> Z n x) (f x):= lived (lilt _) (liftedLife d 8 (by omega)) x
    have hp:= (ht x).add (hasSum_sum (s:=S) fun j (_:j∈S)=> (ht (x+y • windH j)).mul_left (A j y)) -- or HasSum.sum
    unfold Z at hp; apply hp.unique; convert (hasSum_zero (α:=ℂ) (β:=Cover)) using 1
    ext1 i; by_cases v: chipPay f i≠0
    · have hx:=g i (he i v) y; let W:=∑ j∈ S,A j y*mode (tmap (y • windH j)) (-i);
      have hw:∀ j:Cover, mode (tmap (x+y • windH j)) (-i)=mode (tmap x) (-i)*mode (tmap (y • windH j)) (-i):= fun j=> by rw [show ∀ x y:Bin,tmap (x+y)=tmap x+tmap y from fun i j=> funext fun _=>Complex.ofReal_add ..,mode_phase]
      simp_rw [hw]; let C:= Z i x; rw [show ∑ j∈S,A j y*(chipPay f i*(mode (tmap x) (-i)*mode (tmap (y • windH j)) (-i)))=C*W from (by unfold C W Z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>by ring)]; change C+C*W=0; rw [show W=-1 from (eq_neg_of_add_eq_zero_right hx),mul_neg,mul_one,add_neg_cancel]
    simp [not_not.mp v]
 apply becomes d S b p; intro u
 let x:=plane 0 u; let w:=𝓝[≠] (0:ℝ); have ht (y:ℝ) : tick d y *f (y • x)+ ∑ i∈S,A i y * (tick d y*f (y • plane i u))=0:=by
    rw [show ∑ i∈S,A i y * (tick d y*f (y • plane i u))=tick d y*∑ i∈S,A i y*f ((y • x)+y • windH i) from (by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>by rw [←smul_add,show x+windH i=plane i u by simp [x,plane],mul_left_comm]), ← mul_add,hg,mul_zero]
 have hp : Tendsto (fun y:ℝ=> tick d y *f (y • x)+ ∑ i∈S,A i y * (tick d y*f (y • plane i u))) w (𝓝 _) := (shopping d x).add (tendsto_finsetSum _ (fun i h'=> (((t i h').tendsto 0).mono_left nhdsWithin_le_nhds).mul (shopping d (plane i u))))
 exact tendsto_nhds_unique hp (tendsto_const_nhds.congr fun i=> (ht i).symm) -- alpha
end YM.CF.Crest.Sleet.Sorcerer
#print axioms YM.CF.Crest.Sleet.Sorcerer.opened
