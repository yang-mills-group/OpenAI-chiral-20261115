import GaugeFieldConstruction.PalmoraMars
/-!
# finite cost gestures
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Set Filter MeasureTheory Measure Complex Analysis Points Bulb
open scoped ContDiff Topology BigOperators
section Motion
variable {E G: Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup G][NormedSpace ℝ G]
variable (x:E) (p:List E)
-- all Points-n vectors for now. define general D list to carry B actions
abbrev PoolDMars (l:List E)(F:E→ G): E→G:=List.foldr Analysis.D F l
lemma poolHeadMars (v : E)(s : List E)(F:E→G): PoolDMars (v::s) F=D v (PoolDMars s F):=rfl
lemma pool_appendMars (v w:List E)(F:E→G) : PoolDMars (v++w) F=PoolDMars v (PoolDMars w F):=List.foldr_append ..
lemma pool_germMars (f g:E→G)(h:f =ᶠ[𝓝 x] g):PoolDMars p f=ᶠ[𝓝 x]PoolDMars p g:=by
 induction p with
 | nil=> exact h
 | cons v s h'=> exact h'.fderiv.mono fun i hi=> congr_arg (fun l:E→L[ℝ]G=>l v) hi
lemma poolSmMars (x:E)(f:E→G)(hf:ContDiffAt ℝ ∞ f x):ContDiffAt ℝ ∞ (PoolDMars p f) x:=by
 induction p with
 | nil=> exact hf
 | cons v s hs=> exact dSmooth hs v (by simp)
lemma poolBillMars (v : Fin p.length→ E)(e : p=List.ofFn v)(f:E→G)(S:Set E)(u:IsOpen S)(h:ContDiffOn ℝ ∞ f S)(x:E)(hx:x∈S):
    PoolDMars p f x = iteratedFDeriv ℝ p.length f x v :=by
 induction p generalizing x with
 | nil=> exact (iteratedFDeriv_zero_apply ..).symm
 | cons i s hs=>
    rw[List.ofFn_succ] at e; let w:=Fin.tail v
    have hi:= (List.cons.inj e).1; have ht:s=List.ofFn w:= (List.cons.inj e).2
    change D i (PoolDMars s f) x=_
    change _=iteratedFDeriv ℝ (s.length+1) f x v
    conv_rhs=> arg 2; rw[←Fin.cons_self_tail v] -- tune arg
    rw [cons_jet (((h x hx).contDiffAt (u.mem_nhds hx)).of_le (by exact_mod_cast le_top))]
    -- don't subst i? type eq changes lengths dep defeq
    apply Eq.trans (GermD i (show PoolDMars s f=ᶠ[𝓝 x] (fun y=>iteratedFDeriv ℝ s.length f y w) from (u.eventually_mem hx).mono (fun y hy=>hs w ht y hy))) ?_; exact congr_arg (fun q=>D q (fun y=>iteratedFDeriv ℝ s.length f y w) x) hi
lemma pool_payMars {m:ℕ}(v : Fin m→ E)(f:E→G)(S:Set E)(u:IsOpen S)(h:ContDiffOn ℝ ∞ f S)(x:E)(hx:x∈S):PoolDMars (List.ofFn v) f x=iteratedFDeriv ℝ m f x v :=by
 generalize he : List.ofFn v=p
 have e : m=p.length:=by simp [←he ]
 subst m; exact poolBillMars p v he.symm f S u h x hx
lemma pool_sumMars {ι: Type*}(s: Finset ι)(F:ι→ E→G)(S:Set E)(u:IsOpen S)(h:∀ i∈s,ContDiffOn ℝ ∞ (F i) S)(x:E)(hx:x∈ S):
    PoolDMars p (fun x=>∑ i∈s,F i x) x=∑ i∈s,PoolDMars p (F i) x :=by
 induction p generalizing x with
 | nil => rfl
 | cons i s' hs=>
    have he: PoolDMars s' (fun x=> ∑ i∈s,F i x)=ᶠ[𝓝 x] fun x=>∑ i∈s,PoolDMars s' (F i) x:= (u.eventually_mem hx).mono hs -- tune
    rw[poolHeadMars,GermD i he]
    unfold D -- unfolds pool?
    rw [fderiv_fun_sum (fun i l=> (poolSmMars s' _ _ (((h i l) x hx).contDiffAt (u.mem_nhds hx))).differentiableAt (by simp)),_root_.sum_apply]; rfl
-- Capped generic family price (no m growth)
end Motion
variable {n:ℕ}
section Sauna -- tune
variable (b:Bulb)(k : Fin n)(x:Points n)(h:BreatherMars b k x)(a i: Axis)
variable (F:Points (n+1)→ℂ)(hf:ContDiffOn ℝ ∞ F (conf _))
local notation "α"=> SoilMars F (Payroll.ticket (n:=n) i) b a i
local notation "Τ" F:max => SoilMars (n:=n) F (Payroll.ticket i) b a i
abbrev trailMars (l:List (Points n)):=l.map (Points.cons 0)
lemma coatMars(y:E4): (α) (y,x) = (LED b a).f y • F (Points.cons y x):=by rw[SoilMars]; simp only[Payroll.ticket,mul_one,basis_eq,↓reduceIte]; rfl -- tune syntaxes
-- share parameter
include hf h
lemma CamDMars (v:Points n)(y:E4): D ((0:E4),v) α (y,x)= (Τ (D (Points.cons 0 v) F)) (y,x):=by
 by_cases c:y∈b.shore
 · have H:= RoomMars b k x h y c
   let U:= (LED b a).f; let Q:E4×Points n→E4:=Prod.fst
   have he:DifferentiableAt ℝ (U ∘ Q) (y,x):= ((LED b a).d.comp contDiff_fst).differentiable (by simp) _
   have heF:DifferentiableAt ℝ F (fuse.symm (y,x)):= ((hf _ H).contDiffAt ((conf_open _).mem_nhds H)).differentiableAt (by simp)
   rw [show α= (U ∘ Q) • (F ∘ fuse.symm) from funext fun x' => coatMars _ x'.2 _ _ _ x'.1]
   rw [D,fderiv_smul he (heF.comp _ fuse.symm.differentiableAt)]
   have hv:fderiv ℝ (U ∘ Q) (y,x) (0,v)=0:=by rw[fderiv_comp (y,x) ((LED b a).d.differentiable (by simp) (Q (y,x))) differentiableAt_fst,(hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,x))).fderiv]; simp
   simp only[ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,hv,zero_smul,add_zero,zero_add,Function.comp_apply]; rw[fderiv_comp (y,x) heF fuse.symm.differentiableAt, ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply, coatMars]; rfl -- tune
 have hp: y ∉ (LED b a).run:= fun z=> c (cone _ _ z)
 have hz : α =ᶠ[𝓝 (y,x)] (fun _=>0):=by
    filter_upwards [((isClosed_tsupport (LED b a).f).isOpen_compl.prod isOpen_univ).mem_nhds (show (y,x)∈ (run (LED b a))ᶜ ×ˢ univ from ⟨hp,mem_univ _⟩)] with i hΓ; exact SoilAreaMars _ _ _ _ _ _ hΓ.1 _
 rw [SoilAreaMars _ _ _ _ _ _ hp,GermD _ hz]; simp[D]
lemma CordDMars (l:List (Points n)) : PoolDMars l (WrapMars α) x= WrapMars (Τ (PoolDMars (trailMars l) F)) x:=by
 induction l generalizing x with
 | nil=> rfl
 | cons v s hs=>
    let W:= PoolDMars (trailMars s) F
    have he:IsOpen {x|BreatherMars b k x}:=BreathingMars ..
    have hy:ContDiffOn ℝ ∞ W (conf _):= fun y hp=> (poolSmMars _ _ _ ((hf _ hp).contDiffAt ((conf_open _).mem_nhds hp))).contDiffWithinAt
    have hz:= (he.eventually_mem (show x∈ {x|BreatherMars b k x} from h)).mono (fun i z=>hs i z)
    rw[poolHeadMars,GermD _ hz,CubicDMars _ {x|BreatherMars b k x} he (run (LED b a)) (LED b a).c (fun i e y=>SoilCapMars _ hy _ _ _ _ i k e y) (fun i e y E=> SoilAreaMars _ _ _ _ _ _ E _) x h]
    exact integral_congr_ae (Eventually.of_forall fun y=>CamDMars _ _ _ h _ _ _ hy v y)
end Sauna
#print axioms CordDMars
end YM.GaugeFieldConstruction.Fathom
