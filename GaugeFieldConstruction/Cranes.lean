import GaugeFieldConstruction.Pigeon
import YM.Corona.Spend
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Stretch
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Finset
open scoped Topology BigOperators ComplexConjugate Matrix InnerProductSpace
variable {c f:Side}
abbrev Crossed (k:form 1 c)(j:form 1 c):Prop:=∀ x y:Body 1 c,k x≠0→ j y≠0→40 < separation x.1 y.1
abbrev Tr (s:StepData c f)(I:form 1 c) : form 1 f:= (mean s)ᵀ *ᵥ I
variable (s:StepData c f)(h:s.patch.J=4)
lemma past {k j:form 1 c}(v:Crossed k j): k ⬝ᵥ j=0:=by refine sum_eq_zero fun i _=>?_ ; by_contra! p; obtain ⟨p,w⟩:= mul_ne_zero_iff.mp p; have he:=v i i p w; simp [separation,pdist,lift] at he
include h
lemma paymind (x:Site c)(y: s.patch.Points) (i a:Axis) (k:ℕ)(v:k < s.patch.L.val): separation (atPoint s x y + k • step i) (s.ratio.embed x) ≤ 8*s.patch.L.val :=by
 let L:=s.patch.L
 have hv: pdist (wrap f (y.val + k • step i)) ≤ 8*L.val:= Finset.sup_le fun j _=>by
   apply (Corona.lap ..).trans; have hx:y.val ∈ box ((s.patch.J+3) * s.patch.L.val):=y.property; rw [h] at hx; have he:= (box_test.mp hx); have he := And.intro (he.1 j) (he.2 j)
   change (y.val j+(k • step i:Cover) j).natAbs ≤ _
   rw [Pi.smul_apply,nsmul_eq_mul]
   by_cases p:j=i
   · subst j; simp only [Lattice.step_apply,if_true, mul_one]; dsimp [L]; omega -- tune
   simp only [Lattice.step_apply,p,if_false,mul_zero,add_zero]; dsimp [L]; omega
 rw [separation]; simp only [map_add,map_nsmul,wrap_step] at hv; rw [show (atPoint s x y + k • step i) - s.ratio.embed x= wrap f y.val + k • step i from ?_]; exact hv
 change (wrap f y.val+s.ratio.embed x + _)-_= _; abel
lemma earl (x:Body 1 c)(X:Body 1 f)(p: mean s x X≠0): separation X.1 (s.ratio.embed x.1) ≤ 8*s.patch.L.val:=by
 let b: form 1 f:=Pi.single X 1
 have he:(mean s *ᵥ b) x=mean s x X:=by simp [b,mulVec, dotProduct,Pi.single_apply, mul_ite] -- tune
 have g:=mean_run_real s b x; rw [he] at g; rw [g] at p
 obtain ⟨y,-,w⟩:= exists_ne_zero_of_sum_ne_zero p; obtain ⟨k,v,q⟩:= exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul w)
 unfold b at q; rw [Pi.single_apply] at q; split at q; · rename_i ht; rw [←ht]; exact paymind s h x.1 y _ 0 _ (mem_range.mp v)
 exact absurd rfl q
lemma pivotC {k j:form 1 c}(v:Crossed k j):Crossed (Tr s k) (Tr s j):=by
 intro x y p u; obtain ⟨i,-,hx⟩:= exists_ne_zero_of_sum_ne_zero p; obtain ⟨l,-,hl⟩:= exists_ne_zero_of_sum_ne_zero u
 have he:=earl s h i x (left_ne_zero_of_mul hx); have ht:=earl s h l y (left_ne_zero_of_mul hl)
 have hw:=v i l (right_ne_zero_of_mul hx) (right_ne_zero_of_mul hl); have hr:=s.patch.coarse
 let L:=s.patch.L; have h1:L.val * 41 ≤ separation (s.ratio.embed i.1) (s.ratio.embed l.1):=(Nat.mul_le_mul_left _ hw).trans (Corona.below s.ratio ..)
 rw [separation_comm] at he
 have h2:=separation_triangle (s.ratio.embed i.1) x.1 y.1; have h3:=separation_triangle (s.ratio.embed i.1) y.1 (s.ratio.embed l.1)
 dsimp only [L] at h1; omega
abbrev Cycle (n:Side)(q:Momentum):Prop:= ∀ x y:Cover, wrap n x=wrap n y → mode q x=mode q y
abbrev perQ (n:Side)(i:TypeFace 1)(p:Momentum) : Body 1 n →ℂ:= fun x=> if x.2=i then mode p (lift x.1) else 0
abbrev PriceM (j:form 1 c)(p:Momentum)(a:TypeFace 1):= reK j ⬝ᵥ perQ c a p
abbrev FilterT (L:Side)(p:Momentum)(a:TypeFace 1):=(L.val:ℂ)*(area L p)^4*rail L (p (axisEquiv.symm a))
omit h in
lemma bringQ (p:Momentum)(g: Cycle f p):Cycle c (s.patch.L.val • p):=by intro x y w; rw [mode_scale,mode_scale]; apply g; rw [←show s.ratio.embed (wrap c x)=wrap f (s.patch.L.val • x) from s.ratio.embed_wrap _,← show s.ratio.embed (wrap c y)=wrap f (s.patch.L.val • y) from s.ratio.embed_wrap _,w] -- tune
lemma sail_power (p:Momentum)(u:Cycle f p)(a:TypeFace 1): approached (mean s) *ᵥ perQ f a p= FilterT s.patch.L p a • perQ c a (s.patch.L.val • p):=by
 let L:=s.patch.L; funext x; rw [mean_run]; by_cases H:x.2=a; swap; · simp [perQ,H]
 simp only [Pi.smul_apply,perQ,H,if_true,smul_eq_mul]; let i:= axisEquiv.symm a
 have he(y:s.patch.Points)(k:ℕ): mode p (lift (atPoint s x.1 y + k • step i))= mode (L.val • p) (lift x.1)*mode p y.val*twirl (p i) k :=by
    have hk: wrap f (lift (atPoint s x.1 y + k • step i))=wrap f (L.val • lift x.1+y.val+k • step i):=by rw [wrap_lift,map_add,map_add,map_nsmul (wrap f) k,wrap_step]; unfold atPoint; rw [add_comm _ (wrap f y.val)]; rfl
    have ht: mode p (k • (step i:Cover))=twirl (p i) k:=by rw [←mode_scale,Exterior.factor,Pi.smul_apply,nsmul_eq_mul]; unfold twirl; push_cast; congr 1; ring
    rw [u _ _ hk,mode_shift,mode_shift,← mode_scale L.val,ht] -- tune
 unfold FilterT; unfold i at he; simp_rw [he, ← Finset.mul_sum]; rw [show area _ _ ^4 = massFilter s.patch p from h ▸ rfl, ← pays_roll,rail]
 dsimp only [L,i] at *; field_simp [side_ne s.patch.L]
 conv_rhs => rw [Finset.mul_sum]
 exact sum_congr rfl (fun _ _=>by ring)
lemma matadors (J:form 1 c)(p:Momentum)(u:Cycle f p)(a:TypeFace 1): PriceM (Tr s J) p a=FilterT s.patch.L p a* PriceM J (s.patch.L.val • p) a:=by unfold PriceM Tr; rw [mulVec_transpose,vecst,←dotProduct_mulVec, sail_power s h p u,dotProduct_smul]; exact rfl -- tune
omit h
lemma filter_mult (L M:Side)(v:Odd L.val)(w:Odd M.val)(p:Momentum)(a:TypeFace 1) : FilterT L (M.val • p) a * FilterT M p a = FilterT (L*M) p a:=by
 have he:area L (M.val • p)*area M p=area (L*M) p:=by unfold area; simp_rw [Pi.smul_apply,nsmul_eq_mul,←prod_mul_distrib]; refine prod_congr rfl fun i _=>plank_bind L M v w _
 unfold FilterT; rw [mul_side_complex, ←he, Pi.smul_apply,nsmul_eq_mul, mul_pow,←rail_bind]; ring
lemma rhythm (g:Ratio c f)(k:form 1 f)(p:Site c)(l:Site g.count)(a:TypeFace 1):pack_R g k (p,l,a)= PriceM k (aliasAt (mon p) l) a:=by
 change (reK k) ⬝ᵥ (fun v=> (priceZ (g:=g)) v (p,l,a))=_; unfold PriceM; congr 1; ext1 ⟨x,i⟩; exact sample ..
end YM.Next.Free.Stretch
end
