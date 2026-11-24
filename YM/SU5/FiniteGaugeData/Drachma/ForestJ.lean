import YM.SU5.FiniteGaugeData.Drachma.Vivo

/-! # The internal + coarse gauge projection, and transport of trunk measures. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch Next.Rank.Axial
open scoped Topology BigOperators Matrix Classical
variable {c f:Side} {r:Ratio c f}

abbrev spanJ(f c:Side):= LT f⊕LT c
abbrev um (f c:Side)(x:coin (spanJ f c)):=ℓ (LT f) (LT c) x
abbrev du (f c:Side)(x:coin (spanJ f c)):=ℜ (LT f) (LT c) x
abbrev am(f c:Side):=sty_l (LT f) (LT c)
abbrev cd(f c:Side):=sty_r (LT f) (LT c)
def uphill(r:Ratio c f)(t : Site f→ℝ):coin (spanJ f c):=swapper (ant t) (ant (t ∘ r.embed))
lemma highplus(r:Ratio c f)(t v:Site f→ℝ):uphill r (t+v)=uphill r t+uphill r v:=by
 unfold uphill; rw [ant_linear,show (t+v) ∘ r.embed=t ∘ r.embed+v ∘ r.embed from rfl,ant_linear]; funext i; cases i <;> rfl
lemma highscl(r:Ratio c f)(t:Site f→ℝ)(s:ℝ):uphill r (s•t)=s • uphill r t:=by
 unfold uphill; rw [ant_scale,show (s•t) ∘ r.embed=s •(t ∘r.embed) from rfl,ant_scale]; funext i; cases i <;> rfl
def climbJ(r:Ratio c f): (Site f→ℝ)→ₗ[ℝ] coin (spanJ f c):= {toFun:=uphill r,map_add':=highplus r,map_smul':=fun s a=> highscl r a s}

variable (F:Forest r)(A:AfterT c) (G:AfterT f)
def oakC(G:AfterT f) (c:Side):= tickets G*am f c
abbrev τ(F:Forest r)(A:AfterT c):= stem F ⊕ stem A
def oakD := fromRows (tickets F*am f c) (tickets A*cd f c)
lemma deckC (x:coin (spanJ f c)): oakC G c*ᵥ x=η_t G (um f c x):=by rw [oakC,← mulVec_mulVec,am,sty_l_bill,tickets_bill]
lemma deckD (x:coin (spanJ f c)): oakD F A *ᵥ x=swapper (η_t F (um f c x)) (η_t A (du f c x)):=by rw [oakD,rband,←mulVec_mulVec,←mulVec_mulVec, am,cd,sty_l_bill,sty_r_bill,tickets_bill,tickets_bill]
-- trunk rank and common units
lemma livesEq: Fintype.card (stem G)=Fintype.card (τ F A):=by
 change _= Fintype.card (stem F ⊕ stem A); rw [Fintype.card_sum]; have ht:=size_stamp F; have h1:=ranks_1 G; have h2:=ranks_1 A; omega
variable (r)
def thumbA: Matrix (spanJ f c) (stem G) ℝ:= LinearMap.toMatrix' ((climbJ r).comp (propeller G))
lemma v_A(x:coin (stem G)): thumbA r G*ᵥ x= uphill r (descend G x):=by rw [thumbA,LinearMap.toMatrix'_mulVec]; rfl
lemma compA : oakC G c * thumbA r G=1:=by apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← mulVec_mulVec,v_A,deckC, one_mulVec]; exact onTab G x
variable {r}
def thumbB: Matrix (spanJ f c) (τ F A) ℝ:= LinearMap.toMatrix'
 ((climbJ r).comp ((propeller F).comp (sty_l (stem F) (stem A)).mulVecLin + (LinearMap.pi fun i:Site f=>(LinearMap.proj (R:=ℝ) (φ:=fun _ : Site c=>ℝ) (r.parent i))).comp ((propeller A).comp (sty_r (stem F) (stem A)).mulVecLin))) -- tune
abbrev ail(F:Forest r)(A:AfterT c)(x:coin (τ F A)):= descend F (ℓ (stem F) (stem A) x) + descend A (ℜ (stem F) (stem A) x) ∘ r.parent
lemma v_B(x:coin (τ F A)): thumbB F A *ᵥ x=uphill r (ail F A x):=by
 rw [thumbB,LinearMap.toMatrix'_mulVec]; change uphill r (descend F (sty_l _ _ *ᵥ x)+ descend A (sty_r _ _ *ᵥ x) ∘ r.parent)=_; rw [sty_l_bill,sty_r_bill]
lemma compB:oakD F A*thumbB F A=1:=by
 apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← mulVec_mulVec,v_B,deckD,one_mulVec]; let v:=ail F A x; let a:= ℓ (stem F) (stem A) x; let b:= ℜ (stem F) (stem A) x
 change swapper (η_t F (ant v)) (η_t A (ant (v ∘ r.embed)))=x
 have he:v∘r.embed=descend A b:=by funext i; simp only [v,ail,Function.comp_apply,Pi.add_apply,descend_anchor,r.embed_parent,zero_add]; rfl
 have hl: η_t F (ant v)=a:=by
    unfold v ail; rw [ant_linear]; change η_t F (ant (descend F a))+_= _; rw [onTab,add_eq_left]; funext i
    change ant _ (markZ f i)=0; rw [ant_z]; simp only [SectorNext.Vacuum.FlatTree.climb,Function.comp_apply, F.trunk_internal i.2,sub_self,neg_zero]
 rw [hl,he,onTab]; exact born_two x
-- same null-space of GAUGES
lemma whole_const{X:Type}{v:Site f→ℝ}{h:X→ Site f} {g} (e: ∀ x,v x=g):v ∘ h=fun _=>g:= funext fun x=> e (h x)
lemma constHill(r:Ratio c f)(t:Site f→ℝ)(e:∀ x,t x=t 0):uphill r t=0:=by
 have he : ant t=0:=by funext i; simp only [ant,SectorNext.Vacuum.FlatTree.climb,e,sub_self,neg_zero,Pi.zero_apply] -- e simp loop?
 have hl:ant (t ∘ r.embed)=0:=by rw [whole_const e]; funext i; simp [ant,SectorNext.Vacuum.FlatTree.climb]
 funext i; unfold uphill; rw [he,hl]; cases i <;> rfl
lemma COnly{r:Ratio c f}{t:Site f→ℝ}(h:oakC G c*ᵥ uphill r t=0):uphill r t=0:= constHill r t (fun i=>all_anchor G t ((deckC G _).symm.trans h) i)
lemma DOnly{t:Site f→ℝ}(h:oakD F A*ᵥ uphill r t=0):uphill r t=0:=by
 rw [deckD] at h; let g : Site c→ℝ:= t ∘ r.embed
 have ht(i:Site f):t i=t (r.embed (r.parent i)):=climb_anchor F _ (congr_arg (ℓ (stem F) (stem A)) h) i
 have he(i:Site c): g i=g 0:= all_anchor A _ (congr_arg (ℜ (stem F) (stem A)) h) i
 have hc(i:Site f):t i=g 0:= (ht i).trans (he (r.parent i))
 exact constHill r t (fun i=>(hc i).trans (hc 0).symm)
lemma reclaim {X:Type}[Fintype X](E: Matrix X (spanJ f c) ℝ)(D:∀ x:Site f→ℝ,E *ᵥ uphill r x=0→uphill r x=0)(x y:Site f→ℝ)(he:E *ᵥ uphill r x=E *ᵥ uphill r y):uphill r x = uphill r y:=by
 apply sub_eq_zero.mp; change climbJ r x-climbJ r y=0; rw [← map_sub]; exact D _ (by change E *ᵥ climbJ r (x-y)=0; rw [map_sub,mulVec_sub]; exact sub_eq_zero.mpr he)
lemma paid_B(t:Site f→ℝ): thumbB F A*ᵥ (oakD F A*ᵥ uphill r t)=uphill r t:=by
 rw [v_B]; apply reclaim (oakD F A) (fun _ u=> DOnly F A u); rw [←v_B,mulVec_mulVec,compB,one_mulVec]
lemma paid_A(r:Ratio c f)(t:Site f→ℝ): thumbA r G*ᵥ (oakC G c*ᵥ uphill r t)=uphill r t:=by
 rw [v_A]; apply reclaim (oakC G c) (fun _ u=> COnly G u); rw [←v_A,mulVec_mulVec,compA,one_mulVec]
-- integer gauges
lemma integral_AtoD: integralMap (oakD F A * thumbA r G):=by
 intro y; let v := descend G y
 refine ⟨Sum.elim (η_t F (ant v)) (η_t A (ant (v∘ r.embed))),?_⟩; change (oakD F A * thumbA r G) *ᵥ toRealX y= _; rw [←mulVec_mulVec,v_A,deckD,descend_real]; change swapper (η_t F (ant (toRealX v))) (η_t A (ant ((toRealX v)∘ r.embed)))=_
 rw [ant_real,show toRealX v∘ r.embed=toRealX (v∘r.embed) from rfl,ant_real]; funext i; cases i <;> rfl
lemma integral_DtoA: integralMap (oakC G c * thumbB F A):=by
 intro y; let l:= descend F (y ∘ Sum.inl); let h:=descend A (y ∘ Sum.inr); let v:=l+h ∘ r.parent; refine ⟨η_t G (ant v),?_⟩; change (oakC G c * thumbB F A) *ᵥ toRealX y= _
 have he:ail F A (toRealX y)=toRealX v:=by
    change descend F (toRealX (y ∘Sum.inl))+descend A (toRealX (y∘Sum.inr))∘ r.parent= _; rw [descend_real,descend_real]; funext i; simp [v,l,h,toRealX]
 rw [←mulVec_mulVec, v_B,deckC, he]; change η_t G (ant (toRealX v))=_; rw [ant_real]; rfl
lemma prize_exchange (H:sp (spanJ f c))(h:H.IsSymm)(v:∀ t,H *ᵥ uphill r t=0):
 (H+prizes (oakC G c)).det=(H+prizes (oakD F A)).det:=by
 let e:stem G≃τ F A:= Fintype.equivOfCardEq (livesEq F A G); let P:=oakC G c; let U:=thumbA r G; let Q:=oakD F A; let V:=thumbB F A; let M:=(1:sp (τ F A)).submatrix e id; let W:=(1:sp (stem G)).submatrix e.symm id
 have he(x:coin (τ F A)):M *ᵥ x=x∘ e:= funext fun i=>congr_fun (one_mulVec x) (e i); have hw(x:coin (stem G)):W*ᵥ x=x∘e.symm:=funext fun i=>congr_fun (one_mulVec x) (e.symm i) -- tune line semi
 let A':= M*Q; let B':=V*W
 have hp: prizes A'=prizes Q:=by
    apply wager; intro x y; rw [prize_bill,prize_bill]; unfold A'; rw [←mulVec_mulVec,←mulVec_mulVec,he,he]; exact e.sum_comp (fun i=> (Q*ᵥ x) i * (Q*ᵥ y) i)
 change _=(H+prizes Q).det; rw [←hp]; apply tally H P A' U (compA ..) (Matrix.ext_iff_mulVec.mpr (fun i=>by unfold U; rw [←mulVec_mulVec,v_A,v,zero_mulVec])) h
 apply intact (A'*U) (P*B')
 · apply Matrix.ext_iff_mulVec.mpr; intro x; let y:=W*ᵥ x; unfold A' B' P Q V U; rw [← mulVec_mulVec,← mulVec_mulVec,← mulVec_mulVec,←mulVec_mulVec,←mulVec_mulVec, v_B, paid_A,←v_B,mulVec_mulVec (M:=oakD F A),compB]; rw [one_mulVec,one_mulVec,he,hw]; ext i; simp
 · intro x; obtain ⟨y,h⟩:=integral_AtoD F A G x; refine ⟨y∘ e,?_⟩; unfold A' Q U; rw [Matrix.mul_assoc,←mulVec_mulVec,h,he]; rfl
 intro x; obtain ⟨y,h⟩:=integral_DtoA F A G (x∘e.symm); refine ⟨y,?_⟩; unfold P B' V; rw [← Matrix.mul_assoc,←mulVec_mulVec,hw]; exact h
end YM.SU5.FiniteGaugeData.Drachma
