import YM.SU5.FiniteGaugeData.Drachma.Dovecote

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch CF.Font Next.Rank.Axial
open scoped Topology BigOperators Matrix Classical
variable {c f:Side} {S:StepData c f}{p:Clip}{a A₀:ℝ}{P Q:Bed}
local notation "σ" => S.kernel.penalty
variable (F:Forest S.ratio)(A:AfterT c) (G:AfterT f)

-- restrict with one-coordinate accounting. Relation with augmentation via exact shear on gauges.
omit A in
lemma senate{X Y:Type}[Fintype X][Fintype Y][DecidableEq X][DecidableEq Y] (T:sp (X⊕Y)) (E:Matrix Y X ℝ)(h:T.IsSymm)(he:∀ x:coin X,T*ᵥ swapper x (E*ᵥ x)=0):
 (T+prizes (sty_l X Y)).det=(T.submatrix Sum.inr Sum.inr).det:=by
 let L:=layer E; rw [← wager_det _ L (layer_det _)]
 have u(x:coin Y): ℜ X Y (T*ᵥ swapper (0:coin X) x)= T.submatrix Sum.inr Sum.inr *ᵥ x:=by
    ext i; change ∑ j:X⊕Y,T (.inr i) j*swapper (0:coin X) x j=_; rw [Fintype.sum_sum_type]; simp [swapper]; rfl
 have hw(x:coin Y)(y:coin (X⊕Y)):dotProduct (swapper (0:coin X) x) y=dotProduct x (ℜ X Y y):=by rw [bills,born_l,born_r]; simp
 have hz(x:coin (X⊕Y)):L*ᵥ x= swapper (ℓ X Y x) (E*ᵥ ℓ X Y x) +swapper (0:coin X) (ℜ X Y x):=by unfold L; rw [layer_bill]; funext i; cases i <;> simp [swapper]
 have ht: boost (T+prizes (sty_l X Y)) L=sided (1:sp X) (T.submatrix Sum.inr Sum.inr):=by
    apply wager; intro x y; rw [boost_bill,sidedBill,plus_bill,prize_bill,sty_l_bill,sty_l_bill,one_mulVec]; have hp(z:coin (X⊕Y)): ℓ X Y (L*ᵥ z)=ℓ X Y z:=by unfold L; rw [layer_bill,born_l]
    rw [hp,hp,hz,hz,mulVec_add,he,zero_add, add_dotProduct, dotProduct_mulVec (swapper (ℓ X Y x) _), ← Matrix.mulVec_transpose,h.eq,he,zero_dotProduct, zero_add, hw,u, add_comm]
    -- symmetry easier separate
 rw [ht,sided_det,det_one,one_mul]

variable {r:Ratio c f}(F': Forest r)
def bail (F':Forest r): stem F' ⊕ F'.Free ≃ LT f := (Equiv.sumCompl (fun i:Edge (Site f)=>i∈F'.trunks)).trans (portfolio f)
@[simp] lemma ballot_l(i:stem F'): bail F' (.inl i)= tag F' i:=rfl
@[simp] lemma ballot_r(i:F'.Free): bail F' (.inr i)= ηT F' i:=rfl
lemma senateF(T:sp (LT f))(h:T.IsSymm)(he:∀ t:Site f→ℝ,(∀ i:Site c,t (r.embed i)=0)→T*ᵥ ant t=0):
 (T+prizes (tickets F')).det =(T.submatrix (ηT F') (ηT F')).det:=by
 let e:=bail F'; let S:= T.submatrix e e; let u:=prizes (sty_l (stem F') F'.Free)
 have hp:(prizes (tickets F')).submatrix e e=u:=by
    have he: (tickets F').submatrix (Equiv.refl (stem F')) e= sty_l (stem F') F'.Free:=by
       ext i j; cases j with
       | inl j=> by_cases hx:i=j; · subst i; simp [tickets,sty_l,fromCols,e,one_apply]
                 have hh: tag F' i≠tag F' j:=fun h=> hx (Subtype.ext (mark_ins h)); simp [tickets,sty_l,fromCols,e,id,one_apply,hx,hh]
       | inr j=> have hx: tag F' i≠ηT F' j:=fun h=>j.2 (mark_ins h ▸ i.2); simp [tickets,sty_l,fromCols,e,id,hx,one_apply]
    unfold prizes u; rw [prizes,← he]; rw [show ((tickets F').submatrix (Equiv.refl (stem F')) e).transpose=(tickets F').transpose.submatrix e (Equiv.refl (stem F')) from rfl,submatrix_mul_equiv] -- tune
 let A:= LinearMap.toMatrix' ((atlas f (k:=ℝ) (P:=ℝ)).comp (propeller F'))
 let C:= A.submatrix (ηT F') id
 have he'(x:coin (stem F')): S *ᵥ swapper x (C *ᵥ x)=0:=by
    let t:=descend F' x
    have ha:A*ᵥ x= ant t:=by unfold A; rw [LinearMap.toMatrix'_mulVec]; rfl
    have hu: swapper x (C*ᵥ x)=ant t ∘ e:=by
       funext j; cases j with
       | inl j=> exact (congr_fun (onTab F' x) j).symm
       | inr j=> exact congr_fun ha (ηT F' j)
    rw [hu]; ext i; unfold S; change ∑ j, T (e i) (e j)*ant t (e j)=0; rw [ show (∑ j,_)= ∑ j, T (e i) j * ant t j from e.sum_comp _] -- tune
    exact congr_fun (he t (descend_anchor F' x)) (e i)
 rw [← det_submatrix_equiv_self e]; change (S+(prizes (tickets F')).submatrix e e).det= _; rw [hp]; unfold u; rw [senate S C (h.submatrix e) he'] -- tune defeq
 rfl

abbrev subB := (plaid P f+σ• prizes (probe S)) -- remove implicit var.S
abbrev jazz(F:Forest S.ratio)(P:Bed): Matrix F.Free F.Free ℝ:= (subB (P:=P) (S:=S)).submatrix (ηT F) (ηT F)

lemma bore_p (P:Bed)(h:(P.metric.acts f).IsSymm): (bore F P).det= (jazz F P).det:=by
 apply senateF F _ ((plaidS h).add (by simp [Matrix.IsSymm,(prize_sym _).eq])); intro t p; rw [add_mulVec,plaid_nil P (ant t) (ant_c t),zero_add,smul_mulVec,prize_nil (probe S) _ (by rw [payout]; have he:t ∘ S.ratio.embed=0:=funext p; rw [he]; exact (atlas c (k:=ℝ) (P:=ℝ)).map_zero), smul_zero]
lemma chips_p (P:Bed)(h:(P.metric.acts f).IsSymm): (chips G P).det= ((plaid P f+prizes (lasers f)).submatrix (ηT G) (ηT G)).det:=by
 unfold chips; rw [_root_.add_right_comm]; exact senateF G _ ((plaidS h).add (prize_sym _)) fun t _=> by rw [add_mulVec,plaid_nil P (ant t) (ant_c t),prize_nil _ _ (lasers_ant t),zero_add]

-- HERE EXACT step relation on internal gauge analytic regulator
lemma fumes {V:Matrix (LT f) (LT c) ℝ} (i:Inputs S V (P.metric.acts f) (Q.metric.acts c))(h:(P.metric.acts f).IsSymm):
 chassis P f *σ^Fintype.card (LT c)=(jazz F P).det*chassis Q c:=by unfold chassis; rw [chimney F (axle c) (axle f) i h, bore_p F P h]
lemma fumes_p{p q:Clip}{a b c₁ c₂:ℝ} {V:Matrix (LT f) (LT c) ℝ} (i:Inputs S V (P.metric.acts f) (Q.metric.acts c)) (he:Floor P p f a c₁)(hv:Floor Q q c b c₂)(hp:0<a)(hq:0<b): 0<(jazz F P).det:= pos_of_mul_pos_left ((fumes F i he.symmetric.1) ▸ mul_pos (chassis_p he hp) (pow_pos S.kernel.penalty_pos _)) (chassis_p hv hq).le -- tune
end YM.SU5.FiniteGaugeData.Drachma
