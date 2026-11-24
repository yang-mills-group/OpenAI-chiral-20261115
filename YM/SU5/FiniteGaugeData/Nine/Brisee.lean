import YM.SU5.FiniteGaugeData.Nine.Ombre
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Window.Pivot
variable (o:Cover){N:Side}
-- price.CROP.
variable {Λ:Preparation}{l:ℕ} {s t k j i:ℕ}{h:Real.exp 1 ≤ Λ.x}
local notation "Κ"=> storeH Λ.V
local notation "Ω" i:max=> tailCost (Κ).c (Κ).C i
private theorem sol (k:ℕ)(p:1≤k): ∃ i c, (0:ℝ)<c∧ c<1∧∀ (N:Side), i ≤ N.val → Aptitude k N ∧∀ M:Tulip.Male,c≤ rubra k N M∧ c≤ villa k N M:=by
 obtain ⟨c,v,e,n',P⟩:= Pivot.duly k p; obtain ⟨t,h⟩:= Pivot.tall p; exact ⟨t+n',c,v,e,fun i A=>⟨h _ (by omega), P _ (by omega)⟩⟩
private abbrev four_sol:= sol 4 (by decide) -- return Type? syntax make lemma
abbrev lively :ℕ:= Classical.choose four_sol -- K needed no d.
abbrev σFee:ℝ:= four_sol.choose_spec.choose
lemma phase_costP(Λ:Preparation)(z:lively ≤ N.val): Aptitude Λ.K.j N ∧∀ M:Tulip.Male,σFee ≤ rubra Λ.K.j N M∧ σFee ≤ villa Λ.K.j N M:= Λ.kJ.symm ▸ four_sol.choose_spec.choose_spec.2.2 N z
lemma σFee_pos : 0< σFee:= four_sol.choose_spec.choose_spec.1
def tableI (n:ℕ) : ℝ:= (1+2*(σFee/2)⁻¹)^n
lemma tableI_nn(n:ℕ): 0≤tableI n:=by let p:=σFee_pos; unfold tableI; positivity
private lemma tend_opt(c C:ℝ)(p:0<c): Tendsto (fun i:ℕ=> opt (tailCost c C i)) atTop (𝓝 0):=by
 let P:= tailCost c C; have he:Tendsto P atTop (𝓝 0):= tailCloud _ _ p; simpa only [opt, P,add_zero,mul_zero] using (((tendsto_const_nhds (x:=(2:ℝ))).add he).mul he)
private lemma slabs (c C:ℝ)(p:0<c): ∃ i:ℕ,2*opt (tailCost c C i) ≤ σFee/2:=by
 have ht: Tendsto (fun i=> (2:ℝ)*opt (tailCost c C i)) atTop (𝓝 0):=by simpa only [mul_zero] using (tend_opt c C p).const_mul 2
 exact (ht.eventually (ge_mem_nhds (half_pos σFee_pos))).exists
abbrev sliceP (c C:ℝ)(p:0<c):ℕ:= (slabs c C p).choose
abbrev sideP (Λ:Preparation):ℕ:= sliceP (storeH Λ.V).c (storeH Λ.V).C ((storeH Λ.V).posse.level)
abbrev z₁(Λ:Preparation):= (2:ℕ)*sideP Λ -- pitch earlier than expansion halo.Old `manner`.344
variable {g:ℝ}(Λ)(u:ℕ)(c C ξ:ℝ)
local notation "ζ"=> Quest.zen (slopeF Λ.W g) (storeH Λ.V).C
-- costs, rank `m≥2*n'`, choose m **even‐radius m≥2**. shape. derivative. set alpha=4log + 4oven to pay 1/8
abbrev alpha (u:ℕ)(ξ:ℝ):ℝ:=4*( Real.log (1+2*(σFee/2)⁻¹)+|ξ| *oven u+4)
def thresholdP(d:ℕ)(θ:ℝ):ℝ:= Real.exp (alpha d θ)+1
lemma alpha_nn (u:ℕ)(ξ:ℝ): 0≤ alpha u ξ:=by have he:0 ≤ Real.log (1+2*(σFee/2)⁻¹):= Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg zero_le_two (inv_pos.mpr (half_pos σFee_pos)|>.le))); unfold alpha oven; positivity
section price
variable {r w d:ℕ}{t δ η:ℝ}(V:Travels Λ)
structure Vogue (Λ:Preparation)(α:ℝ)(w:ℕ)(t δ:ℝ) : Prop where
 font : Crags α Λ w δ
 love : opt (tailCost (storeH Λ.V).c (storeH Λ.V).C w)*(σFee/2)⁻¹+(2*tailCost (storeH Λ.V).c (storeH Λ.V).C w+t*(storeH Λ.V).C) ≤ δ-tailCost (storeH Λ.V).c (storeH Λ.V).C w
 warmth : 0 < t
variable {n h':ℕ}
open Nacre
-- ignores l in α; later expansion radius depends Λ R d l ; t after α ; shape.Notational.P.
abbrev quoteI (Λ:Preparation) (g:ℝ):= alpha (z₁ Λ) (Quest.zen (slopeF Λ.W g) (storeH Λ.V).C)
lemma priceα {h:Real.exp 1 ≤ Λ.x}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(hU: d+addgap (tent Y h) ≤ allotL (z₁ Λ)*n)(e: 0<n)(x:2*h'=n^4)(p:0≤g) : lighting h' (quoteI Λ g) (tableI (n^4)) *Real.exp (ζ * ((4:ℝ)*(d+addgap (tent Y h):ℕ))^4)<1/8:=by
 let v:ℕ:=d+addgap (tent Y h); let H:=n^4; have hv:0<H:=pow_pos e _; have ht:(1:ℝ) ≤ (H:ℝ):=Nat.one_le_cast.mpr hv; let V:= oven (z₁ Λ); let f:= σFee; let u:=1+2*(σFee/2)⁻¹; have hu:0<u:=add_pos_of_pos_of_nonneg one_pos (mul_nonneg zero_le_two (inv_pos.mpr (half_pos σFee_pos)|>.le))
 have he:(4*(v:ℝ))^4 ≤ V*(H:ℝ):=by unfold V H oven; push_cast; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have he: (↑v:ℝ)≤ (allotL (z₁ Λ):ℝ)*n:=(by exact_mod_cast hU); push_cast at he; linarith only [he] -- pushcasts allotL
 let fX:= quoteI Λ g; have hx:0 ≤ ζ:= zen_pos _ _ (by unfold slopeF; positivity) ((Κ).posse.value.le)
 have hw: lighting h' fX (tableI (n^4))=Real.exp (( Real.log u-fX/4)*(n^4:ℕ)):=by
    unfold lighting tableI; change Real.exp (-fX/2*h')*u^(n^4)=_; rw [show (Real.log u-fX/4)* ↑(n^4 :ℕ) = (-fX/2*h')+(n^4:ℕ)*Real.log u from ?_,Real.exp_add,Real.exp_nat_mul,Real.exp_log hu]; rw [←x]; push_cast; ring
 rw [hw,← Real.exp_add]; have hp:fX= 4*(Real.log u+ζ*V+4):=by unfold fX quoteI; unfold alpha; rw [abs_of_nonneg hx]
 rw [hp]; refine lt_of_le_of_lt (Real.exp_monotone ?_) (show Real.exp (-4)< (1:ℝ)/8 from ?_); change (Real.log u-4*(Real.log u+ζ*V+4)/4)*(H:ℝ)+ζ*(4*(v:ℝ))^4 ≤ -4; nlinarith only [ht,mul_le_mul_of_nonneg_left he hx]
 have he:4<Real.exp 2:= by rw [show (2:ℝ)=1+1 from (by norm_num),Real.exp_add]; nlinarith only [Real.exp_one_gt_d9];
 rw [Real.exp_neg,←one_div]; apply one_div_lt_one_div_of_lt (by norm_num); rw [show (4:ℝ)= 2+2 from (by norm_num), Real.exp_add]; nlinarith
lemma alpha_needs (P:thresholdP (z₁ Λ) ζ ≤ Λ.h) : ∃ w t e, Vogue Λ (quoteI Λ g) w t e:=by
 let ε:= Real.exp (-quoteI Λ g)/2; have hv:0<ε:=half_pos (Real.exp_pos _); let b:=(σFee/2)⁻¹; let C:=(Κ).C; let t:= ε/(2*C); have hc:0<C:=(Κ).posse.value; have ht:0<t:= div_pos hv (by positivity); have hk:t*C=ε/2:=by unfold t; field_simp
 let F:= tailCost (Κ).c C; have he:Tendsto (fun w=> opt (F w)*b+2*F w+F w) atTop (𝓝 0):=by have h:Tendsto F atTop (𝓝 0):= tailCloud _ _ (Κ).posse.level; simpa using ((((show Tendsto (fun w=> opt (F w)) atTop (𝓝 0) from tend_opt _ _ (Κ).posse.level).mul_const b).add (h.const_mul 2)).add h)
 obtain ⟨w,h,W⟩:=((show ∀ᶠ i:ℕ in atTop,opt (F i)*b+2*F i+F i≤ ε/2 from he.eventually (ge_mem_nhds (half_pos hv))).and ((tailCloud (Κ).c C (Κ).posse.level).eventually (ge_mem_nhds hv))).exists; refine ⟨w,t,ε,⟨alpha_nn ..,P, show ε+F w≤_ from ?_,hv.le⟩, ?_,ht⟩
 · change F w≤ ε at W; unfold ε at *; linarith
 change opt (F w)*b+(2*F w+t*C) ≤ ε-F w; linarith
lemma priceI : 2*opt (tailCost (Κ).c (Κ).C (sideP Λ))≤ σFee/2:= (slabs _ _ (storeH Λ.V).posse.level).choose_spec
end price
def stapled(D:Discovery):Discovery where
 fee K L R V b d U W M J l g :=
  max (D.fee K L R V b d U W M J l g) (thresholdP (2*sliceP (storeH V).c (storeH V).C (storeH V).posse.level) (Quest.zen (slopeF W g) (storeH V).C))
#print axioms priceα
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
