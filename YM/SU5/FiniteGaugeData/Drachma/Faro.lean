import YM.SU5.FiniteGaugeData.Drachma.ForestJ

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

variable (S)
abbrev meter(f c:Side):= lasers f*am f c
abbrev meterD(f c:Side):= lasers c*cd f c
abbrev roc:=cd f c-probe S*am f c
def jointK(P:Bed):sp (spanJ f c):= boost (plaid P f) (am f c)+ σ•prizes (roc S)
omit S in
lemma smid{X:Type}[Fintype X](x y:coin X)(s:ℝ)(T:sp X): dotProduct x ((s•T)*ᵥ y)= s* dotProduct x (T*ᵥ y):=by rw [smul_mulVec,dotProduct_smul]; rfl
lemma rocs(x:coin (spanJ f c)): roc S *ᵥ x=du f c x - probe S*ᵥ um f c x:=by rw [roc,sub_mulVec, cd,am, ←mulVec_mulVec,sty_l_bill,sty_r_bill]
lemma fuel(x y:coin (spanJ f c)): dotProduct x (jointK S P *ᵥ y)=dotProduct (um f c x) (plaid P f *ᵥ (um f c y))+ σ * dotProduct (roc S*ᵥ x) (roc S*ᵥ y):=by rw [jointK,plus_bill,boost_bill,smid,am,sty_l_bill,sty_l_bill,prize_bill]
lemma symBy{X Y:Type}[Fintype Y](T:sp Y)(U:Matrix Y X ℝ)(h:T.IsSymm): (boost T U).IsSymm:=by unfold Matrix.IsSymm boost; simp [h.eq, Matrix.mul_assoc]
lemma jointS(h:(P.metric.acts f).IsSymm): (jointK S P).IsSymm:= (symBy _ _ (plaidS h)).add (by simp [Matrix.IsSymm,(prize_sym _).eq])
lemma payout(t:Site f→ℝ):probe S *ᵥ ant t=ant (t ∘ S.ratio.embed):=by rw [ant_d,root_gradient,ant_d]; rfl
lemma prize_nil{X Y:Type}[Fintype Y][Fintype X](A:Matrix Y X ℝ)(x:coin X)(h:A*ᵥ x=0): prizes A *ᵥ x=0:=by rw [prizes, ←mulVec_mulVec,h,mulVec_zero]
lemma booster_kill(x:coin (spanJ f c)) (e:plaid P f *ᵥ um f c x=0)(h:roc S*ᵥ x=0): jointK S P *ᵥ x=0:=by rw [jointK,add_mulVec,smul_mulVec,prize_nil _ x h,boost, ← mulVec_mulVec,←mulVec_mulVec, am,sty_l_bill, show plaid P f *ᵥ ℓ _ _ x=0 from e,mulVec_zero]; simp -- tune
lemma halt_J(P:Bed)(t:Site f→ℝ): jointK S P *ᵥ uphill S.ratio t=0:=by
 apply booster_kill S (uphill S.ratio t) (plaid_nil P (ant t) (ant_c t)); rw [rocs]; exact sub_eq_zero.mpr (payout S t).symm
lemma meters_f (t:Site f→ℝ): meter f c*ᵥ uphill S.ratio t=0:=by rw [meter, ←mulVec_mulVec,am,sty_l_bill]; exact lasers_ant t
lemma meters_d (t:Site f→ℝ): meterD f c*ᵥ uphill S.ratio t=0:=by rw [meterD, ←mulVec_mulVec,cd,sty_r_bill]; exact lasers_ant _ -- tune

/-- Direction for moving BOTH holonomy probes by the same period-one color. Here '1' is in accounting unit of ℝ, not radians or normalized by L-volume. The Step predictor includes a further root correction that is exact, not dropped. -/
def amplifier(f:Side): Matrix (LT f) Axis ℝ:= LinearMap.toMatrix' ((f.val:ℝ)⁻¹ • (LinearMap.pi fun i : LT f => (LinearMap.proj (R:=ℝ) (φ:=fun _ : Axis=>ℝ) (axisEquiv.symm i.2))))
lemma amplified(x:coin Axis): amplifier f*ᵥ x=amble (fun i=> x i / f.val):=by rw [amplifier,LinearMap.toMatrix'_mulVec]; ext i; change (f.val:ℝ)⁻¹ * _= x _ /_; rw [div_eq_mul_inv,mul_comm]; rfl
def siren: Matrix (spanJ f c) Axis ℝ:= fromRows (amplifier f) (probe S*amplifier f)
lemma vehicle(x:coin Axis): siren S*ᵥ x=swapper (amplifier f*ᵥ x) (probe S*ᵥ(amplifier f*ᵥ x)):=by rw [siren,rband,←mulVec_mulVec]
lemma siren_free(P:Bed)(x:coin Axis):jointK S P*ᵥ (siren S *ᵥ x)=0:=by
 rw [vehicle]; apply booster_kill
 · apply plaid_nil; unfold um; rw [born_l,amplified]; exact amble_d _
 rw [rocs]; exact sub_self _
lemma siren_f(x:coin Axis): meter f c*ᵥ (siren S*ᵥ x)=x:=by
 rw [vehicle,meter,←mulVec_mulVec,am,sty_l_bill,born_l,amplified,lasers_read]; ext i; change (f.val:ℝ)*(x i /f.val)= x i; field_simp
lemma siren_d(x:coin Axis): meterD f c*ᵥ (siren S*ᵥ x)=x:=by
 rw [vehicle,meterD,←mulVec_mulVec,cd,sty_r_bill,born_r,amplified,probe,add_mulVec,←mulVec_mulVec,mulVec_add,lasers_d, mean_s,lasers_read,add_zero]; ext i; change (c.val:ℝ)*(S.patch.L.val*(x i/f.val))=x i; rw [S.sizes]; push_cast; field_simp
variable {S}
lemma swap_horizon (P:Bed)(h:(P.metric.acts f).IsSymm):
 ((jointK S P+prizes (oakC G c))+prizes (meter f c)).det=((jointK S P+prizes (oakD F A))+prizes (meterD f c)).det:=by
 let O:=oakD F A; let R:=jointK S P; let L:=meter f c; let T:=meterD f c
 rw [_root_.add_right_comm _ _ (prizes L),prize_exchange F A G _ ((jointS S h).add (prize_sym _)) (fun t=> by rw [add_mulVec,halt_J,prize_nil _ _ (meters_f S t),zero_add]), _root_.add_right_comm _ (prizes L) (prizes O)] -- tune
 let U:=thumbB F A; let E:=siren S-U*O*siren S
 have he(x:coin Axis): E*ᵥ x=siren S*ᵥ x-U *ᵥ (O *ᵥ (siren S*ᵥ x)):= by unfold E; rw [sub_mulVec, ←mulVec_mulVec,←mulVec_mulVec]
 change (R+prizes O+prizes L).det=(R+prizes O+prizes T).det
 have hh : R * E=0:= Matrix.ext_iff_mulVec.mpr fun x=>by
    rw [←mulVec_mulVec,zero_mulVec,he,mulVec_sub]; unfold R U; rw [siren_free,v_B,halt_J,sub_self]
 have hf : O*E=0:=Matrix.ext_iff_mulVec.mpr fun x=>by rw [←mulVec_mulVec,zero_mulVec,he,mulVec_sub,mulVec_mulVec (M:=O) (N:=U),show O*U=1 from compB F A, one_mulVec,sub_self]
 apply tally _ _ _ E (Matrix.ext_iff_mulVec.mpr fun x=>by rw [←mulVec_mulVec,one_mulVec,he,mulVec_sub]; unfold L U; rw [siren_f,v_B,meters_f,sub_zero]) (by rw [Matrix.add_mul,hh,zero_add,prizes,Matrix.mul_assoc,hf,Matrix.mul_zero]) ((jointS S h).add (prize_sym O))
 have hu:T*E=1:= Matrix.ext_iff_mulVec.mpr fun x=>by rw [←mulVec_mulVec,one_mulVec,he,mulVec_sub]; unfold T U; rw [siren_d,v_B, meters_d,sub_zero]
 rw [hu]; simp
end YM.SU5.FiniteGaugeData.Drachma
