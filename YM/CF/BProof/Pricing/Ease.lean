import YM.CF.BProof.Pricing.Toll

/- drought automatic away from rawbad. Use issue coordinates before testing; show same
 membership in the projected gap. Halo statements will be composed with Face. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Pricing
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)(c:Clip)(d:ℕ)(M:ℝ→ℕ)(R κ y:ℝ)
abbrev rawL := coin y 0 (1/8) 0
abbrev rawQ := rawL y^2
abbrev raw_bill := Release.Day.tip (turnP d) (rawQ y)
abbrev bill_beam := g y*((SU.group.lieDim+1:ℕ)*(Beam.cost c d (steady c d M R y)*rawL y))
structure Ease : Prop where
 cost : K.C*bill_beam c d M R y≤wc y
 size : bill_beam c d M R y ≤ K.size
 limit : wc y≤ κ*thresh y
lemma ease (p:0<d)(u:PL fun y=> (M y:ℝ))(v:0<κ): ∀ᶠ y:ℝ in atTop, Ease K c d M R κ y:=by
 let g(y):=Beam.cost c d (steady c d M R y); let C:=(SU.group.lieDim+1:ℝ); let r(y:ℝ):=g y*C; have he:PL r:= (beam_PL c d _ (steady_p c d M R p u)).mul (PL.const _)
 let z(y:ℝ):=coin y 0 (-3/8) 0; have hz:= he.muln (g:=z) (coin_n (a:=0) (b:= -3/8) (by norm_num) _); have H(y): bill_beam c d M R y=r y*z y*wc y:=by unfold bill_beam z wc; rw [_root_.mul_assoc (r y),coin_mul]; unfold r C g; push_cast; calc
    _ = (Beam.cost c d (steady c d M R y)*(SU.group.lieDim+1:ℝ))*(CF.BProof.g y*rawL y):=by ring
    _ =_:=by rw [coin_mul]; ring_nf
 filter_upwards [((PL.const K.C).muln hz).limit.eventually (ge_mem_nhds one_pos),(hz.mulp (coin_n (a:= -1/2) (b:=1/2) (by norm_num) _).weak).limit.eventually (ge_mem_nhds K.admitted), coin_budget (a:=-1/2) (b:=1/2) (c:=0) (d:= -1/2) (e:=1) (f:=0) (by norm_num) 1 κ v] with y h1 h2 h3
 constructor; rw [H,←mul_assoc]; exact (mul_le_mul_of_nonneg_right h1 (coin_pos ..).le).trans_eq (one_mul _); rw [H]; exact h2; exact (by simpa only [one_mul] using h3.le)
namespace Model
variable {s:Side}(Y:Yard s)(T:PathData G){θ q w:ℝ}(p:Model K P c Y.short M R y κ)(H:Room Y (M y))(u:T.Bounds c w R q)(h: θ∈Set.Icc (1/2) 2)
variable (Z:Finset Y.Col)(x:Plan Y)(W:Locale.House Y)(a:Y.Col)
def raw := Z ∪ Finset.univ.filter fun i=> hot.entry Y x i∈ Day.peak (rawQ y)
def Glow (d:ℕ):= ∀ b,(Gauss.base Y).N a b d→b∉raw y Y Z x
include H h u p
lemma temper (d:ℕ)(v: steady c Y.short M R y≤d)(e:Glow y Y Z x a d)(g:Ease K c Y.short M R κ y)(i:Y.Apt):
    cd G (Locale.A Y y a i) (Release.γ Y T θ y p.X Z x W a i) ≤ wc y:=by
 let R':= Release.γ Y T θ y p.X Z x W a; have hx(j:Stamp Y)(q:(Gauss.base Y).N a j.1 p.X.horizon'):|x j|≤ rawL y:=by
    rw [p.p_hor] at q; have ht:=e j.1 ((Gauss.base Y).mono v q); have hg:Day.ar (hot.entry Y x j.1)<rawQ y:= by by_contra! w; exact ht (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem_univ _,w⟩)); -- name
    exact venues Y x j.1 _ hg.le (coin_pos ..).le j.2
 let X:= tape Y T θ p.X Z x; have hr:=hot.beam_cost K P Y T θ κ p.X H u h Z x (p.bought K P c M R Y y κ) a _ (coin_pos ..).le i hx; rw [p.p_hor] at hr; let L:= Locale.A Y y a i; have hu:a∉ Z:=fun w=> e a ((Gauss.base Y).start a d) (mem_union_left _ w)
 rw [Release.γ, Sky.open_o _ _ _ _ p.X a W hu]; change cd G L (L*SU.group.lieExp (X (a,i))) ≤ _; unfold cd; rw [inv_mul_cancel_left]; exact (K.step _ (hr.trans g.size)).trans ((mul_le_mul_of_nonneg_left hr (zero_le_one.trans K.C_one)).trans g.cost)
lemma free (d:ℕ)(v: steady c Y.short M R y≤d)(e:Glow y Y Z x a d)(g:Ease K c Y.short M R κ y): a∉Locale.bed Y κ y (Release.γ Y T θ y p.X Z x W):=fun z=> (mem_filter.mp z).2 (fun i _=> (temper K P c M R κ y Y T p H u h Z x W a d v e g i |>.trans g.limit)) -- tune
end Model
end YM.CF.BProof.Pricing
