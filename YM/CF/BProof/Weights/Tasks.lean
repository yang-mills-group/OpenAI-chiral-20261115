import YM.CF.BProof.Weights.Flash

/- Majorant on regular Taylor short terms & grouped real charges; support per
 column to Ray(1 after buying inv), with accounting. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Weights
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot Mapping House Pricing
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
local notation "G"=> SU.group
variable {s c': Side}(Y:Yard s)(S:Hall s)(g:Ratio c' s)
variable (M:ℝ→ℕ)(T:PathData G)(θ β:ℝ){R y w C v κ:ℝ}{c:Clip}{K:Chart G}{P: Pub G}(p:Model K P c Y.short M R y κ)(u:Room Y (M y))(t:T.Bounds c w R v)(h:θ∈Set.Icc (1/2) 2)(q:BudgetPoint)(k:ValidR c q (M y))
variable (x x': Pawn Y) (b:Y.Col) (V: Finset (Block Y c'))
abbrev tax (l:Tile s):= Form.Taylor y (Y.roll (Pawn.roof x y T θ p.X)) c q T (M y) (Pawn.put S x y T θ p.X) β l
def trick := -∑ i∈ good Y (M y) x.sev with Lens Y i (M:=M y)=b, Weights.tax Y S M T θ β p q x i
def tabs := Weights.light Y M T θ p x b + Weights.fog Y M T θ p x b + Weights.trick Y S M T θ β p q x b
abbrev rentT (d m:ℕ)(c:Clip)(R C y:ℝ):= gearBound d m * |costY c R C y m (2*y)|
def tabW (P:Pub G)(c:Clip)(M:ℝ→ℕ)(R C:ℝ)(d:ℕ)(y:ℝ) := |hotLight P c M R d y|+ |fogC M c d R y|+rentT d (M y) c R C y
lemma tabW_pos (P:Pub G)(c:Clip)(M:ℝ→ℕ)(R C:ℝ)(d:ℕ)(y:ℝ) : 0≤ tabW P c M R C d y:=by unfold tabW rentT; positivity
lemma tabN (M:ℝ→ℕ)(u:PL fun y=>(M y:ℝ))(P:Pub G)(c:Clip)(R C:ℝ)(d:ℕ)(h:0<d) : NPL (tabW P c M R C d):=by
 have he:PL fun y=>(gearBound d (M y):ℝ):=by unfold gearBound; push_cast; apply PL.mul (PL.const _); apply PL.pow; exact ((PL.const _).mul ((PL.const _).add ((PL.const _).mul u))).add (PL.const _)
 have hf {f:ℝ→ℝ}(p:NPL f):NPL (fun y=> |f y|):= NPL.by_le p (Eventually.of_forall fun y=>by rw [abs_abs])
 exact ((hf (hot_n M u P c R d h)).add (hf (fog_n M u c d R h))).add (he.muln (hf (grantY c M u R C))) -- tune
include t
lemma tax_m (i:Tile s) : Measurable (fun x:Pawn Y=> Weights.tax Y S M T θ β p q x i):=by
 unfold Weights.tax Form.Taylor; refine ((heavy_c c q T _ β i t).comp (Pawn.put_m Y S y T θ p.X)).sub ((measurable_const.add ?_).add ?_)
 · unfold Form.L; apply Measurable.const_mul; apply Continuous.measurable (f:=fun x:Mag.Lie=> inner ℝ _ x) (by fun_prop) |>.comp; fun_prop
 unfold Form.Q; fun_prop
lemma trick_m : Measurable (fun x:Pawn Y=> Weights.trick Y S M T θ β p q x b):=by
 apply Pawn.onSev (fun Z x=> -∑ i∈good Y (M y) Z with Lens Y i (M:=M y)=b, Weights.tax Y S M T θ β p q x i); intro i; exact (Finset.measurable_sum _ (fun l hl=>tax_m Y S _ _ _ _ p t q _)).neg
lemma tabs_m : Measurable (fun x:Pawn Y=> tabs Y S M T θ β p q x b) := ((light_m ..).add (fog_m ..)).add (trick_m Y S M T θ β p t q b)
variable (a: Pricing.StampC P c Y.short M R κ y)(e:Ink K C y)(Kp:q.threshold=thresh y)(hv: Pawn.Proceeds Y S y T θ p.X κ x)
include u h t k
include hv a e Kp
lemma trick_cost (g:β≤2*y)(g':0≤β) : |Weights.trick Y S M T θ β p q x b| ≤ rentT Y.short (M y) c R C y:=by
 let G':=(good Y (M y) x.sev).filter (fun i=> Lens Y i (M:=M y)=b); have hp(i:Tile s)(q:i∈G'): Stove Y (M y) i ∧ Cave Y (M y) i x.sev ∧ Lens Y i (M:=M y)=b := by obtain ⟨a,h⟩:= mem_filter.mp q; exact ⟨(mem_filter.mp a).2.1,(mem_filter.mp a).2.2,h⟩
 have hh:G'.card≤gearBound Y.short (M y):= (card_le_card (t:=Gear Y (M y) b) (fun i (q:i∈ G')=> (engaged ..).2 ⟨(hp i q).1,(hp i q).2.2 ▸ (own_need ..)⟩)).trans (gear_count ..)
 unfold trick; rw [abs_neg]; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (s:=G') (g:=fun i=>|costY c R C y (M y) (2*y)|) (fun i hi=>?_)).trans (by rw [sum_const,nsmul_eq_mul]; unfold rentT; gcongr)); obtain ⟨h₀,h₁,h₂,h₃⟩:= hv
 apply le_trans _ (le_abs_self _); exact Pricing.Model.taylor_pay K P c M R κ y Y T p u t h x.sev x.gauss (Pawn.put S x y T θ p.X) q x.gap e Kp k h₃ (Y.mix_field ..) h₁ h₀ a i (mem_filter.mp hi).1 g g' -- tune
lemma tabBound (g:β≤2*y)(g':0≤β) : |tabs Y S M T θ β p q x b|≤ tabW P c M R C Y.short y:=by
 refine (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add ?_ ?_)) (trick_cost Y S M T θ β p u t h q k x b a e Kp hv g g')); exact le_trans (lights Y M T p u t h x b hv.1) (le_abs_self _); exact le_trans (fog_c Y M T p u t h x b hv.1) (le_abs_self _)
omit a e Kp
include hv
lemma tab_spark (u':Pawn.Agreed g x x' V)(v: Pawn.Shade g V b (dim_step M Y.short c R y))(hv':Pawn.Proceeds Y S y T θ p.X κ x')(H: 5*M y+2<2*Deep.D Y):
    tabs Y S M T θ β p q x b=tabs Y S M T θ β p q x' b:=by
 have hp(k:ℕ)(l:k≤dim_step M Y.short c R y):Pawn.Shade g V b k:=fun i q=> v i ((Gauss.base Y).mono l q)
 unfold tabs; rw [fog_h Y g M T p u x x' b V u' v,view_h Y g M T p u x x' b V u' (hp _ (by unfold dim_step; omega))]; unfold Weights.trick good; apply congrArg ((Weights.light Y M T θ p x' b + Weights.fog Y M T θ p x' b)+·); apply congrArg Neg.neg; simp_rw [filter_filter,sum_filter]; apply sum_congr rfl; intro i hi; by_cases h:Stove Y (M y) i∧ Lens Y i (M:=M y)=b
 · have he(k:ℕ)(l:k≤dim_step M Y.short c R y): Pawn.Shade g V (Lens Y i (M:=M y)) k:= h.2.symm ▸ hp k l; have hh:= Pawn.cave_h g x x' V u' i (he (3*M y) (by unfold dim_step; omega)); apply if_congr (by tauto) (Pawn.taylor_h g S x x' V y T θ p.X u u' i h.1 q t k hv.2.2.1 hv'.2.2.1 H (he _ (by rw [p.p_hor]; unfold dim_step; omega))) rfl
 rw [if_neg,if_neg] <;> tauto
omit u h hv t k
lemma error_all : ∑ b,Weights.trick Y S M T θ β p q x b = Release.error Y T θ y p.X q β x.sev x.gauss (Pawn.put S x y T θ p.X) := by
 unfold trick; rw [sum_neg_distrib]; exact congrArg Neg.neg (sum_fiberwise _ _ _)
end YM.CF.BProof.Weights
