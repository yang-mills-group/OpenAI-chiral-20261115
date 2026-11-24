import YM.CF.BProof.Weights.Tasks
import YM.CF.BProof.Mapping.Wheel

/- support, component bills. combined Night & Crowd assignments exact, suppressed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Weights
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot Mapping House Pricing Prox Moment Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
local notation "G"=> SU.group
variable {s c': Side}(Y:Yard s)(S:Hall s)(g:Ratio c' s)
variable (M:ℝ→ℕ)(T:PathData G)(θ β:ℝ){R y w C v κ:ℝ}{c:Clip}{K:Chart G}{P: Pub G}(p:Model K P c Y.short M R y κ)(u:Room Y (M y))(t:T.Bounds c w R v)(h:θ∈Set.Icc (1/2) 2)(q:BudgetPoint)(k:ValidR c q (M y))
variable (x x': Pawn Y) (b:Y.Col) (V: Finset (Block Y c'))
def burn := Pricing.Model.vault (β:=β) K P c M R κ y Y T θ p u t h x.sev x.gauss (Pawn.put S x y T θ p.X) q b
abbrev issueD := Model.roster K P c M R Y y κ p T θ u t h
def issueW (Z: Finset Y.Col) := (Weights.issueD Y M T θ p u t h).long x.sev (Model.issued c M R y Y) Z
abbrev zCost (Z:Finset Y.Col) := (Weights.issueD Y M T θ p u t h).costs (Model.issued c M R y Y) Z
lemma cut_price : Release.cut P Y T θ y p.X q β x.sev x.gauss (Pawn.put S x y T θ p.X)=(∑ b,tabs Y S M T θ β p q x b)+(∑ b∈ x.sev,burn Y S M T θ β p u t h q x b)+∑ s,issueW Y M T θ p u t h x s:=by
 let U:= issueD Y M T θ p u t h; let T':= Pawn.put S x y T θ p.X
 let z:= U.ledger x.sev (Model.issued c M R y Y); unfold Release.cut burn Model.vault tabs issueW; rw [z,sum_add_distrib,sum_add_distrib,sum_add_distrib, sum_fog, error_all, sum_light]; unfold U; ring -- tune
lemma price_W (Z:Finset Y.Col): |issueW Y M T θ p u t h x Z| ≤ zCost Y M T θ p u t h Z:= Night.Design.costs_price ..
lemma W_m (Z:Finset Y.Col): Measurable (fun x:Pawn Y=> issueW Y M T θ p u t h x Z):= by
 apply Pawn.onSev (fun F x=> (issueD Y _ _ _ p u t h).long F (Model.issued c M R y Y) Z); intro F; exact measurable_const
@[fun_prop] lemma burn_m : Measurable (fun x:Pawn Y=> burn Y S M T θ β p u t h q x b):=by
 unfold burn Model.vault Release.crowd strong; apply Measurable.add; apply Measurable.sub _ measurable_const
 · let a (x:Pawn Y)(i):= Form.sound y c q T (M y) β i+ Form.L T (M y) c β y i (Y.roll (Pawn.roof x y T θ p.X))-heavy c q T (M y) β (Pawn.put S x y T θ p.X) i; change Measurable (fun x:Pawn Y=> ∑ i∈ packs Y (M y) x.sev b,a x i); apply Pawn.onSev (fun F x=>∑ i∈ packs Y (M y) F b,a x i); intro F; apply Finset.measurable_sum; intro i hi; unfold a Form.L; refine Measurable.sub (measurable_const.add (Measurable.const_mul ?_ _)) ((heavy_c c q T _ β i t).comp (Pawn.put_m ..)); exact (show Continuous (fun x:Mag.Lie=> inner ℝ (mA y • Form.root T (M y) i) x) by fun_prop).measurable.comp (f:=fun x:Pawn Y=> Form.linear T (M y) i (Y.roll (Pawn.roof x y T θ p.X))) (by fun_prop)
 exact Pawn.onSev (fun F (x:Pawn Y)=> (issueD Y _ _ _ p u t h).short F _ b) (fun i=> measurable_const)
-- lease burns local. count membership. avoid remote contour.
variable (e:Pawn.Proceeds Y S y T θ p.X κ x)(a: Pawn.Agreed g x x' V) (w':Pawn.Proceeds Y S y T θ p.X κ x')
abbrev license (M:ℝ→ℕ)(d:ℕ)(c:Clip)(R y:ℝ) := dim_step M d c R y + splitD c d M R y
lemma license_p (M:ℝ→ℕ)(v:PL fun y=>(M y:ℝ))(d:ℕ)(c:Clip)(R:ℝ)(h:0<d): PL (fun y=> (license M d c R y:ℝ)):=by
 have hg:=steady_p c d M R h v; have he:=(j_tail c d M R h v).1; unfold license dim_step; push_cast; exact ((hg.add ((PL.const _).mul v)).add hg).add he
include e a k w'
lemma burn_same (h₀:5*M y+2<2*Deep.D Y)(v: Pawn.Shade g V b (license M Y.short c R y)) : burn Y S M T θ β p u t h q x b=burn Y S M T θ β p u t h q x' b:=by
 have hx (d:ℕ) (u:d ≤ license M Y.short c R y) : Pawn.Shade g V b d:=fun i q=> v i ((Gauss.base Y).mono u q)
 unfold burn Model.vault Release.crowd; rw [show strong _ _ _ _ _ _ _ _ _ (roof_cost Y T θ y p.X x.sev x.gauss) _= _ from Pawn.strong_h g S x x' V y T θ p.X u a b q t k e.2.2.1 w'.2.2.1 h₀ (hx _ (by rw [p.p_hor]; unfold license dim_step; omega))]; congr 1; apply Night.Design.fares_part; exact fun i hi=> a.sev i (hx _ (by unfold Model.issued license; omega) i ((Base.ball_m ..).1 hi)) -- tune r.order
omit e k w'
lemma issue_same (Z:Finset Y.Col)(hp:∀ i∈Z,hide Y g i∈ V): issueW Y M T θ p u t h x Z=issueW Y M T θ p u t h x' Z:=by unfold issueW Night.Design.long; split; apply Night.Design.part _ (fun i hi=> a.sev i (hp i hi)); exact rfl
omit a
include e k
lemma burn_c (d:thin C y≤mA y)(v:Ink K C y)(w:q.threshold=thresh y)(j:y≤2*β)(r:StampC P c Y.short M R κ y)(k':b∈x.sev): burn Y S M T θ β p u t h q x b ≤ -bill_c c Y.short κ y β:= Pricing.Model.regard K P c M R κ y Y T p u t h x.sev x.gauss (Pawn.put S x y T θ p.X) q x.gap b v w k d e.2.2.2 (Y.mix_field ..) e.2.1 e.1 r k' j -- tune
omit e k
-- Tail receipt prepared for lift, group if more precision than needed.
abbrev halfC (d:ℕ)(M:ℝ→ℕ)(c:Clip)(R y:ℝ):=rC c d M R y/2
lemma w_toll : Toll id (zCost Y M T θ p u t h) (halfC Y.short M c R y) (tPay c Y.short M R y):=(Weights.issueD Y _ _ _ p u t h).tail_pay (Model.issued ..) (rC_p ..).le
lemma w_roots (Z:Finset Y.Col)(q:zCost Y M T θ p u t h Z≠0) : Z.Nonempty ∧ (Gauss.base Y).C Z:=by
 let V:=issueD Y _ _ _ p u t h; unfold zCost Night.Design.costs at q; split at q; exact (V.nont Z q).symm; exact False.elim (q rfl)
end YM.CF.BProof.Weights
