import YM.SU5.Thin.Cascade.Poetry
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {a C r e:ℝ}{n m N:Side}
open Rapids BPress.Spin
open Pressure
open YM.Gleam
variable {d v:ℝ} {w l k:ℕ} {X:Scree.Loom n}{U:Orbit n}
variable {R:Lattice.Ratio m (More n)}(T:Tree.Forest R)
open Gleam.clocks
local notation "B" x:max => (radiusB x:ℝ)
open Sleigh Paddled

abbrev uniformDebit (a:ℝ)(x:ℝ):=temp x/2+2*Real.exp (-(a*B x))
abbrev corpse (ε a C x:ℝ)(n:Side):=poet ε C a (scant x) (height x) * (180*(n.val:ℝ)^4)
abbrev crimp (ε a C x:ℝ)(w:ℕ)(r:Ratio m (More n))(U:Pane n):= corpse ε a C x n + 2*C*(180* (missed r (height x+w+1) (outerMark x) U:ℝ))
lemma tailMarc (p:0<a): Paddled (-1) (fun x=> Real.exp (-(a*B x))):= by
 apply singers; filter_upwards [tail_gone (G:=SU.group) a p] with x hx; rw [abs_of_pos (Real.exp_pos _),Real.rpow_neg_one,← neg_mul]; exact hx
lemma debitFlow (p:0<a): Paddled (-(2/5)) (uniformDebit a):=by
 have ht:Paddled (-(2/5)) temp:=(tempay (by norm_num : (0:ℝ)<1/10)).agrees (by norm_num)
 refine ((ht.scale (1/2)).add (((tailMarc p).scale 2).up (by norm_num: -(1:ℝ)≤ -(2/5:ℝ)))).agree (Eventually.of_forall ?_); intro x; change (1/2:ℝ)*_+_= _; unfold uniformDebit; ring
lemma decip (p:0<a)(e C:ℝ):Paddled (-(1/5)) (fun x:ℝ=>poet e C a (scant x) (height x)):=by
 let f(x:ℝ):= B x; have hf:Paddled (1/5) f:=by simpa only [pow_one] using radpay (by norm_num:(0:ℝ)<1/5) 1
 refine (((((tailMarc p).up (by norm_num: -(1:ℝ) ≤ -(1/5:ℝ))).scale 2).add (((hf.mul (park (-(2/5:ℝ)))).scale (4*sphereRate/e)).agrees (by norm_num))).scale C).agree (Eventually.of_forall fun x=> ?_); unfold poet; change C*(2* Real.exp (-(a*B x)) + _*(f x*scant x))=_; change C*(2* Real.exp (-(a*f x)) + _*(f x*scant x))=(2*Real.exp (-(a*f x)) +_)*_; unfold f height; ring
lemma corpse_priced (p:0<a)(ε C D:ℝ)(hp:0≤D): ∀ᶠ x:ℝ in atTop,∀ n:Side, D*corpse ε a C x n ≤ (oar x /4)* (Fintype.card (Site (More n))):=by
 filter_upwards [ (((decip p ε C).scale (D*180))).discounts (b:=-(1/500:ℝ)) (by norm_num) (by norm_num : (0:ℝ)<1/4),eventually_gt_atTop (0:ℝ) ] with x h e n
 have hx:0 ≤ (oar x):=(shinyH x e).2.2.2.le; have hl: (1/4:ℝ)*oar x≥ _:= (show D*180*poet ε C a (scant x) (height x) ≤ _ from (le_abs_self _).trans h)
 have hp' : (n.val:ℝ)^4 ≤ (Fintype.card (Site (More n)):ℝ):= by rw [site_card,Nat.cast_pow]; apply pow_le_pow_left₀ (by positivity) _; exact_mod_cast (show n.val ≤ (More n).val from Nat.le_mul_of_pos_right _ two_pos)
 unfold corpse; linarith only [mul_le_mul_of_nonneg_right hl (show 0≤ (n.val:ℝ)^4 by positivity),mul_le_mul_of_nonneg_left hp' hx]
-- numeric budgets against wall
lemma blockDuty(L:Side)(A:ℝ)(p:0 ≤ A): ∀ᶠ x:ℝ in atTop,∀ k:ℕ,starSpan x k L→A*(k:ℝ)^4 ≤ ledge x/2:= by
 have h:= (( (( (park (1/200:ℝ)).scale (2*L.val)).power 4).scale A)).discounts (b:=3/100) (by norm_num) (by norm_num:(0:ℝ)<1/2)
 filter_upwards [h] with x h k z; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) z.2 4) p); exact (le_abs_self _).trans (h.trans_eq (by unfold ledge; ring))
lemma hemming {A:ℝ}(p:0≤A) (L:Side)(w:ℕ) : ∀ᶠ x:ℝ in atTop,∀ (t:Side), starSpan x t.val L → Odd t.val → let l':=height x+w+1; l' ≤ t.val/2 ∧ A*largerBill t.val l' ≤ (oar x/4)*(t.val:ℝ)^4:=by
 filter_upwards [Work.E08.eventual_radiusB (w+2),slip L,( ((radpay (by norm_num : (0:ℝ)<1/500) 1).scale (32*A))).discounts (b:=3/1000) (by norm_num) (by norm_num:(0:ℝ)<1/4),eventually_gt_atTop (0:ℝ)] with x H h L t n p' q l
 let u:=height x; have hu:l≤ hallBill (height x):= by unfold hallBill Sequest l height; omega
 have hz:l≤ n.val/2:= hu.trans (h _ p'); refine ⟨hz,?_⟩
 let N:ℝ:=n.val; have hi:0≤N:= Nat.cast_nonneg _
 have hc:(l:ℝ) ≤ 4*B x:=by exact_mod_cast (show l ≤ 4*radiusB x by unfold l height; omega)

 have he(x:ℝ)(p:0<x): x^(3/1000:ℝ)=oar x*averge x:=by unfold oar averge; rw [←Real.rpow_add p]; norm_num
 have hp: 32*A*(B x) ≤ (oar x/4)*N:=by
    rw [pow_one,he x t] at L; apply ( (le_abs_self _).trans L) |>.trans; have hs:= (shinyH x t).2.2.2; exact (mul_le_mul_of_nonneg_left p'.1 (show 0 ≤ oar x/4 by positivity)).trans' (le_of_eq (by ring))
 refine (mul_le_mul_of_nonneg_left (wall_cheap q hz) p).trans ?_; have hg:0≤A*N^3:=by positivity
 change A*(8*l*N^3)≤oar x/4*N^4; nlinarith only [mul_le_mul_of_nonneg_right hp (show 0≤N^3 by positivity),mul_le_mul_of_nonneg_right hc hg]
lemma coreShot (p:0<a)(ε C D:ℝ)(c:0≤C)(d:0≤D)(L:Side)(w:ℕ) : ∀ᶠ x:ℝ in atTop,∀ {m n:Side}(r:Ratio m (More n)), starSpan x r.count.val L → Odd r.count.val → let t:=height x+w+1; t ≤ r.count.val/2 ∧∀ U:Pane n,D*crimp ε a C x w r U ≤ (oar x/2)*(Fintype.card (Site (More n)):ℝ)+(ledge x/2)*(misdemean (outerMark x) U).card:=by
 let F:=D*360*C; have hf:0 ≤ F:= by unfold F; positivity; -- indent
 filter_upwards [hemming hf L w, blockDuty L (F*21^4) (by positivity),corpse_priced p ε C D d] with x hv he h; intro m n r l q t
 obtain ⟨ht,H⟩:= hv r.count l q; refine ⟨ht,fun U=>?_⟩; let A:=broken r (outerMark x) U; let b:= ((misdemean (outerMark x) U).card:ℝ)
 let N:ℝ:= Fintype.card (Site (More n)); let M:ℝ:=Fintype.card (Site m); let B₀:ℝ:=r.count.val
 have hg: (A.card:ℝ)≤ b*21^4:=by unfold b; exact_mod_cast Gleam.broken_charge (r:=r) (U:=U) (t:=outerMark x)
 let V:=oar x/4; have hN: N=M*B₀^4:= by unfold N M B₀; rw [site_card,site_card,r.exact_size]; push_cast; ring
 have hy: (missed r t (outerMark x) U:ℝ) = M*(largerBill r.count.val t:ℝ)+A.card*B₀^4:=by unfold missed surfaceBill M A B₀; push_cast; simp [card_empty]
 unfold crimp; rw [show (_ : ℝ) = M*(_ : ℝ)+A.card*B₀^4 from hy] -- tune
 let z:= (largerBill r.count.val t:ℝ); have hm: F * M*z ≤ V * N:=by rw [hN]; have he:= mul_le_mul_of_nonneg_left H (show 0≤ M by unfold M; positivity); change M* (F*z)≤ M*(V*B₀^4) at he; linarith only [he]; -- tune
 have hl:F*A.card* B₀^4 ≤ ledge x/2*b:=by
    have hn: F*21^4*B₀^4≤ _:= he r.count.val l; have hw:0 ≤ b:=by unfold b; positivity
    linarith only [mul_le_mul_of_nonneg_left hg (show 0≤F*B₀^4 by positivity),mul_le_mul_of_nonneg_right hn hw]
 let Y:= corpse ε a C x n; change D*(Y+2*C*(180*(M*z+A.card*B₀^4))) ≤ _*N + _ *b; have hh:D*Y≤ V*N:= h n; unfold F V at *; linarith only [hl,hm,hh]

end YM.CF.Pannier.Chancel