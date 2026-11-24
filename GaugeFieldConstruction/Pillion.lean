import GaugeFieldConstruction.Cistern
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Sour.SliceRoof
open Finset Function Lattice Wilson RG Branch Skye Scree Cube Tenant Tulip Lat Rush Spire Laic
open YM.Gleam Tree Pastry Vow Rue
open Hake Jet Sault Stax
open Drapes Rill Levier Thera Urn Nacre
open scoped BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
section mass
variable {I:Type*}[Fintype I][LinearOrder I]{A B:Op I}{b c:ℝ}
lemma payFull_first (h : payFull A b)(k : payFull B c):payFull (A+B) (b+c):= ⟨fun i=>by refine le_trans (sum_le_sum (g:=fun j=> ‖A i j‖+‖B i j‖) (fun j _=>norm_add_le ..)) ?_; rw [sum_add_distrib]; exact add_le_add (h.1 _) (k.1 _),fun j=>by refine le_trans (sum_le_sum (g:=fun i=> ‖A i j‖+‖B i j‖) (fun i _=>norm_add_le ..)) ?_; rw [sum_add_distrib]; exact add_le_add (h.2 _) (k.2 _)⟩
lemma payFull_neg (h:payFull A b):payFull (-A) b:=by simpa [payFull] using h
lemma payFull_diff (h:payFull A b)(k:payFull B c):payFull (A-B) (b+c):= sub_eq_add_neg A B ▸ payFull_first h (payFull_neg k)
lemma payFull_blank (I:Type*)[LinearOrder I][Fintype I] : payFull (1:Op I) 1:=by simp [payFull,Matrix.one_apply,apply_ite]
lemma payFull_cast (h : payFull A b) (s:ℝ):payFull (s • A) (|s| *b):= by simp only [payFull,Matrix.smul_apply,norm_smul,←mul_sum,Real.norm_eq_abs]; exact ⟨fun i=>mul_le_mul_of_nonneg_left (h.1 _) (abs_nonneg _),fun i=>mul_le_mul_of_nonneg_left (h.2 _) (abs_nonneg _)⟩
lemma tall_cols (h:payFull A b) :massSite (A*B)≤ b*massSite B:=by
 unfold massSite; apply le_trans (sum_le_sum (g:=fun i:I=> ∑ j:I,∑ k:I, ‖A i k‖* ‖B k j‖) (fun i _=>sum_le_sum (fun j _=>by rw [Matrix.mul_apply]; simpa only [norm_mul] using norm_sum_le _ (fun k:I=> A i k * B k j))))
 -- rotate k, j
 have hp(i:I): ∑ j:I,∑ k:I,‖A i k‖* ‖B k j‖=(∑ k:I, ‖A i k‖* ∑ j:I, ‖B k j‖):=by rw [sum_comm]; simp_rw [mul_sum]
 simp_rw [hp]; rw [sum_comm]; rw [mul_sum]; apply sum_le_sum; intro k _; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (h.2 _) (sum_nonneg (fun i _=>norm_nonneg _))
lemma tall_rows (h:payFull A b) :massSite (B*A) ≤ b*massSite B:=by
 unfold massSite; apply le_trans (sum_le_sum (g:=fun i:I=> ∑ j:I,∑ k:I, ‖B i k‖* ‖A k j‖) (fun i _=>sum_le_sum (fun j _=>by rw [Matrix.mul_apply]; simpa only [norm_mul] using norm_sum_le _ (fun k:I=> B i k * A k j))))
 rw [mul_sum]; apply sum_le_sum; intro i _; rw [sum_comm]; simp_rw [←mul_sum]; rw [mul_sum]; apply sum_le_sum; intro j _; rw [mul_comm b]; exact mul_le_mul_of_nonneg_left (h.1 _) (norm_nonneg _)
lemma usual_mass (A:Op I) :0 ≤ massSite A:= sum_nonneg (fun i _=> sum_nonneg fun j _=>norm_nonneg _)
end mass

variable {c n:Side}{r:Ratio c (More n)}{T:Forest r}{S:Loom n}{a b d e v u t θ:ℝ}{A:Orbit n}{k m:ℕ}{H:BeatL n}{F:Elm n Unit d a b}
open Fock
lemma sworn (hp:0<d)(p:NearL F (fun _=>H))(V:Pane n) (h:Guard V d)(W:Seat n → SU.E): H (Tulip.profile (Lattice.gauge W V))=twist (tradew n W) (H (Tulip.profile V)):=by
 rw [steady _ p hp (h.cov W),steady _ p hp h,map_sum]; apply sum_congr rfl; intro i _; exact seat_rent ..
-- Bound for output at this stencil, no X cutoff assumptions outside this gauge-slice use. KEEP THIS b-h budget. A2 terms as well as total.
abbrev cliffCourt (A:Pane n)(s:Signed)(R:Ratio c (More n))(u:ℝ)(m:ℕ):= Outline R (broken R u (pull s 0 A)) (hallBill m)
private abbrev Reek (x:Pane n)(s:Signed)(r:Ratio c (More n))(t:ℝ)(m:ℕ) := (univ:Finset (Single n)).filter fun i=> affine s⁻¹ 0 (node i.1.1)∈cliffCourt x s r t m
lemma reek_size (x:Pane n)(s:Signed)(r:Ratio c (More n))(m:ℕ)(a:ℝ): (Reek x s r a m).card ≤ 180*(cliffCourt x s r a m).card:=by
 let V:=cliffCourt x s r a m; let g(i:Single n):= (affine s⁻¹ 0 (node i.1.1),i.1.2,i.2); let Q:=Reek x s r a m
 have hg:Injective g:=by
    rintro ⟨⟨i,j⟩,k⟩ ⟨⟨y,z⟩,t⟩ h
    have he: affine s⁻¹ (0:Site (More n)) (node i)=affine s⁻¹ 0 (node y):= congrArg Prod.fst h
    obtain rfl : i=y:= needle (s⁻¹.act_injective (add_right_cancel he)); obtain rfl : j=z:=congrArg (fun i=> i.2.1) h; obtain rfl : k=t:=congrArg (fun i=> i.2.2) h; rfl
 rw [← card_image_of_injective _ hg]; apply (card_le_card (show Q.image g ⊆ V×ˢ univ from image_subset_iff.mpr fun i w=>mem_product.mpr ⟨(mem_filter.mp w).2,mem_univ _⟩)).trans_eq; rw [card_product,card_univ,Fintype.card_prod, show Fintype.card SpinIdx=4 from Fintype.card_fin 4, SU.slots]; rw [Nat.mul_comm V.card]
abbrev rentK (A:Orbit n)(s:Signed)(R:Ratio c (More n))(θ v a b d:ℝ)(m:ℕ):= (Fintype.card (Single n):ℝ)* lipCharge a b d v m + (180*(cliffCourt A.1 s R θ m).card)*(b+b)
lemma pay_beam (g:NearL F (fun _=>H))(f:0<a)(y:0≤b)(w:0<d)(j:Skye.Roof n u d k S)(l:0≤θ)(p:θ ≤ u)(z:2*(r.count.val+1)<(More n).val)
 (T:Forest r)(A:Orbit n)(s:Signed)(i:k≤ m)(v₀:0 ≤ v)(uv:suitedFee r.count.val θ≤v): let U:= Loose s T A.1; let B:= S A; let E:= twist (tradew n U) (H (Tulip.profile B))- H (Tulip.profile (1:Pane n)); massSite E ≤ rentK A s r θ v a b d m:=by
 intro U B E; let G:= Lattice.gauge U B; let C:=Reek A.1 s r θ m
 let L:= lipCharge a b d v m; have h:G≠G→False:=fun z=>z rfl; let t:=H (Tulip.profile G); let P:= H (Tulip.profile (1:Pane n)); have ht : E=t-P:=by rw [show t= _ from sworn w g B (j.paid _) U];
 have hj : 0≤L:=by unfold L lipCharge; have hx:= BPress.Spin.sphereRate_cost.positive; positivity
 have hb:Guard G d:= (j.paid A).cov U; have hP:Guard (1:Pane n) d:= guard0 w.le
 have hL(x:Single n) : (∑ k:Single n, ‖E x k‖)≤ L+ if x∈C then b+b else 0:=by
    rw [ht]; split_ifs with r
    · exact ((payFull_diff (payFull_real w f g G hb) (payFull_real w f g (1:Pane n) hP)).1 x).trans (le_add_of_nonneg_left hj)
    rw [add_zero]; apply touch_column w f g G (1:Pane n) hb hP v v₀ x m _
    have hx:= span_pale (m:=m) A s j l p z i T (node x.1.1) (by by_contra he; apply r (mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,he⟩⟩))
    exact fun i v p=> (hx i v p).trans uv
 unfold massSite; apply le_trans (sum_le_sum (fun x _=> hL x)); rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero,add_zero,nsmul_eq_mul,nsmul_eq_mul,filter_mem_eq_inter,univ_inter,card_univ]; exact add_le_add_right (mul_le_mul_of_nonneg_right (show (C.card:ℝ) ≤ 180*(cliffCourt A.1 s r θ m).card from (by exact_mod_cast reek_size (A.1) s r m θ)) (by positivity : 0≤b+b)) _
lemma mass_P (j:ℕ)(M:Male)(g:NearL F (fun _=> hemi_L n j M))(f:0<a)(y:0≤b)(w:0<d)(J:Skye.Roof n u d k S)(l:0≤θ)(p:θ ≤ u)(z:2*(r.count.val+1)<(More n).val)(T:Forest r)(A:Orbit n)(s:Signed)(i:k≤ m)(v₀:0 ≤ v)(uv:suitedFee r.count.val θ≤v):
 let U:= Loose s T A.1; let B:=S A; let R:= (twist (tradew n U) (Dial.spar j M B)); payFull R (b+1/2) ∧ massSite (R-Dial.spar j M (1:Pane n)) ≤ rentK A s r θ v a b d m:=by
 intro U B R; let H:=hemi_L n j M; let P:=H (Tulip.profile B); let V:=tradew n U; let E:=halfBand n
 have ht (X:Pane n): H (Tulip.profile X)= Dial.spar j M X-E:=rfl
 have hV: twist V P = R-E:= by unfold P; rw [ht,map_sub]; unfold E halfBand; rw [map_smul,map_one]
 let X:= gauge U B; have hj : H (Tulip.profile X)=twist V P:= sworn w g B (J.paid _) U
 have hc:= payFull_real w f g X ((J.paid A).cov U)
 constructor
 · rw [show R= H (Tulip.profile X)+E from (by rw [hj,hV,sub_add_cancel])]; refine payFull_first hc ?_; have hp:=payFull_cast (payFull_blank (Single n)) (1/2); rw [abs_of_nonneg (by norm_num),mul_one] at hp; exact hp
 apply (pay_beam g f y w J l p z T A s i v₀ uv).trans'; rw [show twist (tradew _ _) _ =R-E from hV, show hemi_L n j M (Tulip.profile (1:Pane n))=_ from ht _, sub_sub_sub_cancel_right]; -- tune
lemma mass_T (p:Aim n)(g:NearL F (fun _=> Moire.bloom p))(f:0<a)(y:0≤b)(w:0<d)(J:Skye.Roof n u d k S)(l:0≤θ)(U:θ ≤ u)(z:2*(r.count.val+1)<(More n).val)(T:Forest r)(A:Orbit n)(s:Signed)(i:k≤ m)(v₀:0 ≤ v)(uv:suitedFee r.count.val θ≤v):
   massSite (twist (tradew n (Loose s T A.1)) (p.den (S A))) ≤ rentK A s r θ v a b d m:=by
 apply (pay_beam g f y w J l U z T A s i v₀ uv).trans'; rw [Moire.bloom_P,profile_trivial,Moire.bloom_zero,sub_zero]
lemma tilt_P (j:ℕ)(G:GramM n)(g:NearL F (fun _=> hemi_L n j G.J.M))(f:0<a)(y:0≤b)(w:0<d)(J:Skye.Roof n u d k S)(l:0≤θ)(p:θ ≤ u)(z:2*(r.count.val+1)<(More n).val)(T:Forest r)(A:Orbit n)(s:Signed)(i:k≤ m)(v₀:0 ≤ v)(uv:suitedFee r.count.val θ≤v) {c' a':ℝ}{E:Elm n Unit d a' c'}(e:NearL E (fun _=> Moire.bloom G.J.P))(v':0<a')(u':0 ≤ c'):
   let V:= tradew n (Loose s T A.1); let B:= twist V (Dial.spar j G.J.M (S A)); let H:= b+1/2
   payFull B H ∧ payFull (1-B) (1+H) ∧ massSite (B-Dial.spar j G.J.M (1:Pane n)) ≤ rentK A s r θ v a b d m ∧ massSite (twist V (Graph.actF j G S A)) ≤ (1+H)* (H* rentK A s r θ v a' c' d m):=by
 intro V B H; obtain ⟨ht,hg⟩:= mass_P j G.J.M g f y w J l p z T A s i v₀ uv
 have he:= payFull_diff (payFull_blank (Single n)) ht
 have hz:= mass_T G.J.P e v' u' w J l p z T A s i v₀ uv
 refine ⟨ht,he,hg,?_⟩
 unfold Graph.actF Kennel.capT; rw [map_mul,map_mul,map_sub,map_one,mul_assoc];
 apply (tall_cols he).trans; have hh:0 ≤ H:=by unfold H; positivity
 exact mul_le_mul_of_nonneg_left ((tall_rows ht).trans (mul_le_mul_of_nonneg_left hz hh)) (show 0≤1+H by positivity)
end YM.CF.Sour.SliceRoof
end
