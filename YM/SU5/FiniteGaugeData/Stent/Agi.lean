import YM.CF.Buffered.Aliases
import YM.Next.FREE_KERNELS.PatchMean
/-! # extraction of actual probe coefficient on gauge block at near-site -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Stent
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "J"=> R.J
variable {x q:Cover}
private lemma multiple {L:Side}(p:wrap L x=0):∃ y:Cover,x=L.val • y:=by
 obtain ⟨y,h⟩:= cover_of_eq (n:=L) 0 x (by rw [p,map_zero]); exact ⟨y,(by rwa [zero_add] at h)⟩
def quotVec (L:Side)(x:Cover):Cover:= if h:wrap L x=0 then Classical.choose (multiple h) else 0
lemma alias_turn(p:Momentum)(L:Side)(x:Cover)(h:wrap L x=0): (∑ i:Site L,mode (aliasAt p i) x)= Fintype.card (Site L) • mode p (quotVec L x):=by
 let A:=quotVec L x; have hx:x=L.val • A:=by unfold A quotVec; rw [dif_pos h]; exact Classical.choose_spec (multiple h)
 nth_rw 1 [hx]; simp_rw [← mode_scale, alias_scale,mode_phase,mode_periodic,mul_one,sum_const,card_univ]; -- A rfl tune
 rfl
lemma alias_block(p:Momentum)(L:Side)(x:Cover)(h:wrap L x≠0): (∑ i:Site L,mode (aliasAt p i) x)=0:=by unfold aliasAt; simp_rw [mode_phase,←cell_wrap,cell_duality _ (wrap L x),←mul_sum,sum_cell h,mul_zero]
-- coefficients at Fourier. encode.
open scoped Classical -- `quotVec` problematic with decidable
abbrev funds := ((R.L.val:ℝ)^2)⁻¹ * ((Real.sqrt (R.L.val:ℝ))⁻¹) * (Fintype.card (Site R.L):ℝ)
def mark(x:Cover)(a:R.Points)(y:Cover):ℂ:= if wrap R.L (x+a.val)=0 then (if y= quotVec R.L (x+a.val) then (funds R:ℂ)*(R.weight a:ℂ) else 0) else 0
def cash (x:Cover) (y:Cover):ℂ:= ∑ a:R.Points, mark R x a y
lemma focused (x:Cover)(a:R.Points): Function.support (mark R x a) ⊆ ({quotVec R.L (x+a.val)}: Set Cover):=by intro y h; change y=_; by_contra t; apply h; unfold mark; rw [if_neg t,ite_self]
lemma robust (x:Cover): (Function.support (cash R x)).Finite:=by
 let V:=univ.image fun a:R.Points=> quotVec R.L (x+a.val); refine (V.finite_toSet).subset ?_; intro i h; by_contra t; apply h; refine sum_eq_zero fun i' _=>?_ ; by_contra k; have hp:= focused R x i' k; exact t (Finset.mem_image.mpr ⟨i',mem_univ _,(Set.mem_singleton_iff.mp hp).symm⟩) -- hp syntax? suffix.
lemma richness(p:Momentum)(x:Cover) : read (cash R x) p = ∑ l:Site (R.L), ((R.L.val:ℂ)^2)⁻¹ * mode (aliasAt p l) x * money J R.L l p:=by
 let X(a:R.Points)(p:Momentum):= (R.weight a:ℂ)*mode p a.val; have he (p:Momentum): muff J R.L p=∑ i:R.Points, X i p := (pays_roll R p).symm
 let W(a:R.Points)(p:Momentum):ℂ:= mode p (x+a.val); let K(l:Site R.L):=aliasAt p l; let C₀:ℂ:=((R.L.val:ℂ)^2)⁻¹ * (((Real.sqrt (R.L.val:ℝ))⁻¹:ℝ):ℂ); let D(a:R.Points):= C₀*(R.weight a:ℂ)
 have hb(l:Site R.L): ((R.L.val:ℂ)^2)⁻¹ * mode (K l) x * money J R.L l p=∑ i:R.Points,D i*W i (K l) :=by unfold money W; rw [he]; unfold K X D C₀; simp_rw [mode_shift,mul_sum]; refine sum_congr rfl fun i _=> ?_; ring
 have hv(a:R.Points): Summable fun i:Cover=> mode p i • mark R x a i:= summable_of_ne_finset_zero (s:={quotVec R.L (x+a.val)}) (fun i v=>by rw [show mark R x a i=0 from Function.notMem_support.mp (mt (fun h=>mem_singleton.mpr (focused R x a h)) v),smul_zero])
 unfold Laurent.read cash; simp_rw [smul_sum]; rw [Summable.tsum_finsetSum (fun i _=>hv i)]; change _=∑ i:Site R.L,((R.L.val:ℂ)^2)⁻¹*mode (K i) _ * _; simp_rw [hb]; rw [sum_comm (f:=fun l a=>D a*W a (K l))]; refine sum_congr rfl fun i _=>?_ ; rw [tsum_eq_single (quotVec R.L (x+i.val)), ←mul_sum]; swap; · intro y h; unfold mark; rw [if_neg h,ite_self,smul_zero]
 unfold mark; by_cases h: wrap R.L (x+i.val)=0; swap; · rw [show ∑ x:Site R.L,W i (K x)=0 from alias_block p R.L (x+i.val) h,if_neg h,mul_zero,smul_zero] -- args
 rw [if_pos h, if_pos rfl, show ∑ x:Site R.L,W i (K x)=_ from alias_turn p R.L _ h]; simp only [smul_eq_mul,nsmul_eq_mul,D,C₀,funds]; push_cast; ring
-- positive zero coefficient
lemma originR(a:R.Rolls):0<R.weight (R.addRoll a):=by
 have hA:0< (Fintype.card R.Rolls:ℝ):= by exact_mod_cast (show 0< Fintype.card R.Rolls from Fintype.card_pos_iff.mpr ⟨a⟩); -- tune
 unfold RG.Patch.weight; let f(t:R.Rolls):ℝ:= if R.addRoll t=R.addRoll a then (Fintype.card R.Rolls:ℝ)⁻¹ else 0; refine lt_of_lt_of_le (b:=f a) (by unfold f; rw [if_pos rfl]; exact inv_pos.mpr hA) (single_le_sum (f:=f) (fun b _=> by unfold f; split <;> positivity) (mem_univ a))
lemma price_pp (L:Side): quotVec L 0=0:=by
 let x:=quotVec L 0; unfold quotVec; rw [dif_pos (map_zero _)]; symm; let q:= @multiple (0:Cover) L (map_zero _); have hx: 0=L.val • (Classical.choose q):= Classical.choose_spec q; -- tune @parameter order
 exact Eq.symm ((smul_eq_zero.mp hx.symm).resolve_left L.property.ne') -- Nat module?
lemma price (x:Cover)(p:-x∈Lattice.box (R.L.val/2)): 0 < (cash R x 0).re :=by
 let i:Fin J:=⟨0,lt_of_lt_of_le (by decide :(0:ℕ)<4) R.order_cut⟩; let f:R.Rolls:= fun j=> if j=i then ⟨-x,p⟩ else ⟨0,center_box _⟩; let A:= R.addRoll f; have he:A.val= -x:=by
    change ∑ j:Fin J,(f j).val=_; rw [sum_eq_single i]; · simp [f]
    · intro k _ p; simp [f,p]
    exact fun g=>(g (mem_univ i)).elim
 have h:0< funds R:=by unfold funds; positivity
 unfold cash; rw [Complex.re_sum]; let W:= (mark R x A 0); have hv:0<W.re:=by unfold W mark; rw [he,add_neg_cancel,map_zero,if_pos rfl, price_pp,if_pos rfl, ←Complex.ofReal_mul]; exact mul_pos h (originR R f)
 refine hv.trans_le (single_le_sum (f:=fun a=> (mark R x a 0).re) (fun b _=>?_) (mem_univ A)); unfold mark; split_ifs; rw [←Complex.ofReal_mul]; exact mul_nonneg h.le (R.weight_nonneg _); all_goals exact le_refl _
#print axioms price
#print axioms richness
private lemma refresh {E:Type*}[Fintype E][DecidableEq E]{A: Momentum→Op E}{f:Cover→Op E}(p:Reads f A)(i j:E)(Y:Cover→ℂ)(hY: Summable (fun x=>‖Y x‖))(t:∀ p∈baseCube,Laurent.read Y p=A p i j):∀ x,f x i j=Y x:=by
 let F(x:Cover): Op E:= Matrix.of fun a b=>if a=i∧b=j then Y x else f x a b; have he(a b:E)(x:Cover):F x a b=if a=i ∧ b=j then Y x else f x a b:=rfl
 have hv:Reads F A:=by
    constructor; · intro a b; simp_rw [he]; split_ifs with H; exact hY; exact p.sumK a b
    intro z hz a b; simp_rw [he]; split_ifs with H; · rw [H.1,H.2]; exact t z hz
    exact p.readK z hz a b
 intro x; rw [Reads_u A f F p hv]; exact if_pos ⟨rfl,rfl⟩
lemma correspondent (x:Site R.L)(u v:SpinIdx)(z:Cover): tub (brix R.J R.L) z (x,u) (0,v) = (if u=v then cash R (lift x) z else 0):= by
 let f(p:Momentum):= (brix R.J R.L) p; let g:= cash R (lift x); let W(i:Cover):= if u=v then g i else 0
 apply refresh (cBrix J R.L R.odd_side) (x,u) (0,v) W _ _ z
 · by_cases h:u=v; · unfold W; simp_rw [if_pos h]; exact summable_of_ne_finset_zero (s:=(robust R (lift x)).toFinset) fun i p=>by rw [show g i=0 from Function.notMem_support.mp (fun h=>p (Set.Finite.mem_toFinset ..|>.mpr h)),norm_zero] -- tune
   unfold W; simp [h]
 intro p h; have he:= tapeB R.L p J x 0 h.1; rw [if_pos rfl, ← richness] at he
 rw [show brix R.J R.L p (x,u) (0,v)=_ from congr_fun (congr_fun he u) v]; by_cases h:u=v; swap; · unfold W; simp only [if_neg h,Matrix.smul_apply,Matrix.one_apply_ne h,smul_zero]; unfold Laurent.read; simp
 unfold W g; rw [h]; simp -- he lhs match tap def?
#print axioms correspondent
end YM.CF.Stent
