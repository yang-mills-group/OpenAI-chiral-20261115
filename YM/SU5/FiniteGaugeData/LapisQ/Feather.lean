import YM.SU5.FiniteGaugeData.LapisQ.Wing
/-! # Tight Fejer G grids Chroma. preserve search stencil in response lower. -/
set_option autoImplicit false
set_option maxHeartbeats 560000
set_option synthInstance.maxSize 19000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory Matrix Lattice Laurent Bloch Work.F06 Complex
open scoped Topology ComplexOrder BigOperators Classical Matrix
set_option quotPrecheck false
namespace Willow
open Vulcan
variable {n:Side}(J:ℕ)(a:Axis){v d:ℕ}{x:Site n}
local notation "S" => Site n
local notation "R"=> Per n
-- orientation.B_range
abbrev signature(J:ℕ)(n:Side): Finset (Per n):= (range J).image (fun i:ℕ=> (i:Per n))
lemma enter_sign (i:R) (hl:v < n.val) : i∈signature v n↔i.val<v:=by
 rw [signature,mem_image]; refine ⟨fun p=>?_,fun h=> ⟨i.val,mem_range.mpr h, ZMod.natCast_zmod_val ..⟩ ⟩; obtain ⟨i,p,rfl⟩:=p; have v:=mem_range.mp p; rw [ZMod.val_natCast_of_lt (v.trans hl)]; exact v
lemma fee_sig(p:v<n.val): (signature v n).card=v:=by
 rw [signature,card_image_of_injOn,card_range]; intro i t j t' δ; have hx:= congrArg ZMod.val δ; rw [ZMod.val_natCast_of_lt ((mem_range.mp t).trans p),ZMod.val_natCast_of_lt ((mem_range.mp t').trans p)] at hx; exact hx
abbrev acreage (J:Axis→ℕ)(n:Side): Finset (Site n):=Fintype.piFinset fun a=> signature (J a) n
lemma acre_mem(A:Axis→ℕ)(p:∀ a,A a<n.val): x∈acreage A n↔∀i,(x i).val<A i:= by unfold acreage; rw [Fintype.mem_piFinset]; apply forall_congr' fun i=> enter_sign (x i) (p i)
lemma acre_size (A:Axis→ℕ)(p:∀ a,A a<n.val) : (acreage A n).card=∏ i,A i:=by rw [acreage,Fintype.card_piFinset]; exact prod_congr rfl fun _ _=>fee_sig (p _)
abbrev blockK(J:ℕ)(n:Side):=acreage (fun _=>J) n
lemma block_size (u:v<n.val): (blockK v n).card=v^4:=by rw [blockK,acre_size _ (fun _=> u),prod_const,card_univ]; rfl
lemma block_bled(u:v<n.val): x∈blockK v n ↔ ∀ i,(x i).val<v:=acre_mem _ (fun _=>u)
abbrev hatch (A:Finset (Site n))(x:Site n):= A.filter (fun o=>o+x∈ A)
variable {r:ℕ}
lemma wallH (h:r+1<n.val)(j:Axis): let A:=blockK (r+1) n; (hatch A (step j)).card= r*(r+1)^3:=by
 intro A; let w(i:Axis):= if i=j then r else r+1; have hw(i:Axis):w i<n.val:= (show w i≤r+1 from (by unfold w; split <;> omega)).trans_lt h
 have hx(x:Site n)(p:x∈A): (x+step j)∈A ↔ x∈ acreage w n:=by
    let f:= x j; have hb(i:Axis):= (block_bled h).1 p i; unfold A; rw [block_bled h, acre_mem w hw]; apply forall_congr'; intro i; by_cases e:i=j; swap; · simp [w,(show i≠j from e)]; -- tune step_apply
    subst i; have he:1<n.val:=by omega
    rw [Pi.add_apply, step_apply, if_pos rfl, ZMod.val_add, ZMod.val_one_eq_one_mod,Nat.add_mod_mod,Nat.mod_eq_of_lt (show (x j).val+1<n.val from (by have he:=hb j; omega)),show w j=r from if_pos rfl]; omega
 have hf:hatch A (step j)=acreage w n:=by
    ext i; rw [mem_filter]; refine ⟨fun h=> (hx i h.1).1 h.2,fun h'=> ⟨?_,?_⟩⟩; all_goals try rw [hx i] <;> try assumption
    all_goals (apply (block_bled h).2; intro j; have hz:= (acre_mem w hw).1 h' j; unfold w at hz; split at hz <;> omega)
 rw [hf, acre_size w hw,← mul_prod_erase univ w (mem_univ j)]; rw [show w j=r from if_pos rfl]; congr 1; apply (prod_congr rfl (g:=fun _=> r+1) (fun i p=> (show w i=r+1 from if_neg (mem_erase.mp p).1))).trans ?_; rw [prod_const, card_erase_of_mem (mem_univ _),card_univ]; rfl
-- mask kernel.Facts
noncomputable def glowK (A:Finset (Site n))(p:Site n):ℝ:= ‖∑ x ∈ A,cell p x‖^2
variable (A:Finset (Site n))(p:Site n)
lemma lightK :0≤glowK A p:=sq_nonneg _ -- remove attr
lemma flash : (glowK A p:ℂ)=∑ x∈A,∑ y∈ A, cell p x* (cell p y)⁻¹:=by
 rw [glowK, ← normSq_eq_norm_sq,normSq_eq_conj_mul_self]; rw [mul_comm]; simp_rw [map_sum, cell_bar, sum_mul,mul_sum] -- ambiguity
lemma padK(x:Site n) : (∑ u:Site n,(glowK A u:ℂ)*cell u x)= ((hatch A x).card:ℂ)*(n.val:ℂ)^4:=by
 simp_rw [flash,sum_mul]; rw [Finset.sum_comm]; let X:= (n.val:ℂ)^4
 have he(a:Site n): (∑ u:Site n,∑ x'∈A,cell u a*(cell u x')⁻¹*cell u x)=if a+x∈A then X else 0:=by
    rw [sum_comm]; have ht(o): (∑ u:Site n,cell u a* (cell u o)⁻¹*cell u x)= if a+x=o then (n.val:ℂ)^4 else 0:=by
       conv_lhs => arg 2; intro u; rw [mul_right_comm, ← cell_add, cell_duality, cell_duality u o]
       exact orthogonal ..
    simp_rw [ht,sum_ite_eq]; rfl
 simp_rw [he, ← sum_filter,sum_const,nsmul_eq_mul]; rfl
lemma watt(h:r+1<n.val): let J:=blockK (r+1) n;(∑ p:Site n, glowK J p)= ((r:ℝ)+1)^4 * (n.val:ℝ)^4:=by
 intro J; have he:= padK J 0; simp only [cell_origin,mul_one,←Complex.ofReal_sum] at he; rw [show hatch J 0=J from Finset.ext (by simp [hatch]), show J.card=(r+1)^4 from block_size h] at he; exact_mod_cast he
-- normalize, uniform distribution in rational Mask.
def litK(n:Side)(r:ℕ):ℝ:= ((r:ℝ)+1)^4*(n.val:ℝ)^4
lemma lit_p:0<litK n r:=mul_pos (by positivity) (pow_pos (side_pos n) 4)
noncomputable abbrev windK(r:ℕ)(x:Site n):= glowK (blockK (r+1) n) x / litK n r
lemma wind_p : 0 ≤ windK r p:= div_nonneg (lightK _ _) lit_p.le
lemma wind_sum (h:r+1<n.val) : (∑ p:Site n, windK r p)=1:=by unfold windK; rw [←sum_div,watt h]; exact div_self (lit_p (r:=r) (n:=n)).ne'
noncomputable def cropE (r:ℕ)(f: Site n→ℂ) := ∑ p:Site n,(windK r p:ℂ)* f p
lemma copA (h:r+1<n.val): cropE r (fun (_:Site n)=> (1:ℂ))=1:=by unfold cropE; simp_rw [mul_one,← ofReal_sum,wind_sum h,Complex.ofReal_one]
lemma critic (p:Site n) : cropE r (fun x => cell x p) = ((litK n r:ℂ))⁻¹ * (((hatch (blockK (r+1) n) p).card:ℂ)*(n.val:ℂ)^4):=by
 unfold cropE windK; simp_rw [ofReal_div, div_eq_mul_inv,mul_comm _ ((litK n r:ℂ))⁻¹,mul_assoc, ← mul_sum, padK]
lemma press (h:r+1<n.val)(j:Axis): cropE r (n:=n) (fun x=> cell x (step j))= ((r:ℂ)/(r+1)):=by -- tune
 rw [critic, wallH h]; unfold litK; have hx:((r:ℂ)+1)≠0:=by exact_mod_cast (by omega : r+1≠0)
 have hp:=side_ne n; push_cast; field_simp
lemma weft (h:r+1<n.val)(j:Axis): (∑ x:Site n,windK r x* ‖Exterior.q (mon x) j‖^2)= 2/(r+1:ℝ) :=by
 let f(x:Site n):=cell x (step j); let A(x:Site n):= windK r x; have he(x:Site n): Exterior.q (mon x) j=f x-1:=by unfold f Exterior.q; rw [cell_step]
 have hr(x:Site n): ‖f x-1‖^2=(2-2*(f x).re):=by
    have hx:= cell_pay x (step j); have hy:(f x).re * (f x).re+ (f x).im * (f x).im=1:=by rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq,show ‖f x‖=1 from hx]; ring
    rw [←normSq_eq_norm_sq,normSq_apply,Complex.sub_re,Complex.sub_im,one_im,one_re]; linarith
 have ht:= congrArg Complex.re (press h j); change (∑ x:Site n,(A x:ℂ)*f x).re=_ at ht; rw [Complex.re_sum,show (r:ℂ)/(r+1)= (Complex.ofReal ((r:ℝ)/(r+1))) from (by push_cast; rfl)] at ht; simp only [Complex.mul_re,Complex.ofReal_re, Complex.ofReal_im,zero_mul, sub_zero] at ht
 simp_rw [he,hr,mul_sub, mul_left_comm (windK r _) (2:ℝ), Finset.sum_sub_distrib, ←sum_mul, ←mul_sum,wind_sum h]; rw [show (∑ x:Site n,_)=_ from ht]; have hv: (r:ℝ)+1≠0:= (by positivity); field_simp; ring
-- cheer
end Willow
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Willow.weft
