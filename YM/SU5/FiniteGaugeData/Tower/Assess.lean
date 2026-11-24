import YM.SU5.FiniteGaugeData.Tower.Assembly
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Input side (operator version of the argument for Satin.patrons in Public.lean)

At the same fixed S as the input (periods eventually fitting S's required
pad at s). Gives genuinely finite representative costs on the transfer map
itself, not just the cost after inserting into the ratio. As in `patrons`,
pay on Hall panels prior to conditional integration, so holds for real Loom
and period color laws without matching either to the upper-period reading nor
changing distribution!
-/
open Stencil Fock
variable (S:Finset Cover)
local notation "C"=> (VolumeCape.Dream.plot l).C
local notation "Z"=> (VolumeCape.Dream.plot l).K
local notation "S₊"=>Satin.plaza (Λ:=Λ) S
local notation "U₀"=>wingspan Λ l S
local notation "T" n:max=>Tipping (S₊) (side Y n s) C
local notation "R" n:max=>Tivoli (U₀) ((tent Y H).c (momentm Y n (s+1)))
variable (v:Evens S)
local notation "q₀"=> tagWord S v.val
local notation "χ" n:max k:max f:max=> block Y H s n k S (note (tent Y H) f (q₀))
local notation "P₀"=> banner (U₀) (tent Y H)
local notation "t₀"=> Courses C (plaza (Λ:=Λ) S)
lemma admit_event : ∀ᶠ i:ℕ in atTop,T i ∧ R i:=by
 filter_upwards [(Journey.momentum Y s).eventually (separates K (tips (Common.porch C (plaza (Λ:=Λ) S)))), (Journey.momentum Y (s+1)).eventually (separates K (tips U₀))] with r p q
 change Set.InjOn _ _ at p; rw [terrain Y H (Y.ir r) s] at p; exact ⟨p,⟨⟨q⟩⟩⟩
include v H
lemma recruit (e:ℝ)(j:0<e):∃ r:Finset (Purse S),∀ (x:Purse S), Satin.price Λ l S x.val ≤ 1→∃ y∈r,∀ (n m:ℕ), legalAt Y s n m→T n→R n→∀ i:Evens (U₀),∀ z:PairsC, ‖P₀ (χ n m x.val) i z-P₀ (χ n m y.val) i z‖ ≤ e :=by
 let W:=Satin.Page Y S s
 have he(x:Purse S)(v:t₀):Envelope (amount (C) (Z) (S₊) x.val v):= amount_env (C) Z (S₊) (Coeff.mono x.property (liner_here ..)) _
 obtain ⟨r,D,p⟩:= Satin.approximate_fleet (Common.law C (plaza (Λ:=Λ) S)) (fun (x:Purse S) r=> amount C Z (plaza (Λ:=Λ) S) x.val r) he (Satin.upholstery Y S s q₀) (Satin.die_env Y S s q₀) e j
 refine ⟨r,fun x h=> ?_⟩
 obtain ⟨y,a,V⟩:= p x h
 refine ⟨y,a,fun n k a t r i z=>?_⟩
 let f(u:Purse S):=note K u.val (q₀)
 have hf(g:Purse S): InTest K true S false (f g):=by have ht:=note_t K (q₀) g.property (brand S v.val); rw [v.property] at ht; exact ht
 let F(g:Purse S):=block Y H s n k S (f g)
 have hF(g:Purse S) : InTest K true (U₀) false (F g):=booked Y H s n k S _
 let μ:= momentm Y n (s+1); let N:= side Y n (s+1)
 let δ:= terrain Y H (Y.ir n) (s+1); let A:=paintOp (U₀) K μ r δ
 let x₀:=replant U₀ N z
 have hw(g:Purse S): P₀ (F g) i z=A (aboveD Y H s n k (f g) x₀) i:= by
    rw [← reserved Y H s S n k a (hf g) r]; exact (delivery _ _ _ _ _ (hF g) i z).symm
 change ‖banner U₀ (tent Y H) (F x) i z-P₀ (F y) i z‖≤e; rw [hw, hw]; unfold A; rw [←paint_jump]; apply (charged_cast ..).trans
 -- debt paid on actual period; letter difference EXACT via grammar below transfer
 let o:PairsC→ℂ:= x.val - y.val
 have hp:note K o (q₀)=f x-f y:=by unfold o f; rw [note_minus,neg_one_smul,sub_eq_add_neg]
 have hx: aboveD Y H s n k (note K o (q₀))=aboveD Y H s n k (f x)-aboveD Y H s n k (f y):=by
    rw [hp,sub_eq_add_neg,←neg_one_smul ℂ (f y),above_parts Y H s n k a (hf _) (.smul _ (hf _)),above_scale,neg_one_smul,sub_eq_add_neg]
 rw [← Pi.sub_apply,←hx]; unfold aboveD; rw [notation_note]
 have ha:Nonempty t₀:=by
    obtain ⟨A,hp,_,_⟩:= (Y.voyage n).craft s
    exact Nonempty.map (chooseCourse C S₊ (side Y n s)) (nonempty_of_isProbabilityMeasure A)
 let w:W:=⟨⟨(n,k),a⟩,1,Classical.choice ha,x₀⟩
 exact Satin.debt Y S s q₀ H (bracketV S v) (x:=x) (y:=y) w t e (fun i r=> le_of_lt (V i r)) x₀

-- convert to input sup unit ball.
local notation "t'"=>Fintype.card (Courses C (plaza (Λ:=Λ) S))
lemma finance_inputs (e:ℝ)(j:0<e): ∃ Vₛ:Finset (Purse S), ∀ (x:Purse S), (∀y, ‖x.val y‖≤1)→∃ y∈Vₛ,∀ (n m:ℕ), legalAt Y s n m→T n→R n→∀ i:Evens (U₀),∀ z:PairsC, dist (P₀ (χ n m x.val) i z) (P₀ (χ n m y.val) i z)≤ e :=by
 let D:ℝ:=t'+1; have hp:0<D:=by unfold D; positivity
 obtain ⟨m,P⟩:= recruit Y H s S v (e/D) (div_pos j hp)
 let a:= fun x:Purse S=>Satin.hue S x (D:ℂ)
 let b:= fun x:Purse S=>Satin.hue S x (D:ℂ)⁻¹
 have ht(x:Purse S): x=a (b x):=by apply Subtype.ext; funext i; change _=(D:ℂ)*((D:ℂ)⁻¹*_); rw [mul_inv_cancel_left₀ (by exact_mod_cast hp.ne')]
 refine ⟨m.image a,fun x h=>?_⟩
 have hx(i):‖(b x).val i‖ ≤ D⁻¹:=by change ‖(D:ℂ)⁻¹ * _‖≤_; rw [norm_mul,norm_inv,Complex.norm_real, Real.norm_of_nonneg hp.le]; exact mul_le_of_le_one_right (by positivity) (h i)
 have h0:Satin.price Λ l S (b x).val ≤ 1:=by
    unfold Satin.price Touch Common.touch Common.amount; refine (sum_le_sum (g:=fun (_:Courses C (plaza (Λ:=Λ) S))=> D⁻¹) (fun i _=> (integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _) (integrable_const _) (Eventually.of_forall fun j=> hx _)).trans_eq (by simp))).trans ?_
    rw [sum_const,card_univ,nsmul_eq_mul]; have ht : D * D⁻¹ = 1:=mul_inv_cancel₀ hp.ne'; rw [←ht] -- tune
    unfold D; gcongr; linarith
 obtain ⟨y,r,p⟩:= P (b x) h0; refine ⟨a y, Finset.mem_image_of_mem a r,fun n k h₁ i₀ v₀ i z=>?_⟩
 let f(g:Purse S):=note K g.val (q₀)
 have hf(g:Purse S): InTest K true S false (f g):=by have ht:=note_t K (q₀) g.property (brand S v.val); rw [v.property] at ht; exact ht
 let rQ(g:Purse S):=banner U₀ K (χ n k g.val)
 have hv(g:Purse S): rQ (a g) i z=(D:ℂ)*rQ g i z:=by
    unfold rQ a; rw [←Satin.swindle S K g q₀ (bracketV S v),scale_scheme Y H s n k (hf g),banner_scale (U₀) (tent Y H) (booked Y H ..)] -- order check
 change dist (rQ x i z) (rQ (a y) i z)≤ _
 rw [ht x,hv,hv,dist_eq_norm,←mul_sub,norm_mul, Complex.norm_real,Real.norm_of_nonneg hp.le]
 exact (mul_le_mul_of_nonneg_left (p _ _ h₁ i₀ v₀ i z) hp.le).trans_eq (mul_div_cancel₀ e hp.ne') -- dist vs norm

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.recruit
#print axioms YM.CF.Buffered.Afterglow.Tower.finance_inputs
