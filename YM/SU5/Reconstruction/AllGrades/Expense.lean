import YM.SU5.Reconstruction.AllGrades.TowerUp
import YM.SU5.FiniteGaugeData.Tower.Assess
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Py Py.Rate LocalLimit Preparation Journey Vale VolumeCape
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(S:Finset Cover)(s:ℕ)
local notation "D₀" => aliasLaw Λ
local notation "C"=> (VolumeCape.Dream.plot l).C
local notation "K₀"=> (VolumeCape.Dream.plot l).K
local notation "T₀" => plaza (Λ:=Λ) S
local notation "L"=> Λ.R.L
local notation "nₛ" p:max=> side Y p s
local notation "n₁" p:max=> side Y p (s+1)

/-! Generalize Public.debt: all grades. -/
variable (u:Chorus)(H:Real.exp 1 ≤ Λ.x)(v:staves u S)
-- knot_on private Library, recreate AtSupport once through language; make it nonprivate? build dependency time minimal via local copy
include H v
private lemma page_support (f:Purse S)(i:ℕ): AtSupport (Sound.treble u) (region S (nₛ i)) (knot (nₛ i) u f.val):=by
 have ht:= (note_t (tent Y H) u f.property v).support (momentm Y i s); rw [kiosk] at ht
 exact fire (terrain Y H (Y.ir i) s) u S f.val ht
where
 fire{N M:Side}(e:N=M)(u S f)(h:AtSupport (Sound.treble u) (region S N) (knot N u f)):AtSupport (Sound.treble u) (region S M) (knot M u f):= by subst_vars; exact h
lemma lexicalDebt {x y:Purse S}(p:Page Y S s)(q:Tipping T₀ (nₛ p.1.1.1) C) (e:ℝ)(E:∀ (t:Page Y S s)(r:Courses C T₀), ‖∫ z:Hall C T₀, (amount C K₀ T₀ x.val r z - amount C K₀ T₀ y.val r z) • edition Y S s u t z∂law C T₀‖ ≤ e):
 let i:=p.1.1.1; let k:=p.1.1.2
 let X:=((Y.voyage i).X (Y.uv k)).gram
 ∀ W:Fields (side Y i (s+1)), ‖nextMark (j:=Λ.K.j) (ho:=Λ.R.odd_side) X (Y.voyage i).CapeT Chi.canonical Λ.J.d (((Y.voyage i).X (Y.uv k)).wave) (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) s (knot (side Y i s) u (x.val-y.val)) W‖ ≤ e:=by
 intro i k U A; let w: Loom (side Y i s) := (Y.voyage i).CapeT s
 have z:Dream.Haven C K₀ (side Y i s) w:=((Y.voyage i).craft _)
 let h:=Sound.pastel x.property y.property
 refine cabaret S C K₀ (nₛ i) (n₁ i) (Vale.apt (Y.ir i) Λ.block L s) (steps Λ.V (Y.ir i) Λ.block (Y.uv k) s) Λ.K.j (p.rate Y S s) (U (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (U (s+1)).beta w (Journey.legal _) ((Y.voyage i).ownership s).paid.bill ((fullness Y i k p.1.2.1).cap_grant.branch s p.1.2.2) ((algebra Y S s (h:=p)).1) ((algebra Y S s (h:=p)).2) h u (page_support Y S s u H v ⟨_,h⟩ i) A z T₀ (liner_here S _) (linen_contains ..) q e (fun F r=> ?_)
 exact E ⟨p.1,F,r,A⟩ r
end YM.CF.Buffered.Afterglow.Satin
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
open Reed (Fine think)
open Fock Pastry Tenant
namespace Garret
open Stencil Branch Tap Fock
variable (S:Finset Cover)
local notation "U₀"=> wingspan Λ l S
section chemistry
variable {J:Type*}(n k₀:J→ℕ)(p:∀i: J, legalAt Y s (n i) (k₀ i))
variable (v:Odds S)
local notation "t₀"=> tagWord S v.val
local notation "Z₀" i:max=> Y.voyage (n i)
local notation "Xs" i:max=> ((Z₀ i).X (Y.uv (k₀ i))).gram
local notation "Q₁" i:max => (((Z₀ i).X (Y.uv (k₀ i))).wave s).val
local notation "R₀" i:max=> (Z₀ i).CapeT s
local notation "A₀" i:max=> steps Λ.V (Y.ir (n i)) Λ.block (Y.uv (k₀ i)) s
local notation "μ" i:max t:max=> momentm Y (n i) t
local notation "d" i:max t:max=> side Y (n i) t
local notation "b"=> Λ.R.L
variable (h:∀i:J,Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y (n i) (s+1))))

local notation "F₀" ξ:max=>fixedStep Λ.R Λ.K.bind (fun i=>d i s) (fun i=>d i (s+1)) (kernel_sizes Y s n) ξ
include k₀
local notation "mime" i:max=> (Course.beta Y (n i) (k₀ i) s)
include p h
variable (g:J→Purse S){B:ℝ}(u:0≤B)(x:∀ i z,‖(g i).val z‖≤B)
include u x
set_option maxHeartbeats 900000 in
lemma output_doc (a:J→Odds U₀): Menu (T:=fun (_:J)=>ℂ) (fun (i:J)(z:PairsC)=> flavor U₀ K (torchBlock Y H s (n i) (k₀ i) S (note K (g i).val t₀)) (a i) z):=by
 rcases isEmpty_or_nonempty J with J' | m
 · exact Menu.congr (h:=Menu.zero) fun (i:J)=> isEmptyElim i
 have j₀:= Classical.choice m
 let Z':= Course.ceiling Λ s
 have β(i:J): |mime i|≤ Z':=abs_le.mpr (Y.seated s (n i) (k₀ i) (p i).2)
 let fees:= Λ.R0 (hat (b) Λ.x s)
 have ht(i:J): ‖Q₁ i‖ ≤ fees:= ((Y.voyage (n i)).X (Y.uv (k₀ i))).pull.tip s (p i).2
 have hx:= (Y.pilot_steps s (n j₀) (k₀ j₀)).2.2
 change (A₀ j₀).patch.Branches (A₀ j₀).kernel SU.group at hx
 rw [patch_real Y s n k₀ j₀] at hx
 have hL(i:J):Measurable (R₀ i):=((Y.voyage (n i)).ownership s).paid.bill
 let P':= (fullness Y (n j₀) (k₀ j₀) (p j₀).1).cap_grant
 obtain ⟨m'⟩:= P'.grant s (p j₀).2
 let f(i:J):= note (tent Y H) (g i).val (tagWord S v.val)
 have hf(i): InTest K true S true (f i):= by have ht:= note_t K (tagWord S v.val) (g i).property (brand S v.val); rw [v.property] at ht; exact ht
 have hf'(i:J): Envelope (knot (d i s) (t₀) (g i).val):=by
    rw [← notation_note Y H]; exact (Garret.locates Y H s (n i) (hf i)).env
 let q₀(i:J)(z:PairsC):= aboveD Y H s (n i) (k₀ i) (f i) (replant (U₀) (d i (s+1)) z)
 let W(i:J):=apt (Y.ir (n i)) Λ.block (b) s
 let Gₛ:=bead (fun i:J=>d i s) (b) (fun i=>d i (s+1)) (patch_sizes Y s n)
 have q':Menu q₀:=by
    have g:=tickets U₀ Λ.R Λ.K.bind hx Λ.K.j (aliasLaw Λ) (Journey.legal Λ) (fun i:J=>d i s) (fun i=>d i (s+1)) (patch_sizes Y s n) (fun i=>R₀ i) hL (fun i=>((Xs i) (s+1)).J.M) (fun i=>Q₁ i) ht Chi.canonical Λ.J.d m'.legal.1 m'.legal.2 (fun i=>mime i) β (fun i=> (g i).val) (t₀) u x hf'
    refine g.congr fun i v=>?_
    unfold q₀ aboveD nextMark f
    rw [show (steps Λ.V (Y.ir _) _ _ s) = F₀ i from patch_real Y s n k₀ i,notation_note Y H] -- f let
    rfl
 let t(i:J)(A:FC (Single (d i (s+1)))):= chargeOp U₀ (tent Y H) (μ i (s+1)) (h i) (terrain Y H (Y.ir (n i)) (s+1)) A (a i)
 obtain ⟨D,e,C⟩:= q'.budget
 have z':Menu (fun i z=>t i (q₀ i z)):=by
    refine ⟨q'.deal.along t ?_, D,e,fun i x=>(charged_out ..).trans (C ..)⟩
    intro δ v; refine ⟨δ,v,fun i x y h=>?_⟩; rw [dist_eq_norm] at h ⊢; unfold t; rw [← charge_jump]; exact lt_of_le_of_lt (charged_out ..) h
 refine z'.congr fun i z=> ?_
 let μ₀:=torchBlock Y H s (n i) (k₀ i) S (f i)
 have e':= possession U₀ K _ (h i) (terrain Y H (Y.ir (n i)) (s+1)) (F:=μ₀) (tBook Y H s (n i) (k₀ i) S _) (a i) z
 change t i (q₀ i z) = _
 unfold q₀
 rw [← tReserve Y H s _ _ (p i) S (hf i) (h i)]; exact e'
end chemistry

section inputDoc
open Stencil Fock
local notation "C"=> (VolumeCape.Dream.plot l).C
local notation "Z"=> (VolumeCape.Dream.plot l).K
local notation "S₊"=>Satin.plaza (Λ:=Λ) S
local notation "T" n:max=>Tipping (S₊) (side Y n s) C
local notation "R" n:max=>Tivoli (U₀) ((tent Y H).c (momentm Y n (s+1)))
variable (v:Odds S)
local notation "q₀"=> tagWord S v.val
local notation "χ" n:max k:max f:max=> torchBlock Y H s n k S (note (tent Y H) f (q₀))
local notation "P₀"=> flavor (U₀) (tent Y H)
local notation "t₀"=> Courses C (plaza (Λ:=Λ) S)
include v H
lemma payDoc (e:ℝ)(j:0<e):∃ r:Finset (Purse S),∀ (x:Purse S), Satin.price Λ l S x.val ≤ 1→∃ y∈r,∀ (n m:ℕ), legalAt Y s n m→T n→R n→∀ i:Odds (U₀),∀ z:PairsC, ‖P₀ (χ n m x.val) i z-P₀ (χ n m y.val) i z‖ ≤ e :=by
 let W:=Satin.Page Y S s
 have he(x:Purse S)(v:t₀):Envelope (Common.amount (C) (Z) (S₊) x.val v):= amount_env (C) Z (S₊) (Coeff.mono x.property (liner_here ..)) _
 obtain ⟨r,D,p⟩:= Satin.approximate_fleet (Common.law C (plaza (Λ:=Λ) S)) (fun (x:Purse S) r=> Common.amount C Z (plaza (Λ:=Λ) S) x.val r) he (Satin.upholstery Y S s q₀) (Satin.die_env Y S s q₀) e j
 refine ⟨r,fun x h=> ?_⟩
 obtain ⟨y,a,V⟩:= p x h
 refine ⟨y,a,fun n k a t r i z=>?_⟩
 let f(u:Purse S):=note K u.val (q₀)
 have hf(g:Purse S): InTest K true S true (f g):=by have ht:=note_t K (q₀) g.property (brand S v.val); rw [v.property] at ht; exact ht
 let F(g:Purse S):=torchBlock Y H s n k S (f g)
 have hF(g:Purse S) : InTest K true (U₀) true (F g):=tBook Y H s n k S _
 let μ:= momentm Y n (s+1); let N:= side Y n (s+1)
 let δ:= terrain Y H (Y.ir n) (s+1); let A:=chargeOp (U₀) K μ r δ
 let x₀:=replant U₀ N z
 have hw(g:Purse S): P₀ (F g) i z=A (aboveD Y H s n k (f g) x₀) i:= by
    rw [← tReserve Y H s n k a S (hf g) r]; exact (possession _ _ _ _ _ (hF g) i z).symm
 change ‖flavor U₀ (tent Y H) (F x) i z-P₀ (F y) i z‖≤e; rw [hw, hw]; unfold A; rw [←charge_jump]; apply (charged_out ..).trans
 -- debt paid on actual period; letter difference EXACT via grammar below transfer
 let o:PairsC→ℂ:= x.val - y.val
 have hp:note K o (q₀)=f x-f y:=by unfold o f; rw [note_minus,neg_one_smul,sub_eq_add_neg]
 have hx: aboveD Y H s n k (note K o (q₀))=aboveD Y H s n k (f x)-aboveD Y H s n k (f y):=by
    rw [hp,sub_eq_add_neg,←neg_one_smul ℂ (f y),parts_odd Y H s n k a (hf _) (.smul _ (hf _)),above_scale,neg_one_smul,sub_eq_add_neg]
 rw [← Pi.sub_apply,←hx]; unfold aboveD; rw [notation_note]
 have ha:Nonempty t₀:=by
    obtain ⟨A,hp,_,_⟩:= (Y.voyage n).craft s
    exact Nonempty.map (chooseCourse C S₊ (side Y n s)) (nonempty_of_isProbabilityMeasure A)
 let w:W:=⟨⟨(n,k),a⟩,1,Classical.choice ha,x₀⟩
 exact Satin.lexicalDebt Y S s q₀ H (brand S v.val) (x:=x) (y:=y) w t e (fun i r=> le_of_lt (V i r)) x₀

-- convert to input sup unit ball.
local notation "t'"=>Fintype.card (Courses C (plaza (Λ:=Λ) S))
lemma input_doc (e:ℝ)(j:0<e): ∃ Vₛ:Finset (Purse S), ∀ (x:Purse S), (∀y, ‖x.val y‖≤1)→∃ y∈Vₛ,∀ (n m:ℕ), legalAt Y s n m→T n→R n→∀ i:Odds (U₀),∀ z:PairsC, dist (P₀ (χ n m x.val) i z) (P₀ (χ n m y.val) i z)≤ e :=by
 let D:ℝ:=t'+1; have hp:0<D:=by unfold D; positivity
 obtain ⟨m,P⟩:= payDoc Y H s S v (e/D) (div_pos j hp)
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
 have hf(g:Purse S): InTest K true S true (f g):=by have ht:=note_t K (q₀) g.property (brand S v.val); rw [v.property] at ht; exact ht
 let rQ(g:Purse S):=flavor U₀ K (χ n k g.val)
 have hv(g:Purse S): rQ (a g) i z=(D:ℂ)*rQ g i z:=by
    unfold rQ a; rw [←Satin.vanc S K g q₀ (D:ℂ),scale_planGr Y H s n k (hf g),flavor_scale (U₀) (tent Y H) (tBook Y H ..)] -- order check
 change dist (rQ x i z) (rQ (a y) i z)≤ _
 rw [ht x,hv,hv,dist_eq_norm,←mul_sub,norm_mul, Complex.norm_real,Real.norm_of_nonneg hp.le]
 exact (mul_le_mul_of_nonneg_left (p _ _ h₁ i₀ v₀ i z) hp.le).trans_eq (mul_div_cancel₀ e hp.ne') -- dist vs norm

end inputDoc
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.output_doc
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.input_doc
