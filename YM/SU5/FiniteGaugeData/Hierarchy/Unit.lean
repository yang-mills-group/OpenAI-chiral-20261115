import YM.SU5.FiniteGaugeData.Hierarchy.Salary

/-! For the whole INPUT unit ball, common approximation independent of election indices. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "T₀"=> plaza (Λ:=Λ) S
local notation "W₀"=> GridStep Λ l S
local notation "K₀"=> (VolumeCape.Dream.plot l).K
local notation "μ₀"=> Common.law C₀ T₀

abbrev Orb := {x:Catalog S// ‖x‖≤1}

local notation "Xₐ" => Orb S
-- scale all moments before approximation.
private def tossed (Λ:Preparation)(l:ℕ)(S:Finset Cover)(z:ℝ)(x:Orb S):Key S × Courses (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S)→ Hall (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S)→ℂ := fun i t=> (z:ℂ) * amount (Dream.plot l).C (Dream.plot l).K (plaza (Λ:=Λ) S) (source S x.val i.1) i.2 t
local notation "U" => Key S × Courses C₀ T₀
local notation "D" => Hall C₀ T₀
lemma owed_toss (x:Orb S) {e:ℝ}(q:0≤e) : owe μ₀ (tossed Λ l S e) x≤ (Fintype.card (Key S × Courses C₀ T₀):ℝ)*e:=by
  refine (Finset.sum_le_sum (f:=fun i:U=>∫ z, ‖tossed Λ l S e x i z‖∂μ₀) (g:=fun _=>e) ?_).trans (by rw [sum_const,card_univ,nsmul_eq_mul])
  intro i _
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun x=>norm_nonneg _) (integrable_const (μ:=μ₀) e) (Eventually.of_forall fun y=>?_)) (by simp)
  unfold tossed; dsimp only; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg q]; refine mul_le_of_le_one_right q ?_; exact ((catalogue_norm_le S zero_le_one x.val).1 x.property) _ _

section
private lemma sum_sure {x y : Catalog S} (P:Offered Y S s i k)(e:ℝ)(q:0≤e) (h':∀ t:Key S,∀ v:Fields (side Y i (s+1)),
   ‖ingress Y s i k (Satin.knot (side Y i s) (Typeset S t) (source S x t-source S y t)) v‖ ≤ e) :
   let X:=transitionQ Y h S s ⟨(i,k),P⟩
   ‖X x - X y‖ ≤ duration S*e:=by
  intro Z; rw [← map_sub Z]
  apply (catalogue_norm_le W₀ (mul_nonneg (le_of_lt (duration_pos S)) q) _).mpr ; intro k' v
  let G:=roomy_hosp _ P.bill.upper; have he:= transition_finance Y h S s P (x-y)
  change ‖source W₀ (transitionL Y h S s P (x-y)) _ _‖ ≤ _; rw [he]
  apply (selector_n W₀ G k' _).trans; rw [ingress_compose_sum Y h S s P (x-y),Finset.sum_apply]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=>h' i _)).trans (by simp [duration]))
end

private lemma baptize {I X Z:Type*}[Fintype Z]{F:I→ Type*}[MeasurableSpace X][∀i, NormedAddCommGroup (F i)](g:Z→(i:I)→X→F i)(h:∀z, Menu (T:=F) (g z))(u:I→Z): Menu (T:=F) (fun i x=>g (u i) i x):=by
  classical
  choose c m u' using fun z=>(h z).budget
  exact ⟨Deal.assembly _ (fun z=>(h z).deal) u,∑ z,c z,sum_nonneg (fun z _=>m z),fun i x=> (u' (u i) i x).trans (single_le_sum (fun z _=>m z) (mem_univ _))⟩
private lemma debt_m : Menu (T:=fun v:Page Y S s × Key S=>FC (Single (side Y v.1.1.1.1 (s+1)))) (X:=Hall C₀ T₀) (fun (v:Page Y S s × Key S) t=> edition Y S s (Typeset S v.2) v.1 t):= baptize _ (fun i:Key S=> (upholstery Y S s (Typeset S i)).re (Prod.fst: Page Y S s × Key S→_)) Prod.snd

include h
set_option maxHeartbeats 400000 in
private lemma Offers (ε:ℝ)(p:0<ε): ∃ J:Finset (Orb S),∀ x:Orb S, ∃ y∈ J,∀ i k, Offered Y S s i k→∀ (a:Key S) (v: Fields (side Y i (s+1))),
   ‖ingress Y s i k (Satin.knot (side Y i s) (Typeset S a) (source S x.val a-source S y.val a)) v‖ ≤ ε:=by
  classical
  let C:= (Fintype.card (Key S × Courses C₀ T₀):ℝ); let e:= (C+1)⁻¹; have hC:0≤C:=by unfold C; positivity
  have hp:0<e:=inv_pos.mpr (by linarith); let Z(x:Orb S):=tossed Λ l S e x
  have hc:C*e≤1:= (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hp.le).trans (le_of_eq (mul_inv_cancel₀ (by linarith)))
  have hm(x:Orb S)(i:Key S)(r:Courses C₀ T₀):Envelope (amount C₀ K₀ T₀ (source S x.val i) r):= amount_env C₀ K₀ T₀ (Coeff.mono (x.val i).property (liner_here S _)) r
  let P(p:Page Y S s × Key S):= edition Y S s (Typeset S p.2) p.1
  have he(x:Page Y S s × Key S): Envelope (P x):= die_env ..
  obtain ⟨J,hK,w⟩:= Satin.approximate_fleet (Common.law C₀ T₀) Z (fun x v=> env_mult (f:=fun _:D=>(e:ℂ)) (Girt.rite_c _) (hm x v.1 v.2)) (debt_m Y S s) he (e*ε) (mul_pos hp p)
  refine ⟨J,fun x=>?_⟩
  obtain ⟨z,j,H⟩:=w x ((owed_toss S x hp.le).trans hc); refine ⟨z,j,fun i k p a W=>?_⟩
  have hc0:Nonempty (Courses C₀ T₀):=by
    obtain ⟨μ,hp,_,_⟩:= (Y.voyage i).craft s; exact Nonempty.map (chooseCourse C₀ T₀ (side Y i s)) (nonempty_of_isProbabilityMeasure μ)
  let N':Page Y S s:=⟨⟨(i,k),p.calendar,p.age⟩,1,(Classical.choice hc0),W⟩
  refine Satin.debt Y S s (Typeset S a) h (Satin.bracketV S a) (x:=unroll S (x.val a)) (y:=unroll S (z.val a)) N' p.bill.lower ε ?_ W
  intro t r; have he:=H (t,a) (a,r); unfold Z tossed at he; dsimp only at he; -- integral of e times diff. don't unfold institutions
  simp_rw [← mul_sub,mul_smul, integral_smul, norm_smul,Complex.norm_real, Real.norm_of_nonneg hp.le] at he; exact le_of_lt (lt_of_mul_lt_mul_left he hp.le)

lemma patrons_Q (ε:ℝ)(v:0<ε): ∃ T:Finset (Orb S),∀ (x:Orb S), ∃ y∈ T,∀ i:PaidPt Y S s, dist (transitionQ Y h S s i x.val) (transitionQ Y h S s i y.val)≤ ε:=by
  let e:= ε/(duration S)
  obtain ⟨Z,F⟩:= Offers Y h S s e (div_pos v (duration_pos _))
  refine ⟨Z,fun x=>?_⟩
  obtain ⟨z,t,L⟩:= F x; refine ⟨z,t,?_⟩
  rintro ⟨⟨i,k⟩,T⟩; rw [dist_eq_norm]; exact (sum_sure Y h S s i k T e (div_nonneg v.le (duration_pos _).le) (L i k T)).trans_eq (mul_div_cancel₀ _ (duration_pos S).ne')
#print axioms patrons_Q
end YM.CF.Buffered.Afterglow.Hierarchy
