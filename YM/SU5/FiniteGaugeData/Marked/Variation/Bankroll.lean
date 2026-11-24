import YM.SU5.FiniteGaugeData.Marked.Variation.Opera

/-! # Compact tariffs via finite Borel questions on the common input, even
for variable Fock spaces. Nothing needed of sup convergence on product topology. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange
open Common
attribute [local instance] opCStarAlgebra
section
variable {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
variable (P:Deck X)
namespace Deck
abbrev Sign := (s:(show Finset _ from P))→Bool
def idT (x:X):P.Sign:= fun s=> decide (x ∈ (s.val))
def room (x:P.Sign):Set X:= {y| P.idT y=x}
lemma id_spec (x y:X) : P.idT x=P.idT y → P.withZ x y:=fun p s t=> by
 have he:=congrFun p (show (P:Finset _) from ⟨s,t⟩); simpa [idT] using he -- wrong ↑?
lemma ticketed (p:P.dark)(x:P.Sign): MeasurableSet (P.room x):=by
 have h: P.room x= ⋂ i:(P:Finset (Set X)),if x i then i.val else i.valᶜ:=by
    ext a; rw [Set.mem_iInter]; change (P.idT a=x) ↔ _; simp_rw [funext_iff]; apply forall_congr'; intro i; unfold idT; cases x i <;> simp
 rw [h]; apply MeasurableSet.iInter; intro i; split; exact p _ i.property; exact (p _ i.property).compl

def nib (q:X→ℂ)(x:P.Sign):ℂ:=∫ a,q a∂(μ.restrict (P.room x))
def charge(q:X→ℂ):ℝ:= ∑ x:P.Sign, ‖P.nib μ q x‖

variable {I:Type*}{V:I→Type*}[∀i,NormedAddCommGroup (V i)][∀i,NormedSpace ℂ (V i)] [∀i,NormedSpace ℝ (V i)] [∀i,IsScalarTower ℝ ℂ (V i)][∀i,MeasurableSpace (V i)][∀i,BorelSpace (V i)][∀i,SecondCountableTopology (V i)][∀i,CompleteSpace (V i)][∀i,FiniteDimensional ℂ (V i)]
lemma phase [Nonempty X] {g:(i:I)→ X→ V i}(h:Menu g)(w:∀i,Envelope (g i)):
 ∃ C:ℝ, 0≤C ∧ ∀ ε:ℝ,0< ε → ∃ P:Deck X,P.dark ∧ ∀ (f:X→ℂ), Envelope f → ∀i, ‖∫ x,f x • g i x∂μ‖ ≤ ε* (∫ x,‖f x‖∂μ)+C*P.charge μ f:=by
 -- h.budget
 obtain ⟨C,c,v⟩:=h.budget
 refine ⟨C,c,fun ε e=>?_⟩
 obtain ⟨P,p,k⟩:=h.deal ε e
 inhabit X
 let r (s:P.Sign): X := if h:(P.room s).Nonempty then Classical.choose h else default
 have m(x:X):P.idT x=P.idT (r (P.idT x)):=by
    have n:(P.room (P.idT x)).Nonempty:=⟨x,rfl⟩; unfold r; rw [dif_pos n]; exact (show _=_ from Classical.choose_spec n).symm
 refine ⟨P,p,fun f u i=>?_⟩
 let A x:= g i (r (P.idT x)); let K(s:P.Sign)(x:X):= (P.room s).indicator f x • g i (r s)
 have hK(s:P.Sign): Integrable (K s) μ:= ((Env.integrableX u μ).indicator (P.ticketed p s)).smul_const _
 have he(x):f x • A x=∑ s:P.Sign,K s x:=by
    rw [sum_eq_single (P.idT x)]; swap
    · intro s _ h; unfold K; rw [Set.indicator_of_notMem (show x∉P.room s from h.symm),zero_smul] -- indicate binder? h
    swap; · simp
    unfold K; rw [Set.indicator_of_mem (show x∈ P.room (P.idT x) from rfl)]
 have hA:Integrable (fun x=>f x • A x) μ:=by simp_rw [he]; exact integrable_finsetSum _ (fun i _=> hK i)
 let R(x:X):V i:= f x • g i x
 haveI : ProperSpace (V i):=FiniteDimensional.proper ℂ _
 have hR:Integrable R μ:=Env.integrableX (Girt.kitE _ _ (fun (x:ℂ)(a:V i)=>x • a) (by exact continuous_fst.smul continuous_snd) u (w i)) _
 have hb : ‖(∫ x,R x∂μ) -(∫ x,f x • A x∂μ)‖ ≤ ε*(∫ x,‖f x‖∂μ):=by
    rw [←integral_sub hR hA,mul_comm,←integral_mul_const]
    refine (norm_integral_le_integral_norm ..).trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _=>norm_nonneg _) ((Env.integrableX u μ).norm.mul_const _) ?_)
    apply Filter.Eventually.of_forall; intro x; change ‖ f _ • _ - _‖ ≤ _; rw [←smul_sub,norm_smul,←dist_eq_norm]; exact mul_le_mul_of_nonneg_left (k _ _ (P.id_spec x _ (m x)) i).le (norm_nonneg _)
 have hm: ‖∫ x, f x • A x∂μ‖ ≤ C*P.charge μ f:=by
    simp_rw [he]; rw [integral_finsetSum _ (fun i _=> hK i)];
    unfold charge; rw [Finset.mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun x _=>?_)
    unfold K nib; rw [integral_smul_const,norm_smul,mul_comm C, integral_indicator (P.ticketed p _)]
    exact mul_le_mul_of_nonneg_left (v ..) (norm_nonneg _)
 change ‖∫ x,R x∂μ‖ ≤ _; exact (sub_le_iff_le_add.mp ((norm_sub_norm_le _ (∫ x,f x • A x∂μ)).trans hb)).trans (add_le_add_right hm _)
end Deck
end
#check integral_smul_const
section
variable {C T S: Type*} -- S coefficient, X underlying stencil; family arbitrary of coefficient tests
variable [Fintype T][MeasurableSpace C](μ:Measure C)[IsProbabilityMeasure μ]
variable (g:S→T→ C→ ℂ)(v:∀s t,Envelope (g s t))

abbrev owe(s:S):ℝ:= ∑ i:T, ∫ x,‖g s i x‖ ∂μ
abbrev cashD(s t:S)(i:T):ℝ:=∫ x, ‖g s i x-g t i x‖ ∂μ
abbrev purseQ(s t:S)(i:T)(P:Deck C):ℝ:=P.charge μ (g s i-g t i)
lemma owes(s:S):0≤ owe μ g s:=sum_nonneg fun _ _=>integral_nonneg fun _=>norm_nonneg _
-- t ∈T bound
lemma single_owe (s:S)(i:T): (∫ x,‖g s i x‖∂μ)≤owe μ g s:= single_le_sum (f:=fun i:T=> ∫ (x:C),‖g s i x‖∂μ) (fun j _=>integral_nonneg fun x=>norm_nonneg (g s j x)) (mem_univ i)
include v
lemma tariff (s t:S)(i:T): cashD μ g s t i ≤ owe μ g s+owe μ g t:=by
 have ht(s:S):=(Env.integrableX (v s i) μ).norm
 unfold cashD
 refine (integral_mono_of_nonneg (Eventually.of_forall fun _=>norm_nonneg _) ((ht s).add (ht t)) (show Filter.Eventually _ _ from Filter.Eventually.of_forall fun x=> norm_sub_le ..)).trans ?_
 simp only [Pi.add_apply]
 rw [integral_add (ht s) (ht t)]
 exact add_le_add (single_owe ..) (single_owe ..)

lemma approximate (P:Deck C)(e:ℝ)(u:0<e):
    let X:= {s:S| owe μ g s ≤ 1}
    ∃ Z:Finset S, ↑Z⊆ X ∧ ∀s∈X,∃ t∈ Z,∀ i:T, purseQ μ g s t i P≤ e:=by
 -- moments ranges compact; finite representatives from range, total bounded approximation.
 intro X; let Y:=T × P.Sign
 -- pp? type notations; define
 let F(s:S)(i:Y):ℂ:=P.nib μ (g s i.1) i.2
 have h (s:S)(H:s∈X)(i:Y): ‖F s i‖ ≤ 1:=by -- binder wrong
    unfold F Deck.nib
    apply (norm_integral_le_integral_norm ..).trans
    apply (setIntegral_le_integral ((Env.integrableX (v s i.1) μ).norm) (Eventually.of_forall fun t=>norm_nonneg _)).trans
    exact (single_owe ..).trans H
 let A:Set (Y→ℂ):=F '' X
 have hz:TotallyBounded A:= ((ProperSpace.isCompact_closedBall (0:Y→ℂ) 1).totallyBounded).subset (by rintro v ⟨s,t,rfl⟩; rw [mem_closedBall_zero_iff]; exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> h s t i)
 let d:= (Fintype.card P.Sign:ℝ)
 have hd:0≤d:=by unfold d; positivity
 let ε:= e/(d+1); have he:0<ε:=div_pos u (by linarith)
 obtain ⟨q,t,m,w⟩:= Metric.finite_approx_of_totallyBounded hz ε he
 choose b p Q using fun a:↥q=>t a.property
 let Z:Finset S:=m.toFinset.attach.image (fun i=> b ⟨i.val,m.mem_toFinset.mp i.property⟩)
 refine ⟨Z,?_,?_⟩
 · rintro y c; obtain ⟨x,z,rfl⟩:= mem_image.mp c; exact p _
 intro s K
 have hw:= w (show F s∈ A from ⟨s,K,rfl⟩); simp only [Set.mem_iUnion] at hw
 obtain ⟨a,v',h⟩:= hw; let r:↥q:=⟨a,v'⟩
 refine ⟨b r,?_,fun i=>?_⟩
 · exact mem_image_of_mem (fun i=> b ⟨i.val,m.mem_toFinset.mp i.property⟩) (m.toFinset.mem_attach ⟨a,m.mem_toFinset.mpr v'⟩)
 rw [show a=F (b r) from (Q r).symm, mem_ball] at h
 unfold purseQ Deck.charge
 have hb(a':P.Sign): P.nib μ (g s i-g (b r) i) a'= F s (i,a')- F (b r) (i,a'):=by
    unfold F Deck.nib; simp only [Pi.sub_apply]; rw [integral_sub (Env.integrableX (v s i) _) (Env.integrableX (v (b r) i) _)]
 apply (sum_le_sum (f:=fun j=> ‖P.nib μ (g s i-g (b r) i) j‖) (g:=fun _=>ε) ?_).trans
 · simp only [sum_const,card_univ,nsmul_eq_mul]; have he:d*ε≤ (d+1)*ε:=by nlinarith
   exact he.trans (le_of_eq (mul_div_cancel₀ _ (by linarith))) -- order
 intro j _; rw [hb j,←dist_eq_norm]; exact ((dist_le_pi_dist ..).trans h.le) -- lemma
#check Set.mem_image
#check setIntegral_le_integral
#check dist_le_pi_dist
#check Finset.mem_attach
lemma approximate_fleet {I:Type*}{V:I→Type*}[∀i,NormedAddCommGroup (V i)][∀i,NormedSpace ℂ (V i)] [∀i,NormedSpace ℝ (V i)] [∀i,IsScalarTower ℝ ℂ (V i)][∀i,MeasurableSpace (V i)][∀i,BorelSpace (V i)][∀i,SecondCountableTopology (V i)][∀i,CompleteSpace (V i)][∀i,FiniteDimensional ℂ (V i)][Nonempty C]
 {F:(i:I)→C→V i}(h:Menu F)(p:∀ i,Envelope (F i)) (e:ℝ)(t:0<e):
 let B:= {s:S| owe μ g s ≤1}
 ∃ Z:Finset S, ↑Z⊆ B ∧ ∀s∈B,∃ z∈ Z, ∀ (i:I)(j:T), ‖∫ x,(g s j x-g z j x) • F i x∂μ‖ < e :=by
 obtain ⟨R,u,Q⟩:= Deck.phase μ h p
 obtain ⟨P,H,D⟩:= Q (e/4) (by linarith)
 let ε:= e/(4*(R+1)); have he:0<ε:=by unfold ε; positivity
 intro B
 obtain ⟨Z,N,v'⟩:= approximate μ g v P ε he; refine ⟨Z,N,fun s t'=>?_⟩
 obtain ⟨z,A,W⟩:=v' s t'; refine ⟨z,A,fun i j=>?_⟩
 have hu:Envelope (g s j-g z j):= Girt.kitE _ _ (fun (x y:ℂ)=> x-y) (by fun_prop) (v ..) (v ..)
 have hv:= D _ hu i; change ‖∫ x,(g _ _ x-_) • _∂_‖ ≤ _ * cashD μ g s z j + R*purseQ μ g s z j P at hv
 apply lt_of_le_of_lt hv
 have ha:=N (show z∈(Z:Set S) from A); change owe _ _ _≤ 1 at ha t'
 have hr:R*ε≤ e/4:=by
    have gu:0<4*(R+1):=by linarith
    have p:4*(R+1)*ε=e:=mul_div_cancel₀ _ gu.ne'; nlinarith
 have hp:=tariff μ g v s z j; specialize W j; nlinarith
end
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.approximate_fleet
