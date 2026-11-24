import YM.SU5.FiniteGaugeData.Tower.Operator
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
# TV + Fock menus -> output chart costs
-/
open Push.GridApprox Tree Next.SectorChange Stencil Tap Tenant Fock

section bouquet
variable (S:Finset Cover)(P:Patch)(Z:KernelChoices)(p:P.Branches Z SU.group)
variable {X ι:Type*}[MeasurableSpace X](c f:ι→Side)(h:∀ i,(More (f i)).val=(More (c i)).val * P.L.val)
local notation "B"=> fixedStep P Z c f h
variable (V:X→LinksC)(hv: Measurable V){w:ℝ}(β:ι→ℝ)(v:∀i, |β i|≤w)
local notation "Λ₁" i:max x:max=> Satin.graft S (f i) (V x)
include hv v p
lemma air_deck (e:ℝ)(q:0<e):∃ m:Deck X,m.dark∧∀ x y:X,m.withZ x y→∀ i:ι,
 ∫ t:Orbit (c i),‖(B i).density (β i) (Λ₁ i x) t.1-(B i).density (β i) (Λ₁ i y) t.1‖∂city _< e:=by
 let d:=patchFee P S
 let ε:= e/(d+1); have ht:0<ε:=div_pos q (by have h:0≤d:=patchFee_n P S; linarith)
 let I:=Σ i:ι,Seat (c i) × P.FrameTag
 let b:= fun i:I=> i.1
 let J:=Σ i:ι, Edge (Seat (c i)) × (Seat (c i)→P.FrameTag) × SU.E
 let t:= fun i:J=> i.1
 obtain ⟨Q,D,H⟩:= (site_deal S P Z p (c∘b) (f∘b) (fun i=>h i.1) V hv (fun i=>i.2.1) (fun i=>i.2.2)).deal ε ht
 obtain ⟨M,N,A⟩:= (link_cards S P Z p (c∘t) (f∘t) (fun i=>h i.1) V hv (β∘t) (fun i=>v i.1) (fun i=>i.2.1) (fun i=>i.2.2.1) (fun i=>i.2.2.2)).deal ε ht
 refine ⟨(Q:Finset (Set X))∪M,Q.join M D N,?_⟩; intro x y w i
 have he(i:ι)(a:Seat (c i))(g:P.FrameTag): ‖perSite (B i) (Λ₁ i x) a g-perSite (B i) (Λ₁ i y) a g‖ ≤ ε:= by
    rw [←dist_eq_norm]; exact (H x y (Deck.grow subset_union_left _ _ w) ⟨i,a,g⟩).le
 have hp(i:ι)(a:Edge (Seat (c i)))(g:Seat (c i)→P.FrameTag)(u:SU.E): ‖perLink (B i) (β i) (Λ₁ i x) g a u-perLink (B i) (β i) (Λ₁ i y) g a u‖≤ ε:=by
    rw [←dist_eq_norm]; exact (A x y (Deck.grow subset_union_right _ _ w) ⟨i,a,g,u⟩).le
 let F(V:Pane (c i)):=(B i).density (β i) (Λ₁ i x) V-(B i).density (β i) (Λ₁ i y) V
 let g:= fun t:Orbit (c i)=> ‖F t.1‖
 have hg(k):Envelope (fun t:Orbit (c i)=> (B i).density (β i) (Λ₁ i k) t.1):= Env.along (g:=Prod.fst) (slice_env (B i) (β i) p (Λ₁ i k)) measurable_fst
 have hl:Integrable g (city (c i)):= ((Env.integrableX (hg x) _).sub (Env.integrableX (hg y) _)|>.norm : _)
 change ∫ a,g a∂city (c i)<_
 rw [Scree.city,integral_prod g hl]; simp_rw [g,integral_const,probReal_univ,one_smul]
 refine lt_of_le_of_lt (stabilization S P Z p (c i) (f i) (h i) V x y _ _ ht.le (fun k _ t=> he _ k t) (fun r _=>hp _ r)) ?_
 change d*ε < _; have h₀:(d+1)*ε=e:= mul_div_cancel₀ _ (by have v:0≤d:=patchFee_n P S; linarith); linarith
end bouquet

section kits
variable(S:Finset Cover)(P:Patch)(Z:KernelChoices)(p:P.Branches Z SU.group)(j D:ℕ)(a:LaurentRadius j P.L D){I:Type*}
variable (c f:I→Side)(h:∀i,(f i).val=(c i).val*P.L.val)
variable (L:(i:I)→Loom (c i))(l':∀i,Measurable (L i))(M:I→Male)(Q:I→Op SU.Slot){w:ℝ}(σ:∀i,‖Q i‖≤w)(q:Chi)(γ:ℝ)(g:0<γ)(t:2*γ<firstRadius SU.group){z:ℝ}(β:I→ℝ)(v:∀i,|β i| ≤ z)
variable (F:I→ PairsC →ℂ)(u:Chorus){b:ℝ}(s0:0≤b)(F₀:∀i x, ‖F i x‖≤b)(X':∀i,Envelope (knot (c i) u (F i)))
local notation "G"=> bead c P.L f h
local notation "B"=> fixedStep P Z c f (fun i=> (by change (f i).val*2= (c i).val * 2 * P.L.val; rw [h i]; ring))
local notation "μ" i:max=> city (c i)
local notation "W" i:max x:max=> replant S (f i) x
include p a l' σ g t v s0 F₀ X'
set_option maxHeartbeats 700000 in
lemma tickets:Menu (T:=fun i=>FC (Single (f i))) (fun i x=> pushMark (G i) (B i) j (Q i) (M i) P.odd_side q γ (β i) (L i) (knot (c i) u (F i)) (W i x)):=by
 let A(i:I)(x:PairsC)(t:Orbit (c i)) := gathered (G i) j (Q i) (M i) P.odd_side q γ (knot (c i) u (F i)) (W i x) (drawn (L i) t)
 let O(i:I)(x:PairsC)(t:Orbit (c i)):=(B i).density (β i) (W i x).1 t.1
 have hz(i x t):0≤O i x t:=(B i).density_positive ..
 have hu(i x):Envelope (O i x):= Env.along (g:=Prod.fst) (slice_env (B i) (β i) p (W i x).1) measurable_fst
 have ht(i x): Envelope (A i x):=Env.along (g:=fun t:Orbit (c i)=>(W i x,drawn (L i) t))
    (env_gathered (G i) j (Q i) (M i) P.odd_side q γ a g t _ (X' i)) (measurable_const.prodMk (drawn_m (L i) (l' i)))
 have he(i x):∫ t,O i x t∂(μ i)=1:=by rw [Scree.city,integral_prod _ (Env.integrableX (hu i x) _)]; simp_rw [O,integral_const,probReal_univ,one_smul]; exact (B i).density_total p _ _
 let J:=Σ i:I,Orbit (c i); let b':= fun i:J=> i.1
 obtain ⟨w,B',m,e⟩:= (show Menu (T:=fun i:J=>FC (Single (f i.1))) (fun (i:J)(x:PairsC)=> A i.1 x i.2) from knot_purchase S P.L j D a P.odd_side (c∘b') (f∘b') (fun i=>h i.1) (M∘b') (Q∘b') (fun i=>σ i.1) (fun i=> drawn (L i.1) i.2) q γ g t id measurable_id u (fun i=> F i.1) s0 (fun i=>F₀ i.1))
 have e'(i x t):‖A i x t‖≤B':=e (⟨i,t⟩:J) x
 have hp(i)(x):∫ z:Orbit (c i),O i x z • A i x z∂(μ i) = pushMark (G i) (B i) j (Q i) (M i) P.odd_side q γ (β i) (L i) (knot (c i) u (F i)) (W i x):=
    (outright (G i) (B i) j (Q i) (M i) P.odd_side q γ (β i) (L i) a (l' i) p g t _ (X' i) _).symm
 simp_rw [←hp]
 constructor
 · intro ε v'; let δ:ℝ:=ε/(B'+2); have h':0<δ:=div_pos v' (by positivity)
   obtain ⟨U,H,E⟩:= w δ h'
   obtain ⟨l,F',e0⟩:= air_deck S P Z p c f (fun i=> (by change (f i).val*2= (c i).val * 2 * P.L.val; rw [h i]; ring)) (Prod.fst:PairsC→LinksC) measurable_fst β v δ h'
   refine ⟨(U:Finset _)∪l,U.join l H F',fun x y p i=>?_⟩; let ν:=city (c i)
   have hx(z):Envelope fun t:Orbit (c i)=> O i z t • A i z t:= Env.scale (hu i z) (ht i z)
   rw [dist_eq_norm,←integral_sub (Env.integrableX (hx x) ν) (Env.integrableX (hx y) ν)]; let Δ(τ:Orbit (c i)):= ‖O i x τ-O i y τ‖
   have d₀:Integrable Δ ν:= ((Env.integrableX (hu i x) _).sub (Env.integrableX (hu i y) _)).norm
   have Z₁:Integrable (fun t=>Δ t*B') ν:=d₀.mul_const _
   have Z₂:Integrable (fun t=>O i y t * δ) ν:= (Env.integrableX (hu i y) ν).mul_const _
   refine lt_of_le_of_lt (b:= ∫ t:Orbit (c i),Δ t*B'+ O i y t*δ ∂ν) ?_ ?_
   · refine (norm_integral_le_integral_norm ..).trans (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (Z₁.add Z₂) (Filter.Eventually.of_forall fun t=>?_))
     dsimp only; rw [show ∀ (a b:ℝ)(x y:FC (Single (f i))), a • x - b • y = (a-b) • x + b • (x-y) from fun a b x y=>by rw [sub_smul,smul_sub]; abel]
     apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,Real.norm_of_nonneg (hz ..)]
     exact add_le_add (mul_le_mul_of_nonneg_left (e' ..) (norm_nonneg _)) (mul_le_mul_of_nonneg_left ((show dist (A i x t) (A i y t)<δ from E x y (Deck.grow subset_union_left x y p) ⟨i,t⟩).le.trans_eq' (by rw [dist_eq_norm])) (hz ..))
   rw [integral_add Z₁ Z₂,integral_mul_const,integral_mul_const,he,one_mul]; have d₁:∫ t,Δ t∂ν <δ:=e0 x y (Deck.grow subset_union_right x y p) i
   have he': δ*(B'+2)=ε:= div_mul_cancel₀ _ (by positivity); apply lt_of_le_of_lt (b:=δ*B'+δ) (by gcongr); nlinarith
 refine ⟨B',m,fun i x=>?_⟩
 refine (norm_integral_le_integral_norm _).trans (le_trans (b:=∫ t, O i x t*B'∂(μ i)) ?_ (le_of_eq (by rw [integral_mul_const,he,one_mul])))
 refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) ((Env.integrableX (hu i x) _).mul_const _) ?_
 exact Filter.Eventually.of_forall fun t=> by dsimp only; rw [norm_smul,Real.norm_of_nonneg (hz ..)]; exact mul_le_mul_of_nonneg_left (e' ..) (hz ..)
end kits
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.tickets
