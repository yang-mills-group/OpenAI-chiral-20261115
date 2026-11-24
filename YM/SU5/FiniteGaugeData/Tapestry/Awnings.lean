import YM.SU5.FiniteGaugeData.Tapestry.Stipple
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Local perturbation estimates for the actual conditional laws

No estimate on a logarithm of the complex *reading*. This estimate is on the
conditional probabilities in `advance`; remarkably a pointwise ratio bound can be
used even on the growing tori. It only compares two upper fields *grafted to same fixed support*.
No singularity or zero test on final signed densities is assumed or concluded here.
-/
open Push.GridApprox
section finance
variable (S:Finset Cover)(N M:Side)(G:StepData M (More N))
    (ab : G.patch.Branches G.kernel SU.group)
local notation "r"=> Push.GridApprox.reach G.patch

def patchTouches : Finset (Site M) := Finset.univ.filter (fun b=> ∃ x∈S, wrap (More N) x∈ Push.GridApprox.window (G.ratio.embed b) (reach G.patch))
local notation "s"=>patchTouches S N M G
lemma outside_agree (x y: PairsC)(b:Site M)(p:b∉s): Agrees (Push.GridApprox.window (G.ratio.embed b) r) (grafted S x N) (grafted S y N):= by
  rintro ⟨a,i⟩ t u; change a∈ _ at t; have h : ¬∃ q:S,pole S N q=a:=by
    rintro ⟨q,rfl⟩; exact p (mem_filter.mpr ⟨mem_univ _,q.val,q.property,t⟩)
  unfold grafted Satin.graft; rw [dif_neg h,dif_neg h]
lemma count_touched : (s).card ≤ S.card * (Lattice.box r).card:=by
  let U:= S ×ˢ Lattice.box r
  let Q(u:Cover×Cover): Seat N:= wrap (More N) u.1- wrap (More N) u.2
  have h:(s).image G.ratio.embed ⊆ U.image Q := by
    intro x hx; obtain ⟨b,e,rfl⟩:= mem_image.mp hx
    obtain ⟨y,a,v,B,w⟩:= (mem_filter.mp e).2
    refine mem_image.mpr ⟨(y,v), mem_product.mpr ⟨a,B⟩,?_⟩
    unfold Q; dsimp only; rw [show (wrap _ y)=_ from w.symm]; exact add_sub_cancel_left _ _
  exact (card_image_of_injective _ G.ratio.embed_injective).symm.le.trans ((card_le_card h).trans (card_image_le.trans_eq (card_product S (Lattice.box r))))
def linkTouches :=
   let T:=patchTouches S N M G ×ˢ (univ:Finset Axis)
   T ∪ (T.image (fun t=> (t.1 - step t.2,t.2)))
local notation "P"=> linkTouches S N M G
abbrev touchingBill (R:Patch):ℕ:=2*(Fintype.card Axis)*(S.card*(Lattice.box (Push.GridApprox.reach R)).card)
include ab
lemma untouched (x y:PairsC)(t:G.Choices)(e:Edge (Site M))(h:e∉ P): G.prediction (show Config SU.group _ from grafted S x N) t e= G.prediction (show Config SU.group _ from grafted S y N) t e:=by
  obtain ⟨a,i⟩:=e; have ht:a∉s:= fun p=> h (mem_union_left _ (mem_product.mpr ⟨p,mem_univ _⟩))
  have he : a+step i∉s := fun p=> h (mem_union_right _ (mem_image.mpr ⟨(a+step i,i),mem_product.mpr ⟨p,mem_univ _⟩,by dsimp only; rw [add_sub_cancel_right]⟩))
  unfold StepData.prediction
  rw [connector_dep G ab _ _ _ rfl rfl (outside_agree S N M G x y a ht) (outside_agree S N M G x y _ he)]
omit ab
lemma touchedCost : (P).card≤ touchingBill S G.patch:=by
  let f:=touchingBill S G.patch; unfold linkTouches
  apply (card_union_le ..).trans; have h:(s ×ˢ (univ:Finset Axis)).card ≤ (S.card*(Lattice.box r).card)*Fintype.card Axis:=by
    rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ (count_touched ..)
  refine (Nat.add_le_add h (card_image_le.trans h)).trans_eq ?_; unfold touchingBill; ring

-- avoid proof cast `G.patch.*` in downstream tags
lemma outerEq (R:Patch)(K:KernelChoices)(p:(More N).val=M.val*R.L.val) (u:R.Branches K SU.group)(x y: PairsC)(t:Ornaments R M):
    ∀ e:Edge (Site M),
      let G':StepData M (More N) := ⟨R,K,p⟩
      e∉ linkTouches S N M G' → (G'.prediction (grafted S x N) t e : SU.E)= G'.prediction (grafted S y N) t e:=
  fun e h=> untouched S N M ⟨R,K,p⟩ u x y t e h -- ∀ e let no arrow?
end finance
section perturbed
variable {I:Type*}(A N:I→Side)(R:Patch)(K:KernelChoices)
    (sz:∀ i,(More (N i)).val=(A i).val*R.L.val)
    (u:R.Branches K SU.group) (S:Finset Cover) (β:I→ℝ){C:ℝ}(hβ:∀ i, ‖β i‖ ≤ C)
local notation "L"=> equipment A N R K sz
local notation "X" i:max=> Config SU.group (A i)
abbrev logitPrice (K:KernelChoices)(a:ℝ)(V W: SU.E):= -a*K.penalty*SU.group.price (V*W⁻¹)
def weightLog (i:I)(z: X i)(t:Ornaments R (A i))(e:Edge (Site (A i)))(x:PairsC): ℝ := logitPrice K (β i) (z e) ((L i).prediction (grafted S x (N i)) t e)
include hβ u
lemma log_deck (ε:ℝ)(v:0<ε): ∃ P:Deck PairsC, P.dark ∧ ∀ x y,P.withZ x y→ ∀ i,∀ z:Config SU.group (A i),∀ t e,
    |weightLog A N R K sz S β i z t e x-weightLog A N R K sz S β i z t e y| ≤ ε:=by
  let J:= Σ i:I, X i × Ornaments R (A i) × Edge (Site (A i)); let p:J→I:= fun i=> i.fst
  let F(i:J):= weightLog A N R K sz S β (p i) i.2.1 i.2.2.1 i.2.2.2
  let Z(i:J):= strandsDeal (A∘p) (N∘p) R K (fun i=>sz (p i)) u S (fun i=>i.2.2.1) (fun i=>i.2.2.2)
  have q:= strandsDeal (A∘p) (N∘p) R K (fun i=>sz (p i)) u S (fun i=>i.2.2.1) (fun i=>i.2.2.2)
  let b:J→ℝ:= β∘p; let h:J→SU.E:= fun i=> i.2.1 i.2.2.2
  let T:Set (ℝ × SU.E × SU.E):= Set.Icc (-C) C ×ˢ Set.univ
  have hz:Continuous (fun x:ℝ× SU.E × SU.E=> logitPrice K x.1 x.2.1 x.2.2):=by unfold logitPrice; fun_prop
  have ht: Deal F:= Deal.clip ((Deal.pure (T:=fun _:J=>ℝ) b).prod ((Deal.pure (T:=fun _:J=>SU.E) h).prod q)) (isCompact_Icc.prod isCompact_univ:IsCompact T) (fun i x=>⟨abs_le.mp (hβ (p i)), Set.mem_univ _⟩) hz
  obtain ⟨P,w,W⟩:=ht ε v
  exact ⟨P,w,fun x y a i z t e=> le_of_lt (show dist (F ⟨i,z,t,e⟩ x) (F ⟨i,z,t,e⟩ y) < _ from W _ _ a _)⟩ -- dist def

local notation "U" x:max i:max=> show Config SU.group (More (N i)) from grafted S x (N i)
local notation "D" i:max x:max V:max=> (L i).density (β i) (U x i) V
lemma density_deck (ε:ℝ)(v:0<ε): ∃ P:Deck PairsC,P.dark∧∀ x y,P.withZ x y→∀ i,∀ V:Config SU.group (A i), (D i x V) ≤ Real.exp ε*(D i y V):=by
  let E:= touchingBill S R; let δ:= ε/((E:ℝ)+1); have d:0<δ:=by unfold δ; positivity
  obtain ⟨P,h,H⟩:= log_deck A N R K sz u S β hβ δ d; obtain ⟨Q,k,W⟩:=likelihood_deck A N R K sz u S
  refine ⟨(P:Finset _)∪ Q, P.join Q h k, fun x y a i z=>?_⟩
  let l:=(L i); let F:= StepData.noise (G:=SU.group) l (β i)
  let kappa:= Fintype.card (Edge (Site (A i)))
  have pZ : 0<l.penaltyZ (β i) SU.group:= l.penaltyZ_pos _; let aₖ:= (l.penaltyZ (β i) SU.group)⁻¹^kappa
  have noise (t:Ornaments R (A i)) (x:PairsC) :
    F (l.prediction (U x i) t) z=aₖ*Real.exp (∑ e, weightLog A N R K sz S β i z t e x):=by
    unfold F StepData.noise StepData.penaltyWeight; rw [prod_mul_distrib,prod_const,card_univ,Real.exp_sum]; rfl
  let U' := linkTouches S (N i) (A i) l
  have he:= touchedCost S (N i) (A i) l
  change U'.card≤ E at he
  have ht : (U'.card:ℝ)*δ≤ ε:= ((mul_le_mul_of_nonneg_right (show (U'.card:ℝ)≤(E:ℝ)+1 from (Nat.cast_le.mpr he).trans (by linarith)) d.le).trans_eq (mul_div_cancel₀ _ (by positivity)))
  have he(t:Ornaments R (A i)): F (l.prediction (U x i) t) z ≤ Real.exp ε * F (l.prediction (U y i) t) z:=by
    let f (x:PairsC)(e: Edge (Site (A i))):= weightLog A N R K sz S β i z t e x
    have hp : (∑ e, f x e) - (∑ e, f y e)≤ ε:=by
      rw [←sum_sub_distrib,←(show ∑ e∈U', (f x e-f y e)=_ from sum_subset (subset_univ _) ?_)] -- tune
      · exact (sum_le_sum (fun e _=> (abs_le.mp (H _ _ (Deck.grow Finset.subset_union_left x y a) i z t e)).2)).trans (((by rw [sum_const,nsmul_eq_mul]): (∑ _e∈ U', δ)≤U'.card*δ).trans ht) -- tune precedence
      intro e _ v; unfold f weightLog; rw [show (L i).prediction (grafted S x (N i)) t e=(L i).prediction (grafted S y (N i)) t e from outerEq S (N i) (A i) R K (sz i) u x y t e v,sub_self] -- order wrong: outside lemma signature S N M G? G omitted? equip unfold
    rw [noise,noise,mul_left_comm,← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (by linarith only [show (∑ e, weightLog A N R K sz S β i z t e x)-(∑ e, weightLog A N R K sz S β i z t e y) ≤ ε from hp])) (by unfold aₖ; positivity)
  unfold StepData.density; rw [mul_sum]; refine sum_le_sum fun t _=>?_
  let t':Ornaments R (A i):=t
  change l.likelihood (U x i) t' * F _ _ ≤ Real.exp ε*(l.likelihood _ _ * F _ _)
  rw [show l.likelihood (U x i) t'= _ from W _ _ (Deck.grow Finset.subset_union_right x y a) i t',mul_left_comm (Real.exp ε)]; exact mul_le_mul_of_nonneg_left (he t') (l.likelihood_pos ..)
-- including exact denominator at fixed step (mass one). No β cost grows with period at this fixed level.
lemma relative_deck (ε:ℝ)(v:0<ε): ∃ P:Deck PairsC,P.dark ∧ ∀ x y,P.withZ x y→∀ i,∀ V:Config SU.group (A i), |(D i x V)-(D i y V)| ≤ ε*(D i y V):=by
  let a:=1+ε; obtain ⟨T,p,t⟩:= density_deck A N R K sz u S β hβ (Real.log a) (Real.log_pos (by unfold a; linarith))
  have he:Real.exp (Real.log a)= a:=Real.exp_log (by unfold a; linarith)
  refine ⟨T,p,fun x y u i W=>?_⟩
  have hf:= t x y u i W; have ht:= t y x (fun i h=> (u i h).symm) i W; rw [he] at hf ht; unfold a at hf ht
  have h:(D i x W) ≤ (D i y W) ∨ (D i y W) ≤ (D i x W):= le_total ..
  cases h with
  | inl h=> rw [abs_of_nonpos (sub_nonpos.mpr h)]; nlinarith
  | inr h=> rw [abs_of_nonneg (sub_nonneg.mpr h)]; nlinarith
end perturbed
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.relative_deck
