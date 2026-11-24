import YM.SU5.FiniteGaugeData.Tapestry.Precompact
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Upgrade step-maps to operator-norm compactness, with the lower side
cost coming from the project Satin scaffold (finite-coordinates nets in the
*source* via the panel test-cost), paired to our new compactness in the
*target*. No cross-period hypothesis on the color probabilities.
-/
open Py Py.Rate LocalLimit Preparation Journey Vale
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H: Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s:ℕ)
local notation "B"=> followBox (Λ:=Λ) (l:=l) S
local notation "V"=> plaza (Λ:=Λ) S
local notation "D" => (VolumeCape.Dream.plot l).K
local notation "R"=> (VolumeCape.Dream.plot l).C

section
variable (x:Evens S)
def nuance (X:Pigment S): Swatch S:= Pi.single x X
lemma show_note (i:ℕ)(g:Pigment S): present Y H s i S (nuance S x g)=knot (side Y i s) (tagWord S x.val) (daub S g):=by
  funext u; rw [ready_gathered Y H s S]; rw [sum_eq_single x]
  · rw [nuance,Pi.single_eq_same]; rfl
  · intro k _ h; unfold nuance; rw [Pi.single_eq_of_ne h, show daub S 0=0 from rfl]; simp
  simp

local notation "κ"=> (Fintype.card (Courses R V):ℝ)
lemma amount_bill (X:Pigment S): Satin.price Λ l S (daub S X) ≤ κ * ‖X‖:=by
  unfold Satin.price Touch Common.touch Common.amount; refine (sum_le_sum (g:=fun _=>‖X‖) (fun i _=>?_)).trans_eq ?_; swap
  · rw [sum_const,nsmul_eq_mul,card_univ]
  exact (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x=> norm_nonneg _)) (integrable_const ‖X‖) (Filter.Eventually.of_forall fun x=>daubLe ..)).trans (by simp) -- implicit

lemma tuft_net (ε:ℝ)(p:0<ε): ∃ T:Finset (Pigment S), ∀ f:Pigment S, Satin.price Λ l S (daub S f)≤ 1 → ∃ g∈ T,∀ i k:ℕ,∀ (q:Turn S Y s i k), Tipping V (side Y i s) R → ‖barter S Y H s ⟨(i,k),q⟩ (nuance S x (f-g))‖ ≤ ε:=by
  let G (i:Pigment S)(r:Courses R V):= Common.amount R D V (daub S i) r
  have he(i r): Envelope (G i r):= amount_env R D V (Coeff.mono (authentic S i) (liner_here S _)) _
  obtain ⟨Z,k,v⟩:= approximate_fleet (Common.law R V) G he (upholstery Y S s (tagWord S x.val)) (fun i=>die_env Y S s (tagWord S x.val) i) ε p
  refine ⟨Z,fun f u=>?_⟩
  obtain ⟨w,h,W⟩:= v f u
  refine ⟨w,h,fun i k q t=>?_⟩
  have hx:Nonempty (Courses R V):=by
    obtain ⟨μ,hp,_,_⟩:= (Y.voyage i).craft s; exact Nonempty.map (chooseCourse R V (side Y i s)) (nonempty_of_isProbabilityMeasure μ)
  let a : Page Y S s:=⟨⟨(i,k),q.1⟩, 1, Classical.choice hx,1⟩
  rw [barter_apply]; apply present_sample Y H (s+1) i B (Roomy.seats q.2)
  intro z; rw [costumed,show_note]; exact debt Y S s (tagWord S x.val) H (bracketV ..) (x:=⟨_,authentic S f⟩) (y:=⟨_,authentic S w⟩) a t ε (fun j r=> (W j r).le) z -- change sub

private lemma pigSub {S:Finset Cover}(c:ℂ)(x y:Pigment S): c • (x-y)= c•x-c•y:= by
  exact smul_sub  c (show ↥(Tapestry.pigments S) from x) (show ↥(Tapestry.pigments S) from y)
-- order?
lemma fluent_net (ε:ℝ)(p:0<ε): ∃ T:Finset (Pigment S), ∀ f:Pigment S, ‖f‖≤ 1 → ∃ g∈ T,∀ i k:ℕ,∀ (q:Turn S Y s i k), Tipping V (side Y i s) R → ‖barter S Y H s ⟨(i,k),q⟩ (nuance S x (f-g))‖ ≤ ε:=by
  let G:=κ+1; have g:0<G:=by unfold G; positivity
  let t:=(algebraMap ℝ ℂ G⁻¹); obtain ⟨T,v⟩:= tuft_net Y H S s x (ε/G) (by positivity)
  refine ⟨T.image (fun x:Pigment S=> t⁻¹ • x), fun f h=>?_⟩
  have w:‖t‖=G⁻¹:=by simp [t,abs_of_nonneg g.le,Real.norm_eq_abs]
  have W:t≠0:= norm_pos_iff.mp (by rw [w]; positivity)
  have he : Satin.price Λ l S (daub S (t • f))≤1:=by
    apply (amount_bill S _).trans; rw [norm_smul,w]; have ht:κ≤G:=by unfold G; linarith
    rw [←mul_assoc]; refine le_trans (mul_le_mul (le_of_eq (rfl)) h (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr g.le))) ?_; rw [mul_one]; exact (mul_le_mul_of_nonneg_right ht (inv_nonneg.mpr g.le)).trans_eq (mul_inv_cancel₀ g.ne')
  obtain ⟨a,s',K⟩:= v (t • f) he; refine ⟨t⁻¹ • a,mem_image_of_mem _ s',fun i k q h=>?_⟩
  rw [show f-t⁻¹ • a=t⁻¹ • (t • f-a) from (by rw [(show t⁻¹ • (t • f-a)= t⁻¹ • t • f-t⁻¹ • a from pigSub _ _ _),inv_smul_smul₀ W]),show nuance S x (t⁻¹ • (t • f-a))= t⁻¹ • nuance S x (t • f-a) from ?_, map_smul,norm_smul,norm_inv,w, inv_inv]; swap
  · exact Pi.single_smul' x t⁻¹ (show ↥(Tapestry.pigments S) from t • f-a) -- order
  exact (mul_le_mul_of_nonneg_left (K i k q h) g.le).trans_eq (mul_div_cancel₀ _ g.ne')
end

abbrev Matinee(i:ℕ):Prop:= Tipping (plaza (Λ:=Λ) S) (side Y i s) (VolumeCape.Dream.plot l).C ∧ Roomy (followBox (Λ:=Λ) (l:=l) S) (side Y i (s+1))
abbrev Spanned (i k:ℕ):Prop:= Satin.PairIdx Y s i k ∧ Matinee Y S s i
lemma Spanned.turn {i k:ℕ}(h:Spanned Y S s i k):Turn S Y s i k:=⟨h.1,h.2.2⟩
include H in
lemma seasons : ∀ᶠ i in atTop, Matinee Y S s i:=by
  filter_upwards [(momentum Y s).eventually (separates (tent Y H) (tips (porch R V))),roomyTail Y H (s+1) B] with i v g
  refine ⟨?_,g⟩; unfold side; rw [←terrain Y H]; exact v

abbrev Sales := {x:ℕ×ℕ//Spanned Y S s x.1 x.2}
abbrev peddle (i:ℕ) (k:ℕ) (h:Turn S Y s i k) := barter S Y H s ⟨(i,k),h⟩
-- may use anytime Turn. TB so far just Spanned. 
def offer (i:Sales Y S s): (Swatch S →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S)):=peddle Y H S s i.val.1 i.val.2 (Spanned.turn Y S s i.property)
lemma offerMap (a:Sales Y S s)(f:Swatch S): offer Y H S s a f=Tapestry.costume Y H s a.val.1 a.val.2 S a.property.1 a.property.2.2 f:=rfl

lemma offerDiff {T U:Type*}[NormedAddCommGroup T][NormedSpace ℂ T][NormedAddCommGroup U][NormedSpace ℂ U](f:T→L[ℂ]U)(x y:T): f (x-y) = f x-f y:=map_sub f x y
lemma offerSum {T U I:Type*}[Fintype I][NormedAddCommGroup T][NormedSpace ℂ T][NormedAddCommGroup U][NormedSpace ℂ U](f:T→L[ℂ]U)(x:I→T):f (∑ i,x i)=∑ i,f (x i):= map_sum ..
lemma audience (ε:ℝ)(p:0<ε) : ∃ T:Finset (Swatch S),∀ f:Swatch S, ‖f‖≤1 → ∃ g∈T,∀ t:Sales Y S s, dist (offer Y H S s t f) (offer Y H S s t g) ≤ ε :=by
  let E:=spread S+1; have e:0<E:=by unfold E; positivity
  choose T v using fun x:Evens S=> fluent_net Y H S s x (ε/E) (by positivity); let A:=Finset.univ.image (fun (t:∀ i,↑(T i)) i=> (t i).val) -- Icc; no nonempty needed
  refine ⟨A,fun f h=>?_⟩
  choose g t p' using fun i=> v i (f i) ((norm_le_pi_norm ..).trans h)
  refine ⟨g,Finset.mem_image.mpr ⟨fun i=>⟨_,t i⟩,mem_univ _,rfl⟩,fun z=>?_⟩
  let f':= offer Y H S s z
  have eq: f' (f-g) = f' f - f' g:= offerDiff (T:=Swatch S) (U:=Swatch (followBox (Λ:=Λ) (l:=l) S)) f' f g
  have eq'(X:Evens S→ Swatch S) : f' (∑ i,X i) = ∑ i, f' (X i):= offerSum (T:=Swatch S) (U:=Swatch (followBox (Λ:=Λ) (l:=l) S)) f' X
  change dist (f' f) (f' g) ≤ ε; rw [dist_eq_norm,←eq]
  rw [show f-g =∑ i:Evens S, nuance S i (f i-g i) from (Finset.univ_sum_single (f-g)).symm, eq']
  exact (norm_sum_le ..).trans ((sum_le_sum (fun i u=> p' i z.val.1 z.val.2 (Spanned.turn Y S s z.property) z.property.2.1)).trans (by rw [sum_const,nsmul_eq_mul,card_univ]; apply le_trans _ (mul_div_cancel₀ ε e.ne').le; gcongr; unfold E; linarith))

/-- Local dual/operator-norm compactness of the advancers themselves. -/
lemma offer_tb : TotallyBounded (Set.range (offer Y H S s)):=by
  refine capture (offer Y H S s) ?_
  intro ε p
  let d:= ε/4; have hd:0<d:=by unfold d; linarith
  obtain ⟨T,w⟩:= audience Y H S s d hd
  let U(t:Sales Y S s)(j:T):= offer Y H S s t j.val
  refine ⟨↥T→Swatch (followBox (Λ:=Λ) (l:=l) S), inferInstance,U,d,hd,captureTuple U ?_,?_⟩
  · intro i; exact costumeTB S Y H s (fun i:Sales Y S s=>i.val.1) (fun i:Sales Y S s=>i.val.2) (fun i=>i.property.1) (fun i=>i.property.2.2) (fun _=>i.val) (fun _=>le_refl ‖i.val‖)
  intro i k v; rw [dist_eq_norm (offer Y H S s i) (offer Y H S s k)]; apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm (f:=(offer Y H S s i-offer Y H S s k)) (C:=3*d) (by positivity) ?_) (by unfold d; linarith)
  intro x hx; obtain ⟨t,m,h⟩:=w x hx.le
  let u:↥T:=⟨t,m⟩; let X:=offer Y H S s
  change ‖X i x-X k x‖ ≤ _; rw [←dist_eq_norm]; change dist (X i x) (X k x)≤ _; have a (i'): dist (X i' x) (X i' t) ≤ d:= h i'; have he:dist (X i t) (X k t) ≤ d:= ((dist_pi_lt_iff hd).mp v u).le
  linarith [a i,a k, dist_triangle (X i x) (X i t) (X k x), dist_triangle_right (X i t) (X k x) (X k t)]
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.offer_tb
