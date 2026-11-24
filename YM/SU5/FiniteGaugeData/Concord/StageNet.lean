import YM.SU5.FiniteGaugeData.Concord.RibbonCut
/-!
# Overlap and limits on the FiniteGaugeData algebras

Use the linear Palette presentation and hence get support controls on products/smudges across
intersecting sets, `K` generic arithmetic issuer; no `Histories` (pricing window) needed.
Express compatibility by the *common* linear operator of wide local family germs, native products
at s of marks where all are supported, and later use prefactorization transport (separated
products) where it holds. No comparison of a mark with the putative product of its individual
transfers here.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale

section native
variable (K:Calibration) (S:Finset Cover){T:Finset Cover}
/-- All wide even observables native (link, CAR & joint Pane). Issue by exact expression *as functions*, not syntactic: use the quotient inherent in this equality at all periods, which is equivalent to the stencil system at ONE roomy period. -/
def junior (K:Calibration): Subalgebra ℂ (Buffered.Family K) where
  carrier := {f| TestFamily K true f}
  add_mem' := fun t v=> TestFamily.add t v
  mul_mem' := fun t v=> TestFamily.mul t v
  algebraMap_mem' c:=by
    rw [Algebra.algebraMap_eq_smul_one]; exact TestFamily.oneT.scale c

lemma also {f:Buffered.Family K}{S:Finset Cover}(p:InTest K true S false f): f∈ junior K:= show TestFamily K true f from ⟨⟨S,p⟩,fun _=>by contradiction⟩
instance : CommRing (junior K) where
  __ := (inferInstance : Ring (junior K))
  mul_comm (a b : junior K):= Subtype.ext (TestFamily.comm (f:=a.val) (g:=b.val) (wide:=true) (b:=true) a.property b.property)

def club : Subalgebra ℂ (junior K) where
  carrier:={f| InTest K true S false f.val}
  add_mem':= fun t v=> InTest.add t v
  mul_mem':= fun (t:InTest _ true _ false _) (v:InTest _ true _ false _)=> InTest.mul t v
  algebraMap_mem' k:=by
    rw [Algebra.algebraMap_eq_smul_one]; exact InTest.smul k (InTest.one : InTest K true S false 1)

lemma lodge (p:S⊆T) : club K S ≤ club K T:= fun _ t=> InTest.mono t p
lemma supported (f:junior K) : ∃ S, f∈ club K S:= (show TestFamily K true f.val from f.property).paid

-- inclusion from Palette; allows representatives at any support

def music : Palette S→ₗ[ℂ] junior K := (pigment S K).codRestrict (junior K).toSubmodule (fun _=> also K (pigment_test ..))
lemma music_coe (f:Palette S) : (music K S f).val=pigment S K f := rfl
lemma cleft (f:Palette S): music K S f∈club K S:= pigment_test ..
lemma music_rep (f:junior K)(p:f∈club K S): ∃ t:Palette S,music K S t=f:=by obtain ⟨x,v⟩:= encode S K p; exact ⟨x,Subtype.ext v⟩
lemma music_inj : Injective (music K S):= fun _ _ v=> pigment_injective S K (congrArg Subtype.val v)

private def upL (p:S⊆ T): Palette S→ₗ[ℂ] Palette T := by
  let f(x:Palette S):= (encode T K ((pigment_test S K x).mono p)).choose
  have he(x:Palette S):pigment T K (f x)=pigment S K x:=(encode T K ((pigment_test S K x).mono p)).choose_spec -- TC placeholder
  exact {toFun:=f
         map_add' := fun x y=> pigment_injective T K (by rw [he,map_add,map_add,he,he])
         map_smul':=fun a x=> pigment_injective T K (by change _=pigment T K (a • _); rw [map_smul,he,he,map_smul])} -- indentation
private lemma upgrader (p:S⊆T)(x:Palette S): pigment T K (upL K S p x)=pigment S K x:=
  (encode T K ((pigment_test S K x).mono p)).choose_spec

def featuring (p:S⊆T):Palette S→L[ℂ]Palette T:= (upL K S p).mkContinuous (count S) (fun x=> by
  obtain ⟨n,h⟩:= (suitable T K).exists; apply palette_norm T K h; intro i; rw [native_formula,upgrader]; exact native_bound ..)
lemma stow (p:S⊆T)(f:Palette S): music K T (featuring K S p f)=music K S f:=Subtype.ext (upgrader K S p f)
lemma featuring_cost (p:S⊆T): ‖featuring K S p‖ ≤ count S:=by unfold featuring; apply LinearMap.mkContinuous_norm_le; exact count_nonneg _

def polish (f:junior K)(p:f∈club K S): Palette S:= (music_rep K S f p).choose
lemma polish_eq (f:junior K)(p:f∈club K S): music K S (polish K S f p)=f := (music_rep K S f p).choose_spec

-- multilinearity costs, give continuous bilinear readings even though ‖·‖ infinite-volume not put on germs outside boxes
private def times : Palette S →ₗ[ℂ] Palette S→ₗ[ℂ] Palette S := by
  let f(x y : Palette S): junior K := music K S x*music K S y
  let F(x y: Palette S):= polish K S (f x y) ((club K S).mul_mem (cleft ..) (cleft ..))
  have he(x y:Palette S):music K S (F x y)=f x y:=polish_eq ..
  exact {
    toFun x := {
       toFun := F x
       map_add' := fun g k=> music_inj K S (by rw [he,map_add,he,he]; unfold f; rw [map_add,mul_add])
       map_smul' := fun a y=> music_inj K S (by rw [he, RingHom.id_apply,map_smul,he]; unfold f; rw [map_smul,Algebra.mul_smul_comm]) }
    map_add' := fun x y=> LinearMap.ext fun z=> music_inj K S (a₁:=F (x+y) z) (a₂:=F x z+F y z) (by rw [he,map_add,he,he]; unfold f; rw [map_add,add_mul])
    map_smul' := fun a x=> LinearMap.ext fun z=> music_inj K S (a₁:= F (a • x) z) (a₂:=a • F x z) (by rw [he,map_smul,he]; unfold f; rw [map_smul,Algebra.smul_mul_assoc]) }

private lemma times_musical (x y:Palette S) : music K S (times K S x y) = music K S x * music K S y:= polish_eq K S _ ((club K S).mul_mem (cleft ..) (cleft ..))
private lemma times_bound (x y:Palette S): ‖times K S x y‖ ≤ (count S)^2*‖x‖*‖y‖:=by
  have he : pigment S K (times K S x y)=pigment S K x*pigment S K y:= congrArg Subtype.val (times_musical ..)
  obtain ⟨m,h⟩:= (suitable S K).exists; refine palette_norm S K h (fun i=>?_)
  simp only [native_formula,he,Pi.mul_apply]; exact ((norm_mul_le ..).trans (mul_le_mul (pigment_bound ..) (pigment_bound ..) (norm_nonneg _) (mul_nonneg (count_nonneg S) (norm_nonneg _)))).trans_eq (by ring)

def chorusMul : Palette S →L[ℂ] Palette S →L[ℂ] Palette S:= (times K S).mkContinuous₂ _ (times_bound K S)
lemma con_join (x y:Palette S) : music K S (chorusMul K S x y)=music K S x * music K S y:= times_musical ..
lemma join_cost (x y:Palette S): ‖chorusMul K S x y‖ ≤ count S^2*‖x‖*‖y‖:= times_bound ..
lemma timely_mul {I:Type*}{l: Filter I}{f g:I→Palette S}{x y:Palette S}(t:Tendsto f l (𝓝 x))(a:Tendsto g l (𝓝 y)) : Tendsto (fun i=> chorusMul K S (f i) (g i)) l (𝓝 (chorusMul K S x y)) := pair_eval ((chorusMul K S).continuous.continuousAt.tendsto.comp t) a
end native

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover){T: Finset Cover}(s:ℕ) {i k p u v:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "U"=> swept Λ l
local notation "Ω"=> ConeFilter Y i k
variable (V:Universal Y H i k F E)(W:Traced Y H i k F E P)

lemma luggage {Q:Finset Cover}(p:Q⊆T) : swept Λ l Q ⊆ swept Λ l T:=by
  rintro a v; unfold swept Satin.liner at *; obtain ⟨i,v,t⟩:=mem_biUnion.1 v; exact mem_biUnion.mpr ⟨i,Finset.image_subset_image p v,t⟩

include W
lemma step_on {s:ℕ}{S:Finset Cover} {r j:ℕ}(w:SeasonPass Y H S s (i r) (k j))(f:Palette S) : observe Y H (i r) (s+1) (music K (U S) (screen Y H S s (i r) (k j) f)).val= haul Y s (i r) (k j) (observe Y H (i r) s (music K S f).val):=by rw [house Y H S s w, music_coe,music_coe, ←nativeHere_eq, ←nativeHere_eq]; exact repertoire ..

lemma friends (p:S⊆T)(x:Palette S) : featuring K (swept Λ l S) (luggage p) (P.issue s S x) = P.issue s T (featuring K S p x):=by
  let f:=featuring K (swept Λ l S) (luggage (Λ:=Λ) (l:=l) p)
  let h:= (cone_trace Y H S s W.own P W.receipts)
  let t:= (cone_trace Y H T s W.own P W.receipts)
  letI := ConeFilter.uses (Y:=Y) (i:=i) W.own.pick.grow_k
  let X:=featuring K S p x
  apply tendsto_nhds_unique_of_eventuallyEq (f.continuous.continuousAt.tendsto.comp (pair_eval h (tendsto_const_nhds (x:=x)))) (pair_eval t (tendsto_const_nhds (x:=X))) -- hands
  filter_upwards [box_visit W.own.pick (S:=S) (s:=s),box_visit W.own.pick (S:=T) (s:=s)] with a d p'
  apply music_inj K (U T); apply Subtype.ext
  let y:=screen Y H S s (i a.1) (k a.2) x; let Y':=screen Y H T s (i a.1) (k a.2) X
  change (music K (U T) (f y)).val=(music K (U T) Y').val; apply observe_ext Y H (i a.1) (s+1) (pigment_test ..) (pigment_test ..) (Eq.mp (congrArg (Hosp (U T)) (terrain Y H (Y.ir (i a.1)) (s+1))) (roomy p'.main.bigger))
  change observe _ _ _ _ (music K (U T) (f y)).val= observe _ _ _ _ (music K (U T) Y').val
  unfold f y Y'; rw [stow,step_on Y H W d,step_on Y H W p', show music K T X=_ from stow K S p x]

lemma allied (x:Palette S)(y:Palette T) (p:music K S x = music K T y):music K (U S) (P.issue s S x)=music K (U T) (P.issue s T y):=by
  let L:= S ∪ T
  have he: featuring K S (T:=L) subset_union_left x= featuring K T (T:=L) subset_union_right y:= music_inj K _ (by rw [stow,stow,p])
  exact calc
    _ = music K (U L) (featuring K _ (luggage (show S⊆L from subset_union_left)) _) := (stow ..).symm
    _ = music K (U L) (featuring K _ (luggage (show T⊆L from subset_union_right)) (P.issue s T y)):=by rw [friends Y H S s W subset_union_left, friends Y H T s W subset_union_right, he] -- p erased?
    _ = _ := stow ..

omit W
-- use common receipt precision in the counting spaces; afterwards can remove duplicates (actual equality of F).
def courseAdvance (W:Traced Y H i k F E P) : junior (tent Y H) →ₗ[ℂ] junior (tent Y H) := by
 let g(x:junior K):= (supported K x).choose
 let G(x:junior K):= polish K (g x) x (supported K x).choose_spec
 let f(x:junior K):= music K (U (g x)) (P.issue s (g x) (G x))
 have he(x:junior K)(T)(y:Palette T)(p:music K T y=x): f x=music K (U T) (P.issue s T y):= allied Y H (g x) s W (G x) y ((polish_eq ..).trans p.symm)
 exact {
   toFun:=f
   map_add' := fun x y=>by
     let L:=g x ∪ g y
     let Fx:= featuring K _ (T:=L) subset_union_left (G x)
     let Fy:= featuring K _ (T:=L) subset_union_right (G y)
     have hx:music K L Fx=x:=(stow ..).trans (polish_eq ..); have hy:music K L Fy=y:=(stow ..).trans (polish_eq ..)
     rw [he x L Fx hx,he y L Fy hy,he (x+y) L (Fx+Fy) (by rw [map_add,hx,hy]),map_add,map_add]
   map_smul' := fun a x=> by
     let T:=g x; let y:=G x; let L:=P.issue s T
     have hy:music K T y=x:= polish_eq ..
     rw [he (a • x) T (a • y) (by rw [map_smul,hy])]; change music K (U T) (L (a • y))= a • music K (U T) (L y); rw [map_smul L,map_smul] }

include W
lemma courseAdvance_on (x:Palette S) : courseAdvance Y H s W (music K S x)=music K (U S) (P.issue s S x):=
  allied Y H _ s W _ _ (polish_eq ..)
lemma travels (f:junior K)(p:f∈club K S): courseAdvance Y H s W f∈club K (U S):=by obtain ⟨x,rfl⟩:= music_rep K S f p; rw [courseAdvance_on]; exact cleft ..

lemma nilPass : courseAdvance Y H s W 1=1:=by
  letI:= ConeFilter.uses (Y:=Y) (i:=i) W.own.pick.grow_k
  let f:= polish K ∅ 1 (Subalgebra.one_mem _); let b:Finset Cover:= swept Λ l ∅; let t:=polish K b 1 (Subalgebra.one_mem _)
  have hx:music K ∅ f=1:=polish_eq ..; have ht: music K b t=1:=polish_eq ..
  nth_rw 1 [←hx]; rw [courseAdvance_on]; apply Eq.trans _ ht
  apply congrArg; symm; refine tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds (pair_eval (cone_trace Y H ∅ s W.own P W.receipts) (tendsto_const_nhds (x:=f))) ?_
  filter_upwards [box_visit W.own.pick (S:=∅) (s:=s)] with j p
  let y:=screen Y H ∅ s (i j.1) (k j.2) f
  apply music_inj K b
  refine Subtype.ext (observe_ext Y H (i j.1) (s+1) (p:=pigment_test b _ t) (t:=pigment_test b _ y) (Eq.mp (congrArg (Hosp b) (terrain Y H (Y.ir (i j.1)) (s+1))) (roomy p.main.bigger)) ?_) -- tune
  change observe Y H (i j.1) (s+1) (music K b t).val=observe Y H (i j.1) (s+1) (music K b y).val
  have h1:(1:junior K).val=1:=rfl
  rw [ht, show observe Y H _ _ (music K b y).val = _ from step_on Y H W p f,hx,h1, observe_one, observe_one, haul_one _ _ p.timely]
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.courseAdvance_on
#print axioms YM.CF.Buffered.Concord.nilPass
