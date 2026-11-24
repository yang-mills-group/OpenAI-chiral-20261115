import YM.SU5.Registration.Postcards.Separation

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap MeasureTheory Small
variable {S} {V : Type*}[AddCommGroup V][Module ℂ V] (B:Carton S V){n m:ℕ}
-- use Postcards/ bridge with temporal fare subtracting before pricing
local notation "T" => TrainJ V
variable {I:Type}[Fintype I][Nonempty I](p:ℝ≥0)(l t:List (TrainJ V))(f:I→E4)
noncomputable def shipping : ℕ→ (E4→ℂ)→ E4→ℂ
 | 0,c,x=> c x
 | k+1,c,x=> (Fintype.card I :ℂ)⁻¹*∑ i,shipping k c (x+f i)
noncomputable def postmark (n:ℕ) (c:E4→ℂ) (x:E4) :ℂ:= (n:ℂ)⁻¹*∑ i∈ Finset.range n,shipping f i c x
local notation "C!" f:max=> collection S f
variable {d:E4} {Q:E4→ℂ} {K₀ W:H.Op} {j k:H} (hq:∀ u:E4,Solemn u→ Q (d+u)= inner ℂ j (K₀ (postcard S u k))) (g:∀ i,ampleStep (f i))
section pass
-- every F&G::ypa. $h$ nonzero cost. apply sweep_maps from M4 used. calculation uses geometry across all axes for this use.
include hq g
lemma shipped_formula (u:E4)(p:Solemn u)(n:ℕ): shipping f n Q (d+u)=inner ℂ j (K₀ (postcard S u (((C! f)^n:H.Op) k))):=by
 -- ^n k precedence!!
 induction n generalizing u with
 | zero=> rw [pow_zero]; exact hq u p
 | succ n ih=>
   let z := ((C! f)^n : H.Op) k; unfold shipping; rw [pow_succ']; change _ = inner ℂ j (K₀ (postcard S u ((C! f) z)))
   simp_rw [add_assoc]; have he(i:I): shipping f n Q (d+(u+f i))=inner ℂ j (K₀ (postcard S u (postcard S (f i) z))):=by
      rw [ih _ (p.mixes (ample_sick _ (g i))), card_journey S u (f i) (p _) (show 0≤YM.time (f i) from (g i timeAxis).le)]; rfl
   rw [collection_here, map_smul, map_sum,map_smul,map_sum,inner_smul_right,inner_sum]; simp_rw [he]
lemma parcel_formula (n:ℕ) : postmark f n Q d=inner ℂ j (K₀ ((sweep (C! f) n) k)):=by
 have he(i:ℕ): shipping f i Q d= inner ℂ j (K₀ (((C! f)^i:H.Op) k)):=by have ht:= shipped_formula f hq g 0 solemn_zero i; rw [add_zero,card_zero] at ht; exact ht
 unfold postmark sweep; simp_rw [he]; rw [smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum,inner_smul_right,inner_sum]
end pass
-- convert Limit onto H/G x_γ actual post grounding. sign canonical
set_option quotPrecheck false
local notation "N" f:max=> (C! f).eqLocus (1:H.Op)
noncomputable def ground_card (v:H): H:= ((N f).orthogonalProjectionOnto v).val
include hq g
lemma post_pays : Tendsto (fun n=> postmark f n Q d) atTop (𝓝 (inner ℂ j (K₀ (ground_card (S:=S) f k)))):= by
 have h : Tendsto (fun n=> (sweep (C! f) n) k) atTop (𝓝 (ground_card (S:=S) f k)):= sweep_maps (C! f) (collection_norm S f) (StarAlgHom.id ℂ H.Op) k
 exact ((tendsto_const_nhds (x:=j)).inner (K₀.continuous.continuousAt.tendsto.comp h)).congr fun i=>(parcel_formula f hq g i).symm
omit hq
variable {B} (F:InkWaves V)(P:B.Defined F)(φ:waltz p l)(κ:waltz p t)(hs:SweepAhead l t d)(q:Priced f)
local notation "ω" => B.omega
include φ κ P hs
-- point cluster on FORCED words with θ. eventually in width and consulting after. For budget convergence include G witness charges. Limit formula dictates why just WPermit not always enough.
noncomputable def concertedMoments (n:ℕ)(d:E4):=postmark f n (fun u=> Figures F (l++moveCaps t u)) d
local notation "W!" n:max=> concertedMoments l t f F n d
lemma moment_bound (n:ℕ) : ‖W! n‖ ≤ ‖caps B p l‖*‖caps B p t‖:=by
 obtain ⟨J,b,e,u⟩:= either_moving P p l t φ κ d hs
 let K(i:List (TrainJ V)):=caps B p i; let X:= K l*J; let Q:=fun u=> Figures F (l++moveCaps t u); rw [show W! n= _ from (show W! n= inner ℂ ω (X (sweep (C! f) n (K t ω))) from parcel_formula f u g n)];
 let v:=sweep (C! f) n (K t ω)
 have p0 : ‖X‖≤‖K l‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) b)
 let hz:= norm_inner_le_norm (𝕜:=ℂ) ω (X v); rw [B.size,one_mul] at hz
 have hu:‖v‖ ≤ ‖K t‖:=by
    unfold v; refine le_trans ((sweep (C! f) n).le_of_opNorm_le (sweep_bound (C! f) (collection_norm S f) n) (K t ω)) ?_; simpa [B.size] using! (K t).le_opNorm ω
 exact hz.trans ((X.le_opNorm _).trans (mul_le_mul p0 hu (norm_nonneg _) (norm_nonneg _)))
def Moors (B:Carton S V):Prop:= ∀ x,Moored S x→x∈ Submodule.span ℂ {B.omega}
omit φ κ P hs
include q g
lemma moor_sums (h:Moors B)(x:H): ground_card (S:=S) f x= inner ℂ ω x • ω:=by
 let Y:= N f; let t:= ground_card (S:=S) f x; obtain ⟨w,u⟩:= Submodule.mem_span_singleton.mp (h t ((collection_rest S f q (fun i=>g i _) t).1 (((Y).orthogonalProjectionOnto x).property)))
 change t=_; have k:ω∈Y:= by exact (collection_rest S f q (fun i=>g i _) ω).2 ⟨B.hot,fun p=> B.stay _⟩
 have he: inner ℂ ω t=inner ℂ ω x:= Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=Y) ⟨_,k⟩ _
 rw [←u,inner_smul_right, inner_self_eq_norm_sq_to_K,B.size] at he; simp only [one_pow,map_one,mul_one] at he; rw [← he]; exact u.symm
include φ κ P hs
lemma concert_cluster (h:Moors B) : Tendsto (fun n=> W! n) atTop (𝓝 (Figures F l * Figures F t)):=by
 obtain ⟨J,b,e,u⟩ := either_moving P p l t φ κ d hs; have he(w:E4)(z:Solemn w): _:=u w z; let X(i:List (TrainJ V)):=caps B p i; let K₁:=X l*J
 let k:= X t ω; have hq:∀ u':E4,Solemn u' → (fun x=> Figures F (l++moveCaps t x)) (d+u')= inner ℂ ω (K₁ (postcard S u' k)):=u
 convert post_pays (d:=d) (Q:=fun x=> Figures F (l++moveCaps t x)) (S:=S) (K₀:=K₁) (k:=k) f hq g using 2 <;> first|rfl| (rw [moor_sums f g q h,small_moment P p _ φ, small_moment P p _ κ,map_smul,inner_smul_right, mul_comm]; change _*_ = _ * inner ℂ _ (X l (J ω)); rw [e])
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms moment_bound
#print axioms concert_cluster
#print axioms post_pays
