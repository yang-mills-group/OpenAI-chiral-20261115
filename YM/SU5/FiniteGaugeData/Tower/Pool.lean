import YM.SU5.FiniteGaugeData.Tower.Ford
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
# Time motions of the Hilbert space, for now throughout the lattice moments

Advance *one* OS Hilbert system. Law of addition even for different
resolutions. Comparison odd-step subdivision need not give a positive E_s(t)
for the single t_step, thus have option to use doubled times throughout for
true positive (not just contractive) semigroup; still arbitrarily fine. Keep
normalization and same read identification (`Ark`/`Clouds`) including in
forms on this motion.
-/
open scoped InnerProductSpace
open Fock
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
local notation "m"=> meshface (Λ:=Λ) z s
variable (C:Arena Y H Q j z strict)
local notation "T" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "κ'" s:max=>arrows Y H V Q j z strict C s
local notation "A"=> Ark.Ht Y H Q j z strict C
local notation "t₀" s:max=>tick Y H s j z strict
local notation "Z"=>Choir Y H j z strict
local notation "R"=> Raise Y H Q j z strict
local notation "L"=>Λ.R.L.val
def amount (Λ:Preparation)(s r i:ℕ):=Λ.R.L.val^(r-s)*i
lemma amount_reset (Λ:Preparation)(s i:ℕ): amount Λ s s i=i:=by simp [amount]
lemma amount_add (Λ:Preparation)(s r i k:ℕ): amount Λ s r (i+k)=amount Λ s r i+ amount Λ s r k:=by simp [amount,Nat.mul_add]
lemma amount_grew (Λ:Preparation)(s t r i:ℕ)(p:s≤ t)(q:t≤ r):amount Λ t r (amount Λ s t i)=amount Λ s r i:=by unfold amount; rw [← mul_assoc, ←pow_add,show r-t+(t-s)=r-s by omega]

noncomputable def bear (r t i:ℕ)(e:s ≤ r)(p:t ≤ r)(x:T t):T r:= (t₀ r) (amount Λ s r i) (R t r p x)
variable (i':ℕ)
local notation "F₀" r:max t:max=> bear Y H s Q j z strict r t i'
include V
lemma grow_h {a b c:ℕ}(e:s≤ a)(p:c≤ a)(q:a≤ b)(x:T c): (F₀ b c) (e.trans q) (p.trans q) x= R a b q ((F₀ a c) e p x):=by
 unfold bear
 rw [← tick_up Y H V a Q j z strict b q (Raise Y H Q j z strict c a p x) (amount Λ s a i'),←show amount Λ a b (amount Λ s a i')=_ from amount_grew Λ s a b i' e q]
 congr 1; apply Subtype.ext; exact (congrArg Subtype.val (linking_diagram Y H Q j z p q (freeze Y H c j z strict x))).symm

noncomputable def evolve(x: Choir Y H j z strict): A:= (κ (max s x.1)) (bear Y H s Q j z strict (max s x.1) x.1 i' (le_max_left ..) (le_max_right ..) x.2)
local notation "X₀"=> evolve Y H s Q j z strict C i'
include C
lemma regrow {a b:ℕ}(e:s ≤ a)(q:b≤ a)(x:T b): X₀ (show Z from ⟨b,x⟩)=(κ a) ((F₀ a b) e q x):=by
 unfold evolve; let v:=max_le e q
 rw [grow_h Y H V s Q j z strict i' (a:=max s b) (b:=a) (le_max_left s b) (le_max_right s b) v x,join_actor Y H V]

lemma meridian:∃ A': A →L[ℂ] A, ‖A'‖≤1∧∀t (x:T t), A' ((κ t) x)= X₀ (show Z from ⟨t,x⟩):=by
 suffices h:∃ A':A →L[ℂ] A, ‖A'‖≤1 ∧∀x:Z, A' ((κ x.1) x.2)=X₀ x by obtain ⟨v,t,g⟩:=h; exact ⟨v,t,fun t x=>g (show Z from ⟨t,x⟩)⟩
 apply _root_.YM.Kernel.Gram.by_bound C X₀ 1 zero_le_one
 intro f; classical
 let r:=max s (f.support.sup (fun i:Z=>i.1))
 have e(i:Z)(t:i∈f.support):i.1 ≤r:= (le_sup (f:=fun i:Z=>i.1) t).trans (le_max_right ..)
 have p:s ≤ r:=le_max_left ..
 let g(x:Z):T r:= if w:x∈f.support then R x.1 r (e x w) x.2 else 0
 let t:T r:= f.sum (fun i v=> v • g i)
 have Hd: (show _root_.YM.Kernel.Gram _ from C).stems f= (κ' r) t:=by
    simp only [_root_.YM.Kernel.Gram.stems,Finsupp.linearCombination_apply,t,map_finsuppSum,map_smul]
    unfold Finsupp.sum; refine sum_congr rfl fun i v=> ?_; dsimp only; unfold g; rw [dif_pos v]; exact congrArg (fun x:A=> f i • x) (join_actor Y H V Q j z strict C i.1 r (e i v) i.2).symm
 let u:=(t₀ r) (amount Λ s r i')
 have ht : Finsupp.linearCombination ℂ X₀ f= (κ' r) (u t):=by
    simp only [Finsupp.linearCombination_apply,t,map_finsuppSum,map_smul]
    unfold Finsupp.sum; refine sum_congr rfl fun i v=> ?_; dsimp only; unfold g; rw [dif_pos v]; exact congrArg (fun x:A=> f i • x) (regrow Y H V s Q j z strict C i' (a:=r) p (e i v) i.2)
 rw [one_mul,ht,Hd]; exact ticks Y H V r Q j z strict C _ _

noncomputable def ripple : A →L[ℂ] A := (meridian Y H V s Q j z strict C i').choose
local notation "ρ" s:max i:max=>ripple Y H V s Q j z strict C i
lemma ripple_le: ‖ρ s i'‖≤1:= (meridian Y H V s Q j z strict C i').choose_spec.1
lemma ripples{a b:ℕ}(p:s≤ a)(t:b≤ a)(x:T b): (ρ s i') ((κ b) x)= (κ a) ((F₀ a b) p t x):=((meridian Y H V s Q j z strict C i').choose_spec.2 b x).trans (regrow Y H V s Q j z strict C i' p t x)
-- formulas on compatible plant vectors even when actor at higher scale
lemma limited_time {a:ℕ}(p:s≤ a)(v:T a): (ρ s i') ((κ a) v)=(κ a) ((t₀ a) (amount Λ s a i') v):=by
 have ht:R a a (le_refl _) v=v:=Subtype.ext (by change stream Y H D a (a-a) v.val=v.val; rw [Nat.sub_self]; rfl)
 rw [ripples Y H V s Q j z strict C i' p le_rfl,bear,ht]
-- bona fide operations and spectral switch
lemma consistent_τ (r:ℕ)(p:s≤r): ρ r (amount Λ s r i')=ρ s i':=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro x
 let t:=max r x.1; have v:x.1 ≤ t:=le_max_right ..; have h:r ≤ t:=le_max_left ..
 change (ρ r (amount Λ s r i')) ((κ x.1) x.2)=(ρ s i') ((κ x.1) x.2)
 rw [ripples Y H V _ Q j z strict C _ h v,ripples Y H V _ Q j z strict C _ (p.trans h) v]; unfold bear; rw [amount_grew Λ _ _ _ i' p h]
lemma unleash:(ρ s 0)=ContinuousLinearMap.id ℂ A:=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro x
 change (ρ s 0) ((κ x.1) x.2)= (κ x.1) x.2
 rw [ripples Y H V s Q j z strict C 0 (le_max_left s (x.1)) (le_max_right s (x.1)),bear,show amount Λ s _ 0=0 from mul_zero _,tick_seed Y H,join_actor Y H V]
lemma breeds (k:ℕ): (ρ s i').comp (ρ s k)= ρ s (i'+k):=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro x
 let t:=max s x.1; have v:x.1 ≤ t:=le_max_right ..; have h:s ≤ t:=le_max_left ..
 change (ρ s i') ((ρ s k) ((κ x.1) x.2))=(ρ s (i'+k)) ((κ x.1) x.2)
 rw [ripples Y H V _ Q j z strict C k h v,limited_time Y H V s Q j z strict C i' h,ripples Y H V _ Q j z strict C _ h v]; unfold bear; rw [amount_add,tick_tock]
lemma current_adjoint: (ρ s i').adjoint=(ρ s i'):=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro v
 let u:=v.1
 apply all_voices Y H Q j z strict C; intro r x
 let t:=max s (max r v.1); have a:v.1≤t:=(le_max_right ..).trans (le_max_right ..); have b:r≤t:=(le_max_left ..).trans (le_max_right ..); have c:s≤t:=le_max_left ..
 change inner ℂ ((κ r) x) ((ρ s i').adjoint ((κ v.1) v.2))= _
 change _=inner ℂ ((κ r) x) ((ρ s i') ((κ v.1) v.2))
 rw [ContinuousLinearMap.adjoint_inner_right,ripples Y H V s Q j z strict C i' c a,ripples Y H V s Q j z strict C i' c b]
 rw [← join_actor Y H V Q j z strict C v.1 t a v.2,←join_actor Y H V Q j z strict C r t b x]
 exact shuttle Y H V t Q j z strict C (amount Λ s t i') _ _
lemma normalized_τ: (ρ s i') (floorV Y H Q j z strict C)=floorV Y H Q j z strict C:=by
 rw [vacua Y H V Q j z strict C s,limited_time Y H V s Q j z strict C i' (le_refl s),tick_unit]
lemma c_even (x:A):0≤ inner ℂ x ((ρ s (2*i')) x):=by
 rw [two_mul,←breeds Y H V,ContinuousLinearMap.comp_apply]; nth_rw 1 [← current_adjoint Y H V s Q j z strict C i']; rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]; positivity
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.current_adjoint
#print axioms YM.CF.Buffered.Afterglow.Tower.breeds
#print axioms YM.CF.Buffered.Afterglow.Tower.c_even
