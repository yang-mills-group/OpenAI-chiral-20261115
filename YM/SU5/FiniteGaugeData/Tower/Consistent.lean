import YM.SU5.FiniteGaugeData.Tower.Pass
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
# Single level hierarchy and its anterior regulation

Given the same Universal, use just one cone path (diagonal availability
for these periods exactly) and thin once more. E(s) on the election doesn't
change; `PathLease` just grants cooperation on the block observables. Its
charges will show EXACT resolution coherence of E under the true one-step
transport (i.e., limit of actual push, not K-mark term scale cast), with
multiplication assertions where appropriate. These theorems don't assert
uniqueness of that mapping off the purchase choice. See also relative norm
costs through the selection. This still isn't coherence/positivity for a
continuum system.
-/

variable (n k₀ :ℕ→ℕ)
-- path parameters in CrimsonLine V (not original course)
variable {q: ℕ→ℕ}(Q : CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q)
structure PathLease {i k q:ℕ→ℕ} (n k₀:ℕ→ℕ) : Prop where
  periods : StrictMono n
  cutters : StrictMono k₀
  gate (j:ℕ): legacy Y ((i∘q∘n) j) ((k∘k₀) j)
  members:Cresc Y H (i∘q∘n) (k∘k₀)

local notation "Z"=> i ∘ q ∘ n
local notation "T"=> k ∘ k₀
include V Q
lemma fuel: ∃ p:ℕ→ℕ,StrictMono p∧∀r,legacy Y (i (q r)) (k (p r)):=by
 have h(r m:ℕ):∃ j≥ m+1, legacy Y (i (q r)) (k j):=legacy_above Y H V _ _
 choose W u v using h
 let X:=Nat.rec (motive:=fun _=>ℕ) (W 0 0) (fun r u=> W (r+1) u)
 refine ⟨X,strictMono_nat_of_lt_succ (fun r=>u ..),fun i=>?_⟩
 cases i; exact v 0 0; exact v _ _
lemma permits:∃ n k₀,PathLease (i:=i) (k:=k) (q:=q) Y H n k₀:=by
 obtain ⟨p,e,t⟩:= fuel Y H V Q
 have ht:StrictMono (i∘q):= V.pick.grow_i.comp Q.grows
 have hu(r):∀ᶠ j:ℕ in atTop, legalAt Y r ((i∘q) j) ((k∘p) j):=by
    filter_upwards [((Y.uv_grows.comp (V.pick.grow_k.comp e)).tendsto_atTop.eventually_gt_atTop r)] with i b
    exact ⟨V.pick.ticket (q i) (p i) (t i),b⟩
 obtain ⟨f,x,v⟩:=perform Y H (i∘q) (k∘p) ht.tendsto_atTop hu
 exact ⟨f,p∘f,x,e.comp x,fun j=>t (f j),v⟩
variable (P:PathLease (i:=i) (k:=k) (q:=q) Y H n k₀)
include P
lemma license (s:ℕ):∀ᶠ r:ℕ in atTop,Ferry Y s ((i∘q∘n) r) ((k∘k₀) r):= (P.periods.tendsto_atTop.eventually (Q.budget s ∅)).mono fun i p=> p.2.1 _ (P.gate i)
lemma legally :∀s,∀ᶠ r:ℕ in atTop, legalAt Y s ((i∘q∘n) r) ((k∘k₀) r):=fun s=> ((license Y H V n k₀ Q P (s+1))).mono fun r p=> ⟨p.depth,p.enters⟩
lemma growth :StrictMono (i∘q∘n):=V.pick.grow_i.comp (Q.grows.comp P.periods)
lemma likely {F:Family (tent Y H)}(x:TestFamily K true F): Tendsto (fun r=> sharp Y H s (Z r) (T r) F) atTop (𝓝 (E s F)):=by
 -- use budget via Q and valuation; support fixed
 obtain ⟨S,e⟩:= x.paid
 obtain ⟨v,p⟩:= Journey.valuation Y H e
 have he:Tendsto (fun r:ℕ=> ((1/2:ℝ)^ (n r))*v) atTop (𝓝 0):=by
    have h:Tendsto (fun r:ℕ=>(1/2:ℝ)^r) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (h.comp P.periods.tendsto_atTop|>.mul_const v)
 exact Metric.tendsto_nhds.mpr fun ε h=>by
    filter_upwards [P.periods.tendsto_atTop.eventually (Q.budget s S), he.eventually (gt_mem_nhds h)] with i t hP -- gt_mem
    · rw [dist_eq_norm]; exact lt_of_le_of_lt ((t.2.2 F e v (p _)).2 (k₀ i) (P.gate i)) hP

variable (S:Finset Cover){F:Family (tent Y H)}(x:InTest (tent Y H) true S false F)
local notation "Ψ"=> destined Y H s Z T S P.members
local notation "W"=> wingspan Λ l S
local notation "J" r:max F:max=> block Y H s (Z r) (T r) S F
local notation "δ" r:max=> (1/2:ℝ)^r
local notation "Φ" S':max r:max=> sharp Y H S' (Z r) (T r)
-- Uniform path error even at variable marks: compare upper read on limiting transfer
-- to corresponding *sharp lower* (not normalized on surrogate heat). Since input and output charged,
-- moving marks on other paired path points for same Q and same E have similar cost.
lemma greatest : ∃ A:ℝ,0<A∧∀ e:ℝ,0<e→ ∀ᶠ r in atTop, ∀ (F:Family (tent Y H)), InTest K true S false F→∀ u:ℝ, pay F u →
 pay (Ψ F) (A*u) ∧
 Ferry Y s (Z r) (T r) ∧ Ferry Y (s+1) (Z r) (T r) ∧
 (Φ (s+1) r) (J r F)=(Φ s r) F ∧
 ‖(Φ s r) F-E s F‖≤δ (n r)*u ∧
 ‖(Φ s r) F-E (s+1) (Ψ F)‖≤δ (n r)* (A*u)+e*u ∧
 ‖(Φ (s+1) r) (Ψ F)-E (s+1) (Ψ F)‖≤ δ (n r)*(A*u):=by
 obtain ⟨A,p,f⟩:=operator_paid Y H s Z T P.members S
 refine ⟨A,p,fun e v=>?_⟩
 let d:= toll Y H (s+1) W; have hd:0≤d:= (toll_pays Y H (s+1) W).1; let c:= e/(d+1); have he:0<c:=by unfold c; positivity
 have he': d*c ≤ e:=by have ht:(d+1)*c=e:=mul_div_cancel₀ _ (by positivity); linarith
 filter_upwards [f,(growth Y H V n k₀ Q P).tendsto_atTop.eventually (turning Y H (s+1) W), legally Y H V n k₀ Q P s,
    Cresc.outfits Y H s Z T S P.members c he,P.periods.tendsto_atTop.eventually (Q.budget s S),P.periods.tendsto_atTop.eventually (Q.budget (s+1) W)] with r b h k a x1 x2 F x u y
 have ht₀:= attaches Y H s Z T S P.members F; have hZ:= (x1.2.2 F x u (y _)).2 (k₀ r) (P.gate r)
 have ht:= booked Y H s (Z r) (T r) S F; have hp:= b F x u y
 have he(g x c)(w:pay g c): ‖(Φ (s+1) r) g-E (s+1) g‖≤ δ (n r)*c:= (x2.2.2 g x c (w _)).2 (k₀ r) (P.gate r) -- x infer
 have q₀: (Φ (s+1) r) (J r F)=(Φ s r) F:=upper_coupling Y H s S (Z r) (T r) k x h
 refine ⟨hp.1,x1.2.1 _ (P.gate r),x2.2.1 _ (P.gate r),q₀,hZ,?_,he _ ht₀ _ hp.1⟩
 rw [←q₀]
 refine (norm_sub_le_norm_sub_add_norm_sub _ (E (s+1) (J r F)) _).trans (add_le_add (he _ ht _ hp.2) ?_)
 rw [←E_sub Y H V (s+1) (aux_test ht) (aux_test ht₀)]
 exact (E_bound Y H V (s+1) W (InTest.subOp ht ht₀) (a _ x _ y)).trans (le_trans (le_of_eq (mul_assoc d c u).symm) (mul_le_mul_of_nonneg_right he' (pay_nonneg y)))
include x
-- The limiting E *at the next level* evaluates the flow, and it is exactly
-- THE E at this level.
lemma equality : E (s+1) (Ψ F)=E s F :=by
 obtain ⟨A,p,b⟩:= greatest Y H V s n k₀ Q P S -- order
 obtain ⟨u,v⟩:=Journey.valuation Y H x; have fX:pay F u:=v; have e:0≤u:=pay_nonneg fX
 have h:Tendsto (fun r:ℕ=>(1/2:ℝ)^r) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 refine (tendsto_nhds_unique (likely Y H V s n k₀ Q P (aux_test x)) (Metric.tendsto_nhds.mpr (fun ε h'=>?_))).symm
 let d:= ε/((u+1)*2); have hd:0<d:=by unfold d; positivity
 have he:Tendsto (fun r:ℕ=> (δ (n r))*(A*u)) atTop (𝓝 0):=by simpa using ((h.comp P.periods.tendsto_atTop).mul_const (A*u))
 filter_upwards [b d hd,he.eventually (gt_mem_nhds (half_pos h'))] with r g hh
 rw [dist_eq_norm]; refine lt_of_le_of_lt (g F x u fX).2.2.2.2.2.1 ?_; change δ (n r)*(A*u)< _ at hh
 have hp:d*((u+1)*2)= ε:= div_mul_cancel₀ _ (by positivity); nlinarith
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.permits
#print axioms YM.CF.Buffered.Afterglow.Tower.equality
