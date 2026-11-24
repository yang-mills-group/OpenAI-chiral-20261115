import YM.SU5.FiniteGaugeData.Tower.Lines
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
# Keep cost of multiple actual transfers on these paired trajectories,
using the stronger norm statement

Actual chart-valued, at `Pose r`. QFT use still has to match the transported
insertions against the desired physical boundary probes. This is a regulator
throughput result BEFORE any such boundary, already across resolutions, on
these same signed reads. e.g. transport through several resolutions, evaluate
(after cutoff selection) on elected reading, compare even allowing input mark
to change.
-/
section
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q: Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
local notation "π₀" r:max=> i (a r)
local notation "κ" r:max=> k (b r)
noncomputable def train (j z:ℕ)(n m:ℕ)(S:Finset Cover)(F:Family (tent Y H)):Family (tent Y H) := Nat.rec F (fun i x=> block Y H (j+i) n m (volumeAround Λ l i S) x) z
local notation "F₀" z:max r:max S:max F:max=>train Y H s z (π₀ r) (κ r) S F
local notation "W" S:max z:max=>volumeAround Λ l z S
local notation "X" z:max F:max=>stream Y H D s z F
variable (S:Finset Cover)

lemma train_step(z n m:ℕ)(F:Family (tent Y H)): train Y H s (z+1) n m S F=block Y H (s+z) n m (volumeAround Λ l z S) (train Y H s z n m S F):= rfl
lemma prepared_train (z n m:ℕ){F:Family (tent Y H)}(p:InTest K true S false F): InTest K true (volumeAround Λ l z S) false (train Y H s z n m S F):=by
 induction z with
 | zero=> exact p
 | succ z h=> exact booked Y H (s+z) n m _ _

include Q
lemma D_sub {s}{F G}(p:TestFamily K true F)(q:TestFamily K true G):D s (F-G)=D s F-D s G:= by rw [sub_eq_add_neg,←neg_one_smul ℂ G,Q.circuit.plus_lift _ p (q.scale _),Q.circuit.amp _ q,neg_one_smul,sub_eq_add_neg]

lemma fares (z:ℕ): ∃ C:ℝ,0<C ∧∀ε:ℝ,0< ε → ∀ᶠ r in atTop,
 ∀ (F:Family K),InTest K true S false F→∀x:ℝ,pay F x→
 pay (X z F) (C*x) ∧ pay (F₀ z r S F) (C*x) ∧
 pay (F₀ z r S F-X z F) (ε*x) ∧ sharp Y H (s+z) (π₀ r) (κ r) (F₀ z r S F)=sharp Y H s (π₀ r) (κ r) F :=by
 induction z with
 | zero=> refine ⟨1,zero_lt_one,fun ε p=>Eventually.of_forall fun r F x y h=>?_⟩; simp only [stream,Nat.rec_zero,one_mul,Nat.add_zero,train]; refine ⟨h,h,(sub_self F).symm ▸ (fun i t=> (show ‖(0:Family K) i t‖=(0:ℝ) from norm_zero).le.trans (mul_nonneg p.le (pay_nonneg h))),trivial⟩
 | succ z ih=>
    let U:= s+z; let S₀:=volumeAround Λ l z S
    obtain ⟨B,bp,g⟩:=ih; obtain ⟨A,h,c⟩:=Q.implements U S₀
    refine ⟨A*B,mul_pos h bp,fun ε e=>?_⟩
    let δ:= ε/(A+B+1); have hd:0<δ:=by unfold δ; positivity
    filter_upwards [g δ hd,c δ hd] with r p t F iH x q
    let W₀:=stream Y H D s z F; let Z:= train Y H s z (π₀ r) (κ r) S F
    obtain ⟨h₁,h₂,h₃,Hg⟩:= p F iH x q
    have hv:InTest K true S₀ false W₀:= (proceeds Y H Q.circuit s z iH).1; have hs:= prepared_train Y H s S z (π₀ r) (κ r) iH
    obtain ⟨h₄,h₅,h₆,h₇,h₈⟩:=t _ hs _ h₂
    rw [stream_step,train_step,←Nat.add_assoc,← Hg]; refine ⟨mul_assoc A B x ▸ (t _ hv _ h₁).1, mul_assoc A B x ▸ h₅,?_,h₇⟩ -- eq orientation
    intro n y; let V:=block Y H U (π₀ r) (κ r) S₀ Z
    change ‖V n y-D U W₀ n y‖≤ _; apply (norm_sub_le_norm_sub_add_norm_sub _ (D U Z n y) _).trans
    have hd0:pay (D U Z-D U W₀) (A*(δ*x)):=by rw [←D_sub Y H Q (aux_test hs) (aux_test hv)]; exact (t _ (InTest.subOp hs hv) _ h₃).1
    apply (add_le_add (h₆ n y) (hd0 n y)).trans
    change δ*(B*x)+A*(δ*x)≤ ε*x
    have ht:(A+B)*δ≤ ε:= by have hp:(A+B+1)*δ=ε:=mul_div_cancel₀ _ (by positivity); nlinarith
    calc
      _ = ((A+B)*δ)*x:=by ring
      _≤ _:= mul_le_mul_of_nonneg_right ht (pay_nonneg q)
include V
lemma pirouette(z:ℕ)(ε:ℝ)(p:0< ε):∀ᶠ r in atTop,let n:=π₀ r; let t:=κ r
 Hosp S ((K).c (momentm Y n s))∧Tivoli (W S z) ((K).c (momentm Y n (s+z)))∧
 ∀ (F:Family K), InTest K true S false F→∀ x:ℝ,pay F x →
  let G:=train Y H s z n t S F; let Z:=stream Y H D s z F
  ‖I (s+z) G n - E s F‖ ≤ ε*x∧
  ‖sharp Y H (s+z) n t G-E s F‖ ≤ ε*x ∧
  ‖sharp Y H (s+z) n t Z-E s F‖≤ ε*x:=by
 obtain ⟨A,u,e⟩:=fares Y H s Q S z -- order?
 let U:=s+z; let S₀:= volumeAround Λ l z S
 let C:=toll Y H U S₀; have Hc:0≤C:=(toll_pays Y H U S₀).1
 let δ:= ε/(A+C+1); have hd:0<δ:=div_pos p (by positivity)
 have v: Tendsto (i∘a) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
 have j: ∀ᶠ r:ℕ in atTop,Hosp S ((K).c (momentm Y (π₀ r) s)):= Q.growsA.tendsto_atTop.eventually (hosp_later Y H V s S)
 filter_upwards [j,e δ hd, v.eventually (turning Y H U S₀),Q.growsA.tendsto_atTop.eventually ((boutique Y H V S₀ U).2 δ hd)] with r t₀ e t h
 intro n t'; refine ⟨t₀,t,?_⟩; intro F f x y G Z
 have hz:G=F₀ z r S F:=rfl; have hu:Z=X z F:=rfl
 have w:= e _ f x y; obtain ⟨m,m',d,c⟩:= w
 have hx:InTest K true S₀ false G:=prepared_train Y H s S z n t' f
 obtain ⟨hv,g⟩:=proceeds Y H Q.circuit s z f
 have hZ:InTest K true S₀ false Z:=hv
 obtain ⟨he,hy⟩:= h G hx _ t.hosp _ (m' _)
 have hh₁:=hy (b r) (Q.gate r)
 have hg: ‖E U G-E U Z‖≤C*(δ*x):=by rw [←E_sub Y H V _ (aux_test hx) (aux_test hZ)]; exact E_bound Y H V _ S₀ (InTest.subOp hx hZ) d
 have ht(j:ℂ)(w:‖j-E U G‖≤δ*(A*x)):‖j-E s F‖≤ε*x:=by
    change E U Z=E s F at g; rw [←g]; apply (norm_sub_le_norm_sub_add_norm_sub j (E U G) (E U Z)).trans ((add_le_add w hg).trans ?_)
    have hx:δ*(A+C+1)=ε:=div_mul_cancel₀ _ (by positivity); have hu:δ*A+C*δ≤ ε:=by nlinarith
    calc
      _ = (δ*A+C*δ)*x:=by ring
      _≤ _:= mul_le_mul_of_nonneg_right hu (pay_nonneg y)
 refine ⟨ht _ he,ht _ hh₁,?_⟩ -- goals binder structure? intro placed before and fields! fix
 change E U Z=E s F at g; rw [←g]; have he':= (h Z hZ _ t.hosp _ (m _)).2 (b r) (Q.gate r); apply he'.trans
 have hx:δ*(A+C+1)=ε:=div_mul_cancel₀ _ (by positivity); have hu:δ*A≤ ε:=by nlinarith
 rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hu (pay_nonneg y)
end
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.pirouette
