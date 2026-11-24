import YM.SU5.FiniteGaugeData.Tower.Ark
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
# Convergence directly to the mixed PSD system

Choose any two fixed levels and supported marks on buffered side, any common
finer resolution. Advance the two separately (geometric clearance checked
on projected lifts, different levels needn't be compared on any same-period
stencil until that level), then reflect and multiply *on that level*. The
entries are paid sharp ratios and converge to mixed `kennel`, no single-period
heat formula asserted for these off diagonals. Uniform on varying first,second
input fields with common norm bounds on those fixed supports. Can in particular
use in a finite-volume-lower criterion involving separation of reflection
charges across the tower (instead of the one-functional W theorem), only need
charge the finite marked ratios.
-/
open Fock
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ} (Q: Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
section analytic
variable (P:Calibration){F G X Y₀:Family P}{x y u v:ℝ}
lemma pay_flips{F:Family P}(t:pay F x)(z:Axis)(i:ℤ): pay (mirror P z i F) x:=by intro k v; change ‖Fock.theta _ _‖ ≤ _; rw [theta_fee]; exact t k _
lemma foil{j:Axis}{z:ℤ}: mirror P j z (F-G)=mirror P j z F-mirror P j z G:=by rw [sub_eq_add_neg,← neg_one_smul ℂ G,mirror_plus,mirror_scale,star_neg,star_one,neg_one_smul,sub_eq_add_neg]
lemma floral (t:pay (F-X) u)(p:pay (G-Y₀) v)(w:pay G y)(h:pay X x):
    pay (F*G-X*Y₀) (u*y+x*v):= by
 rw [show F*G-X*Y₀=(F-X)*G + X*(G-Y₀) from by rw [ _root_.sub_mul,mul_sub]; abel]
 exact pay_add (pay_mul t w) (pay_mul h p)
lemma floral_mir (j:Axis)(z:ℤ)(t:pay (F-X) u)(p:pay (G-Y₀) v)(w:pay G y)(h:pay X x):pay (mirror P j z F*G-mirror P j z X*Y₀) (u*y+x*v):=by
 apply floral P _ p w (pay_flips P h j z); rw [←foil]; exact pay_flips P t j z
end analytic
local notation "P"=> tent Y H
variable (j:Axis)(z:ℤ)
local notation "π₀" r:max=>i (a r)
local notation "κ" r:max=>k (b r)
local notation "F₀" s:max z:max r:max S:max F:max=>train Y H s z (π₀ r) (κ r) S F
local notation "W" S:max z:max=>volumeAround Λ l z S
local notation "X" s:max z:max F:max=>stream Y H D s z F
local notation "ω" i:max => meshface (Λ:=Λ) z i
variable (s₁ s₂:ℕ)(S₁ S₂:Finset Cover)
local notation "A" s:max =>Clock Y H s j z
local notation "θ" t:max => mirror P j (ω t)
-- the family on upper lattice that will compute the entry at that pair of
-- FINITE resolutions.
def stageGram (r h:ℕ)(F G:Family (tent Y H)):Family (tent Y H) := (mirror (tent Y H) j (meshface (Λ:=Λ) z h) (train Y H s₁ (h-s₁) (i (a r)) (k (b r)) S₁ F))*train Y H s₂ (h-s₂) (i (a r)) (k (b r)) S₂ G
local notation "Sφ"=>stageGram Y H (i:=i) (a:=a) (k:=k) (b:=b) j z s₁ s₂ S₁ S₂
local notation "R"=> kennel Y H Q.circuit j z
abbrev costRoom (t:ℕ):= reflectedBox j (meshface (Λ:=Λ) z t) (volumeAround Λ l (t-s₁) S₁)∪ volumeAround Λ l (t-s₂) S₂
include V Q
lemma last_cost (t:ℕ)(p:s₁≤ t)(q:s₂ ≤ t):∃ C:ℝ,0≤C∧∀ ε:ℝ,0<ε→ ∀ᶠ r:ℕ in atTop, ∀ (x:A s₁)(y:A s₂),
  InTest P true S₁ false x.val → InTest P true S₂ false y.val →
    ∀ u v:ℝ,pay x.val u→pay y.val v→
      let Z:= Sφ r t x.val y.val; let Y₀:= R ⟨s₁,x⟩ ⟨s₂,y⟩
      InTest P true (costRoom (Λ:=Λ) (l:=l) j z s₁ s₂ S₁ S₂ t) false Z ∧ pay Z (C*u*v) ∧ Ferry Y t (π₀ r) (κ r) ∧
       ‖sharp Y H t (π₀ r) (κ r) Z-Y₀‖≤ ε * u * v ∧ ‖I t Z (π₀ r)-Y₀‖ ≤ ε*u*v:=by
 let s₀:=t-s₁; let t₀:= t-s₂
 obtain ⟨B,V₁,D₁⟩:= fares Y H s₁ Q S₁ s₀
 obtain ⟨C,V₂,D₂⟩:= fares Y H s₂ Q S₂ t₀
 let Z:=costRoom (Λ:=Λ) (l:=l) j z s₁ s₂ S₁ S₂ t
 let T:= toll Y H t Z; have ht:0≤T:=(toll_pays Y H ..).1
 refine ⟨B*C,by positivity,fun ε e=>?_⟩
 let δ:= ε / (B*C+T*(B+C)+1); have hδ:0<δ:=by unfold δ; positivity
 filter_upwards [D₁ δ hδ,D₂ δ hδ,Q.finance t, Q.growsA.tendsto_atTop.eventually (hosp_later Y H V t Z),Q.growsA.tendsto_atTop.eventually ((boutique Y H V Z t).2 δ hδ)] with r Dv D' E0 J j' x y hx hy u v h g
 have w:= Dv _ hx u h; have W':= D' _ hy v g
 let F:= F₀ s₁ s₀ r S₁ (x.val); let G:= F₀ s₂ t₀ r S₂ (y.val)
 let F':=X s₁ s₀ (x.val); let G':=X s₂ t₀ (y.val)
 let A₀:= (θ t) F*G; let G₀:=(θ t) F'*G'; change InTest (tent Y H) true Z false A₀ ∧ _
 have hf' := (proceeds Y H Q.circuit s₁ s₀ hx).1; have hg':= (proceeds Y H Q.circuit s₂ t₀ hy).1
 have hF: InTest P true Z false G₀:= (InTest.mul ((axial P j (ω t) hf').mono subset_union_left) (hg'.mono subset_union_right))
 have hG: InTest P true Z false A₀:=(InTest.mul ((axial P j (ω t) (prepared_train Y H s₁ S₁ s₀ (π₀ r) (κ r) hx)).mono subset_union_left) ((prepared_train Y H s₂ S₂ t₀ (π₀ r) (κ r) hy).mono subset_union_right))
 have a:pay (A₀-G₀) (δ*u*(C*v)+B*u*(δ*v)):= floral_mir P j (ω t) w.2.2.1 W'.2.2.1 W'.2.1 w.1
 have p':pay A₀ ((B*C)*u*v):=by
    have he:(B*C)*u*v=B*u*(C*v):=by ring
    rw [he]; exact pay_mul (pay_flips P w.2.1 j (meshface (Λ:=Λ) z t)) W'.2.1
 refine ⟨hG,p',E0,?_⟩
 obtain ⟨l,d⟩:= j' A₀ hG _ J _ (p' _)
 have d':= d (b r) (Q.gate r)
 let x₀:Voice Y H j z:=⟨s₁,x⟩; let y₀:Voice Y H j z:=⟨s₂,y⟩; have hZ:R x₀ y₀=E t G₀:= vitals Y H Q.circuit j z x₀ y₀ p q
 have hx0:0≤u:=pay_nonneg h; have hy0:=pay_nonneg g
 have J₀: ‖E t A₀-E t G₀‖ ≤ T*(δ*u*(C*v)+B*u*(δ*v)):=by rw [←E_sub Y H V t (aux_test hG) (aux_test hF)]; exact E_bound Y H V t Z (InTest.subOp hG hF) a
 have ht(y:ℂ)(h:‖y-E t A₀‖≤δ*((B*C)*u*v)): ‖y-R x₀ y₀‖ ≤ ε*u*v:=by
    rw [hZ]; apply (norm_sub_le_norm_sub_add_norm_sub y (E t A₀) (E t G₀)).trans ((add_le_add h J₀).trans ?_)
    have hv:δ*(B*C+T*(B+C)) ≤ ε:=by have hv: δ*(B*C+T*(B+C)+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
    calc
      _= δ*(B*C+T*(B+C))*u*v:=by ring
      _≤ _:=by gcongr
 exact ⟨ht _ d',ht _ l⟩

lemma sees {x : A s₁}{y:A s₂}(p:InTest P true S₁ false x.val)(q:InTest P true S₂ false y.val)(t:ℕ)(a₁:s₁ ≤ t)(a₂:s₂ ≤ t):
 Tendsto (fun r=>sharp Y H t (π₀ r) (κ r) (Sφ r t x.val y.val)) atTop (𝓝 (R ⟨s₁,x⟩ ⟨s₂,y⟩)):=by
 obtain ⟨C,p₀,g⟩:= last_cost Y H V Q j z s₁ s₂ S₁ S₂ t a₁ a₂
 obtain ⟨u,v⟩:= Journey.valuation Y H p; have hu:pay x.val u:=v
 obtain ⟨w,k⟩:= Journey.valuation Y H q; have hw:pay y.val w:=k
 have hp:=pay_nonneg hu; have ht:=pay_nonneg hw
 apply Metric.tendsto_nhds.mpr; intro e he
 let δ:=e/(u*w+1); have hd:0<δ:=by unfold δ; positivity
 filter_upwards [g δ hd] with i h; rw [dist_eq_norm]; refine lt_of_le_of_lt (h x y p q u w hu hw).2.2.2.1 ?_
 have hx:δ*(u*w+1)=e:=div_mul_cancel₀ _ (by positivity); nlinarith
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.sees
