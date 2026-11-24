import YM.SU5.Reconstruction.UVPrice.HeatCluster
import YM.SU5.Reconstruction.UVPrice.PayLow
/-!
# Optional soft stamp prices in the actual physical law. Build helpers.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Roy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "F₀"=> osValue Y H V G a (C a) χ
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "L" i:max=> lowland i 0
local notation "Φ"=> move (tent Y H)
variable (p : ∀ j, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
local notation "Θ"=> F₀
local notation "Gq"=> Ds Set.univ
local notation "T"=> lug Y H V G C a χ
local notation "Q" i:max=> Coupon i (marks (timeMesh Λ))
variable (Ht:Hearth (peninsula Y H V G.history G.clipped j' false (C j') (displacement Y H V G.history G.clipped a false (C a) χ j' (C j'))) (vocation Y H V G.history G.clipped j' false (C j') (displacement Y H V G.history G.clipped a false (C a) χ j' (C j'))))
local notation "Uh" i:max=> (Ds (N i))
local notation "κ"=> (Os j)
local notation "α" i:max=> move (tent Y H) (eject j' i)
local notation "B"=> Coupon.tagT (Γ:=marks (timeMesh Λ)) (S₀ j)
include V hv
lemma canTwin (d:ℕ→Gt)(c:Tendsto (fun i=>(d i:ℝ)) atTop atTop)(x y:Ds (N j)) : ∃ f:ℕ→ Ds (N j),∀ᶠ i in atTop,(f i).val=x.val* (α (d i)) y.val:= by
 obtain ⟨U,e,r,z⟩:= (compact_domain Y H G).1 x.property; obtain ⟨W,k,h,ht⟩:= (compact_domain Y H G).1 y.property
 obtain ⟨u',u,u₁,u₂⟩:= Schedule.shutters (daylight (timeMesh Λ)) j' e; obtain ⟨s,s',v,t⟩:= Schedule.shutters (daylight (timeMesh Λ)) j' k
 let f(i):= x.val*(α (d i)) y.val; let F(i) := if p:f i∈ Ds (N j) then (⟨_,p⟩ : Ds (N j)) else x
 have he:∀ᶠ i in atTop, f i∈ Ds (N j):=by
   filter_upwards [c.eventually (eventually_ge_atTop ((u:ℝ)-(s:ℝ)))] with i hj
   let p:= eject j' (d i); let V':=slides (coordinates Λ p) W
   have hs: V'⊆ N j:= (image_mono h).trans (even_flank j p (by simp [p,hv.symm] : 0 ≤ 0 + coordinates Λ p j))
   refine domain_mult_to Y H G z (moving Y H V G p _ ht) (Set.disjoint_left.mpr ?_) r hs
   rintro _ g ⟨x,h,rfl⟩; have he:= (u₂ _ g).2; change _ + coordinates Λ p j' < _ at he
   unfold p at he; rw [coordinates_eject,eject_at] at he; linarith [(t x h).1,(show (u:ℝ)-(s:ℝ) ≤ (d i:ℝ) from hj)]
 refine ⟨F,?_⟩; filter_upwards [he] with i k; unfold F; rw [dif_pos k]
omit hv
noncomputable def seqc (x y :Ds (N j))(z:Coupon j (marks (timeMesh Λ))) : Ds Set.univ:=⟨(θ j) x.val * Φ z.stamp y.val,paired_forever Y H G j x.val (crawl Y H V G j z.stamp z.ground y).val x.property (crawl Y H V G j z.stamp z.ground y).property⟩
local notation "St"=> seqc Y H V G j
include p
lemma audienc (x y: Ds (N j))(z : Q j) : inner ℂ (κ x) (Coupon.cash (S₀ j) z (κ y))= T (seqc Y H V G j x y z):= by
 obtain ⟨b,h⟩:= comeBy Y H V G C a χ j p x y z.stamp z.ground; exact h
include hv Ht
lemma onTwins (d:ℕ→Gt)(c:Tendsto (fun i=>(d i:ℝ)) atTop atTop)(x y:Ds (N j)) (f:ℕ→Ds (N j))(u:∀ᶠ i in atTop,(f i).val=x.val* (α (d i)) y.val) :
    Tendsto (fun i=> B (κ (f i))) atTop (𝓝 (B (κ x) * B (κ y))):= by
 apply tendsto_pi_nhds.mpr; intro z
 obtain ⟨b,r,v⟩:= clusters_roll Y H V G C a χ j' p Ht d c (St x x z) (St y y z)
 have he(f:Ds (N j)): T (St f f z)= B (κ f) z:= (audienc Y H V G C a χ j p f f z).symm
 rw [he,he] at v; refine v.congr' ?_; filter_upwards [r,u] with i q e; change T (b i) = B _ _
 rw [← he]; apply congrArg T; apply Subtype.ext; change _ = (St _ _ _).val; rw [q]; change ((θ j) _* Φ _ _) * (α (d i)) ((θ j) _ * Φ _ _) =(θ j) (f i).val* Φ z.stamp (f i).val
 rw [e]; let t:= eject j' (d i); have hb: reverseOne j t=t:= by
   ext1 v; by_cases h:v=j
   · subst v; unfold reverseOne; simp [t,hv.symm]
   simp [reverseOne,h]
 rw [flipMark_mul, move_prod,move_prod]
 rw [flipped_moves Y H j t _,hb,move_sum,move_sum,add_comm t] -- tune order
 ring
-- no postulating Spectrum locality etc. ADD due to this same state
include Ht hv
lemma produces (x y:Ds (N j)) : B (κ x)* B (κ y) ∈ Coupon.Population (S₀ j) (marks (timeMesh Λ)):= by
 obtain ⟨d,k,t⟩:= towards Λ; obtain ⟨f,u⟩:= canTwin Y H V G j j' hv d t x y
 exact mem_closure_of_tendsto (onTwins Y H V G C a χ j j' hv p Ht d t x y f u) (Eventually.of_forall (fun i=> mem_range_self (κ (f i))))
local notation "Cup"=> Coupon.Population (S₀ j) Gt
lemma bilinear_mul (x y:(Q j→ℂ))(e:x∈ Cup)(v:y∈ Cup): x*y∈ Coupon.Population (S₀ j) (marks (timeMesh Λ)):=by
 let S:= Set.range fun x:Ds (N j)=> B (κ x)
 have ht: Cup⊆ closure S:= by
    apply closure_minimal ?_ isClosed_closure; rintro _ ⟨x,rfl⟩
    have he:= image_closure_subset_closure_image (s:=range ⇑(Os j)) (Coupon.tag_conti (Γ:=marks (timeMesh Λ)) (S₀ j))
    have hs: B '' (range ⇑(Os j))=S:= by rw [← range_comp]; rfl
    rw [←hs]; exact he ⟨x,compass_domain_dense Y H V G j (C j) (w j) x,rfl⟩
 refine closure_minimal (t:={x| x*y∈Cup}) ?_ (isClosed_closure.preimage (continuous_id.mul continuous_const)) (ht e); rintro _ ⟨x,rfl⟩
 refine closure_minimal (t:={y| B (κ x)*y∈ Cup}) ?_ (isClosed_closure.preimage (continuous_const.mul continuous_id)) (ht v)
 rintro _ ⟨y,rfl⟩; exact produces Y H V G C a χ j j' hv p Ht x y
lemma additive (v:Backs (S₀ j))(x y:E4)(h:x∈ Shelf (S₀ j))(t:y∈ Shelf (S₀ j)): x+y∈ Shelf (S₀ j):= by
 let hx:= shelf_ePays _ _ h; let ht:= shelf_ePays _ _ t
 refine Coupon.in_price (S₀ j) (daylight (timeMesh Λ)) v _ (add_nonneg hx ht) ?_
 convert bilinear_mul Y H V G C a χ j j' hv p Ht (Coupon.receipt x) (Coupon.receipt y) (Coupon.climb (S₀ j) x h) (Coupon.climb (S₀ j) y t) using 1
 funext i; exact Coupon.receipts_add i x y hx ht
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
