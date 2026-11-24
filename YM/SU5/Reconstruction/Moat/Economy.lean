import YM.SU5.Reconstruction.Moat.Bank
import YM.SU5.Reconstruction.Moat.Sonic
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
open Anvil
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
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
namespace Reflector
variable (F: ∀ j:Axis, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
  (S : ∀ j:Axis, Forward (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))))
variable (j:Axis) (M u v ε:ℝ) (hu:0<u) (hv:0≤v)(e:0<ε)
local notation "Pv"=> (S₀ j).ℚmeasure.region (Moat.band j u v)
private lemma invocation {u g:ℝ}(p:u<g) : ∃ r:marks (timeMesh Λ), u<(r:ℝ)∧ (r:ℝ)<g:= by
 obtain ⟨x,h,w'⟩:=(daylight (timeMesh Λ)).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr p); exact ⟨⟨x,h⟩,w'⟩
include hu hv e F S
open Moat
local notation "Θ" x:max=>sidePay j x
set_option maxHeartbeats 390000 in
lemma economy : ∃ h> (0:ℝ),∀ (t:marks (timeMesh Λ)),0≤ (t:ℝ)→(t:ℝ) ≤ h→∀ (p:Sky (tent Y H)) (q: Licensed Y H V G C a χ p t M),
     ‖Pv ((Vo j) (outgoing Y H G j p t (q j).registers))‖^2+‖Pv ((Vo j) (returning Y H V G j p t (q j).registers))‖^2< ε^2:= by
 let L:=1/(8*(v+1)); let B:=u*Real.exp (-u*2); have hp:0<L:= by unfold L; positivity
 have bp:0<B:= by unfold B; positivity
 let S':= 3*M^2+1; have P':0<S':=by unfold S'; positivity
 obtain ⟨n,q,hq⟩:= ((eventually_gt_atTop 0).and (winnow ε e bp hp S' P' M)).exists
 let nn:ℝ:= (n:ℝ); have hn:0<nn:=Nat.cast_pos.mpr q; change 0 < (n:ℕ) at q
 have t₀:1≤nn:= (Nat.one_le_cast.mpr q) -- cast issue; norm_num etc
 obtain ⟨r,hr,r'⟩:= invocation (Λ:=Λ) (show 1/nn^5<(2:ℝ)/nn^5 by gcongr; norm_num)
 obtain ⟨s,hS,S₁⟩:= invocation (Λ:=Λ) (show L/nn^2<(2*L:ℝ)/nn^2 by gcongr; linarith)
 let a':= L/(4*nn^2); have hb:0<a':=by unfold a'; positivity
 have hx:0<(r:ℝ):=lt_trans (by positivity) hr; have ys:0<(s:ℝ):=lt_trans (by positivity) hS
 refine ⟨min a' (r:ℝ), lt_min hb hx,?_⟩
 intro t p₀ v₀ x q'
 have Qe : B * (r:ℝ) ≤ 1 - Real.exp (-u*(r:ℝ)):= by
   have he:(r:ℝ) ≤ 2:= r'.le.trans (div_le_self (by norm_num) (one_le_pow₀ t₀))
   calc
      _ ≤ u * Real.exp (-u*(r:ℝ))*(r:ℝ):= by unfold B; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left he (by linarith))) hu.le) hx.le
      _ = u*(r:ℝ)*Real.exp (-(u*(r:ℝ))):= by rw [← neg_mul]; ring
      _ ≤ 1- Real.exp (-(u*(r:ℝ))):= exp_board (by positivity)
      _ = _:= by rw [neg_mul]
 let z:= chorale (a:=j) (n:=n^2) s; let N:= Fintype.card (Moat.Choir j (n^2))
 have hm(i k':Moat.Choir j (n^2)):v*‖Θ (z i)-Θ (z k')‖ ≤ 1:= by
    have hz(i:Moat.Choir j (n^2)): ‖Θ (z i)‖ ≤ 4*L:= by
       have he:2*((n^2:ℕ)*(s:ℝ))≤4*L:= by rw [Nat.cast_pow]; change 2*(nn^2*(s:ℝ)) ≤ _; nlinarith only [(le_div_iff₀ (by positivity : 0<nn^2)).mp S₁.le]
       exact (Moat.balanced i s ys.le).trans he
    have Hq: ‖Θ (z i)- Θ (z k')‖ ≤8*L:= (norm_sub_le ..).trans ((add_le_add (hz i) (hz k')).trans_eq (by ring)); apply (mul_le_mul_of_nonneg_left Hq hv).trans
    unfold L; field_simp; linarith
 let b':ℝ≥0:= ⟨a',hb.le⟩
 have bp':∀ i k':Moat.Choir j (n^2), i≠k' → ∃ k:Axis,k≠j ∧ (((b'+b':ℝ≥0):ℝ)+(t:ℝ)≤ ((z i-z k') k:ℝ)∨ ((b'+b':ℝ≥0):ℝ)+(t:ℝ)≤ ((z k'-z i) k:ℝ)):= by
    intro i k0 e; obtain ⟨k',hx0,g⟩:= Moat.interval i k0 s ys.le e; change ((z k0 k':ℝ) + s ≤ (z i k':ℝ) ∨ (z i k':ℝ)+s ≤ (z k0 k':ℝ)) at g; refine ⟨k',hx0,?_⟩
    have p': (t:ℝ) ≤ a':= v₀.trans (min_le_left ..); change a'+a'+(t:ℝ) ≤ ((z i k':ℝ) - (z k0 k':ℝ)) ∨ _ -- coe_sub not def? for subgroup yes
    change _∨ a'+a'+(t:ℝ)≤ (z k0 k':ℝ)-(z i k':ℝ)
    have e': L/nn^2=4*a':= by unfold a'; ring
    rcases g with g|g; · left; linarith
    right; linarith
 have H₁ := spectral_receipt Y H V G C a χ F S j u v M q' z (fun i=> chorale_head i s) hm r p₀ (v₀.trans (min_le_right ..)) b' hb bp' B bp.le Qe
 dsimp only at hq H₁
 rw [show Fintype.card (Moat.Choir j (n^2))=n^6 from ((choir_card j (n^2)).trans (by ring)), Nat.cast_pow] at H₁
 have hxv : 3*M^2*(r:ℝ)^2/(b':ℝ)^2 ≤ S'*(r:ℝ)^2/a'^2:=by unfold S'; change _≤ _ / (b':ℝ)^2; gcongr; linarith
 let K':=(nn^6)^2/2*(B*(r:ℝ)); have hk : 0<K':=by unfold K'; positivity
 apply lt_of_mul_lt_mul_left ?_ (le_of_lt hk)
 apply lt_of_le_of_lt H₁; refine lt_of_le_of_lt ?_ (hq (r:ℝ) hr.le r'.le)
 gcongr
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
