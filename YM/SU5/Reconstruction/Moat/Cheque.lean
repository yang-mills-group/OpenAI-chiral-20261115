import YM.SU5.Reconstruction.Moat.Shift
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
variable (j b:Axis)(x:Sky (tent Y H))(t: marks (timeMesh Λ))(z : placement Λ)
local notation "r̂"=> reversion (tent Y H) Λ

def outgoing (p:x∈ Domain Y H G false (Chambers.strip j 0 (t:ℝ))): Domain Y H G false (flank j 0):= ⟨x,domain_mono Y H G (Chambers.strip_in j _) p⟩
def returning (p:x∈ Domain Y H G false (Chambers.strip j 0 (t:ℝ))): Domain Y H G false (flank j 0):= outgoing Y H G j (r̂ j t x) t (pose Y H V G j t x p)
-- Budget for price also star version. Can be charged EVEN before Back.Ass fot.
structure Billable (u:ℝ):Prop where
 registers : x∈ Domain Y H G false (Chambers.strip j 0 (t:ℝ))
 positive : ‖(OSvector Y H V G j (C j) (w j)) (outgoing Y H G j x t registers)‖≤ u
 negative : ‖(OSvector Y H V G j (C j) (w j)) (returning Y H V G j x t registers)‖ ≤ u
local notation "UP₀" i:max p:max=> (outgoing Y H G i x t p)
local notation "DN₀" i:max p:max=> (returning Y H V G i x t p)
variable {u:ℝ}(iT: Billable Y H V G C a χ j x t u)(bT: Billable Y H V G C a χ b x t u)(p:b≠j)
local notation "Ξ" i:max p:max=> (Vo i) (UP₀ i p)
local notation "Δ" i:max p:max=> (Vo i) (DN₀ i p)
local notation "TT" i:max p:max d:max=> Moat.tariff (S₀ i) p d
variable (F: ∀ j:Axis, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
  (S : ∀ j:Axis, Forward (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))))
include F
lemma voicebill (f:Domain Y H G false (flank j 0)): ‖(Vo j) f‖=‖(X j) f‖:= congrArg norm (voice_full Y H V G j _ _ (F j) f)
include F S iT bT p
set_option maxHeartbeats 300000 in
lemma launch (sf:marks (timeMesh Λ))(h:0≤(t:ℝ))(he:(t:ℝ)≤ sf)(hz:z j=0) (b':ℝ≥0)(v:0<b')(r:b'+(b':ℝ)+(t:ℝ) ≤ (z b:ℝ)) :
   Moat.tariff (S₀ j) ((Vo j) (outgoing Y H G j x t iT.registers)) (Real.toNNReal (sf:ℝ)) (sidePay j z)+
   Moat.tariff (S₀ j) ((Vo j) (returning Y H V G j x t iT.registers)) (Real.toNNReal (sf:ℝ)) (sidePay j z) ≤ 3*u^2*(sf:ℝ)^2/(b':ℝ)^2:= by
 let d:=UP₀ j iT.registers; let e:=DN₀ j iT.registers; let R: Gt:=sf; let t' := ℜ (R:ℝ)
 let yb:=UP₀ b bT.registers; let vb:=DN₀ b bT.registers; let w0:= (⟨_,sidestamp Y H G b j p vb⟩: D' b)
 let c₀:= Real.toNNReal ((z b:ℝ) - (t:ℝ)); let k:=transversal b j p.symm; let L:= (Vo b) w0; let Z:= (Vo b) yb
 let U (q:OS.Cross b):= inner ℂ L ((S₀ b).U q ((S₀ b).E c₀ Z)); let s:=sidePay b z; let sj:=sidePay j z; let Z₀(q: Gt):= U (s+(q:ℝ) • k)
 have H₁: (t:ℝ) ≤ (z b:ℝ):= by have ht: 0 < (b':ℝ):= v; linarith
 have hb : b'+b' ≤ c₀:= (show ((b'+b':ℝ≥0):ℝ) ≤ (c₀:ℝ) from (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr H₁),NNReal.coe_add]; linarith))
 have pF(q:Gt): Fund Y H V G C a χ ((θ j) x*m₁ (z+eject j q) x) (Z₀ q):= Fund.lateral Y H V G C a χ j b p (F b) z t yb vb w0 rfl rfl q H₁
 have k' (q:Gt)(u:0≤(q:ℝ)): Moat.note (S₀ j) ((Vo j) d) (ℜ q) sj=Z₀ q:= Fund.unique Y H V G C a χ (Fund.focus Y H V G C a χ j z q (F j) d hz u) (pF q)
 have d' (q:Gt)(u:0≤(q:ℝ)): Moat.note (S₀ j) ((Vo j) e) (ℜ q) (-sj)=Z₀ (-t-t-q):= Fund.unique Y H V G C a χ (Fund.reverse Y H V G C a χ j z t q (F j) (show e.val= r̂ j t d.val from rfl) hz u) (pF (-t-t-q))
 let Z':= sidePay j z -- already q
 let J:=(sidePay j z); let n:= -t - t -R; let y':=(R:ℝ) • k; let X':= (n:ℝ) • k
 have M0 : (ℜ ((0:Gt):ℝ))=0:= by simp
 rw [← Moat.probate (S₀ j) ((Vo j) e) (Real.toNNReal (sf:ℝ)) J]; unfold Moat.tariff
 change (Moat.note (S₀ j) _ 0 sj-Moat.note (S₀ j) _ _ sj).re+(Moat.note (S₀ j) _ 0 (-sj)-Moat.note (S₀ j) _ _ (-sj)).re ≤ _
 rw [← M0,k' 0 (by simp), d' 0 (by simp), k' sf (h.trans he), d' sf (h.trans he), ←Complex.add_re]
 have u' : - t - t=n+ R := by unfold n; abel
 have hd: 0≤ (R:ℝ):= h.trans he
 -- rearranges into Moat.four
 have hL : ‖L‖≤u:= by unfold L; rw [voicebill Y H V G C a χ b F, mirrorsize Y H V G C a χ b j p vb w0 rfl]; exact bT.negative
 have hR: ‖Z‖ ≤ u:=(voicebill Y H V G C a χ b F yb).trans_le bT.positive
 have hS : Z₀ 0-Z₀ sf+(Z₀ (-t-t-(0:Gt))-Z₀ (-t - t - sf))= inner ℂ L (Moat.four (S₀ b) s y' X' c₀ Z):=by
     -- hazard reverse rw [u'] loops; change one
     change Z₀ 0- Z₀ R+(Z₀ _- Z₀ n) = _
     rw [sub_zero,u']; unfold Z₀ U Moat.four X' y'; rw [AddSubgroup.coe_add,add_smul,←add_assoc]; simp only [AddSubgroup.coe_zero,zero_smul,add_zero,mul_apply_eq_comp,_root_.sub_apply,_root_.add_apply,inner_sub_right,inner_add_right]; abel
 rw [hS]; set N:=Moat.four (S₀ b) s y' X' c₀; have hu: 0≤u:=(norm_nonneg _).trans hL
 have hn: ‖N‖≤ (sf:ℝ)/(b':ℝ) *(3*(sf:ℝ)/(b':ℝ)):= by
     apply (Moat.four_knobs (S₀ b) (S b) c₀ b' v hb s y' X').trans
     have h₀ : |(n:ℝ)| ≤ 3*(sf:ℝ):= by apply abs_le.mpr; dsimp only [n,R]; push_cast; constructor<;>linarith
     dsimp only [N,y',X']; rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hd, show ‖k‖=1 from transversal_norm _ _,mul_one,mul_one]; gcongr -- R unfolds
 calc
    _ ≤ _:= (Complex.re_le_norm _).trans ((norm_inner_le_norm L _).trans (mul_le_mul hL ((N.le_opNorm _).trans (mul_le_mul hn hR (norm_nonneg _) (by have he:=h.trans he; positivity))) (norm_nonneg _) hu))
    _ ≤ _ := by ring_nf; apply le_refl -- reflex

end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
