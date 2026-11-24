import YM.CF.Wray.Native
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
variable (P0:BudgetPoint) (o:Seat N) (X V_:Support (More N))(K_:ℕ)
variable (tH:o∈X)
-- Scale aperture.K.Root ext. stage ∣∆∣ estimation.
abbrev surgeL (P: BudgetPoint)(X:Support (More N))(k:ℕ):ℝ:= (1+((coverNumber k X * (4*k+2)+2*k):ℝ))^P.power
def rodV : dN→L[ℝ]dN:= ((P0.threshold)⁻¹ • highlight X).comp ((wakeB (unrest V_ P0.B)).comp (Prism.trunk P0 o))
local notation "λd"=> rodV P0 o X V_
local notation "C₀"=> surgeL P0 X K_
include tH
lemma rootA : 1 ≤ C₀:=one_le_pow₀ (le_add_of_nonneg_right (by positivity))
lemma lens_x: ‖λd‖≤ C₀:=by
 let h:=P0.threshold_pos; refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (rootA P0 o X K_ tH)) fun i=> (pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans (rootA P0 o X K_ tH)) (norm_nonneg _))).mpr fun j=>?_
 let c:=P0.threshold; have hx:0< c:=h; have he:0 ≤ C₀*‖i‖:=mul_nonneg (zero_le_one.trans (rootA P0 o X K_ tH)) (norm_nonneg _); simp only [rodV,ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply, highlight,ContinuousLinearMap.pi_apply]; split; swap; · rw [ContinuousLinearMap.zero_apply, smul_zero,norm_zero]; exact he
 rename_i ht; have ht:=ht (mem_insert_self ..); rw [ContinuousLinearMap.proj_apply,steadyB]; split; swap; · rw [smul_zero,norm_zero]; exact he
 change ‖c⁻¹ • (((c :ℝ)*(1+(separation j.1 o:ℝ))^P0.power) • i j)‖≤ _; rw [smul_smul,inv_mul_cancel_left₀ hx.ne',norm_smul,Real.norm_of_nonneg (pow_nonneg (by positivity) _)]; refine mul_le_mul ?_ (norm_le_pi_norm i j) (norm_nonneg _) (zero_le_one.trans (rootA P0 o X K_ tH)); unfold surgeL; gcongr; exact_mod_cast Corona.extent _ _ ht tH
abbrev pegR := C₀⁻¹ • rodV P0 o X V_
local notation "T'"=> pegR P0 o X V_ K_
lemma ethic : ‖T'‖ ≤ 1:=by
 have ht:= zero_lt_one.trans_le (rootA P0 o X K_ tH); rw [pegR,norm_smul,Real.norm_of_nonneg (by positivity :0≤ C₀⁻¹),inv_mul_le_iff₀ ht,mul_one]; exact lens_x P0 o X V_ K_ tH
variable {U:Pane N}{Xz:tangD N}
lemma shore(i:dN): C₀ • T' i= λd i:=smul_inv_smul₀ (zero_lt_one.trans_le (rootA P0 o X K_ tH)).ne' _
omit tH
variable {P': Monk SU.group S}
lemma stoveV (p:P0.threshold=temp x)(t:dN) : Agrees X (gyrate (unrest V_ P0.B) U (Prism.trunk P0 o t)) (Vmove x U (λd t)):=by
 intro i h v; have ht:pinPos i⊆X:= insert_subset h (singleton_subset_iff.mpr v); unfold Vmove rodV gyrate highlight
 simp only [RG.increment,ContinuousLinearMap.comp_apply,Pi.smul_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.pi_apply,if_pos ht,p.symm]; rw [smul_inv_smul₀ (P0.threshold_pos.ne')]; rfl
lemma axel (t:dN) (hp:1000 ≤ P0.B): let Z:= P0.threshold • T' t; axl V_ Z=Z ∧ wakeB (unrest V_ P0.B) Z=Z :=by
 intro Z
 have he(i:Bond (More N))(p:i∉unrest V_ P0.B): Z i=0:=by
    unfold Z pegR rodV; simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply, highlight,ContinuousLinearMap.pi_apply]; split; · rw [ContinuousLinearMap.proj_apply,steadyB,if_neg p]; simp
    simp -- indentation
 constructor
 · funext i; unfold axl; split; rename_i hv; symm; refine he i fun k=>?_ ; let H:halo 15 V_⊆halo (5*P0.B) V_:=Corona.halo_mono (by omega) (Subset.refl _); cases hv with | inl h=>exact Finset.disjoint_left.mp (mem_filter.mp k).2 (mem_insert_self ..) (H h) | inr h=> exact Finset.disjoint_left.mp (mem_filter.mp k).2 (mem_insert_of_mem (mem_singleton_self _)) (H h)
   rfl
 funext i; rw [steadyB]; split_ifs with h; rfl; exact (he _ h).symm
local notation "O'"=> Rue.litres P0.threshold X V_
variable {Y_: Type}[NormedAddCommGroup Y_][NormedSpace ℝ Y_][FiniteDimensional ℝ Y_]
variable (f:Pane N→ ℂ)
lemma turfH (w:U∈O') (Q: dN→L[ℝ]dN) (x:ℝ): ∀ᶠ y:dN in 𝓝 0,Vmove x U (Q y)∈Rue.litres P0.threshold X V_:=by
 let V(t:dN):= Vmove x U t
 have hk:Continuous V:=by unfold V Vmove RG.increment; apply continuous_pi; intro j; fun_prop
 have ht:= (hk.comp Q.continuous).tendsto 0; have hp:(V ∘ Q) 0= U:=by simp [V,Vmove]; -- indent
 rw [hp] at ht; exact ht.eventually ((Rue.open_l ..).mem_nhds w)
lemma lyreH(w:U∈O'):∀ᶠ y:dN in 𝓝 0,gyrate (unrest V_ P0.B) U (Prism.trunk P0 o y)∈O':=by
 let f:=gyrate (unrest V_ P0.B) U; have h:=((stickU (unrest V_ P0.B) U).comp (Prism.trunk P0 o).continuous).tendsto 0; simp only [Function.comp_apply,map_zero,Forge.born] at h; exact h.eventually ((Rue.open_l ..).mem_nhds w)
include tH
set_option maxHeartbeats 600000 in
lemma germA (p:P0.threshold=temp x)(w:U∈Rue.litres P0.threshold X V_) (h:∀ P W:Pane N,P∈Rue.litres P0.threshold X V_→W∈Rue.litres P0.threshold X V_→Agrees X P W→f P=f W): (f ∘ (Vmove x U ∘ T')) ∘ ((C₀ • ContinuousLinearMap.id ℝ dN): dN→L[ℝ]dN)=ᶠ[𝓝 0] (f ∘ gyrate (unrest V_ P0.B) U) ∘ Prism.trunk P0 o :=by -- precedence
 let V(i):= Vmove x U (λd i); let Y(i):= gyrate (unrest V_ P0.B) U (Prism.trunk P0 o i)
 filter_upwards [turfH P0 X V_ w λd x, lyreH P0 o X V_ w] with y v t
 change f (Vmove x U (T' (C₀ • y)))=f (Y y); rw [map_smul,shore P0 o X V_ K_ tH y]; exact (h _ _ t v (stoveV P0 o X V_ p y)).symm
lemma sock (p:P0.threshold=temp x)(w:U∈Rue.litres P0.threshold X V_) (h:∀ P W:Pane N,P∈Rue.litres P0.threshold X V_→W∈Rue.litres P0.threshold X V_→Agrees X P W→f P=f W)(t:Pence P0.order (fun y:dN=> f (Vmove x U (T' y))) 0 A) : Signs P0 o (f ∘ gyrate (unrest V_ P0.B) U) (composeCost P0.order ((P0.order.factorial:ℝ)*A) C₀):=by
 let G(y:dN):= f (Vmove x U (T' y)); apply Prism.skills; let M: dN→L[ℝ]dN:= C₀ • (ContinuousLinearMap.id ℝ dN); have hz: M 0=0:=M.map_zero
 have hx: ‖M‖≤ C₀:=by unfold M; rw [norm_smul,Real.norm_of_nonneg (zero_le_one.trans (rootA P0 o X K_ tH))]; apply mul_le_of_le_one_right (zero_le_one.trans (rootA P0 o X K_ tH)); exact ContinuousLinearMap.norm_id_le ..
 have he:= (show Allows P0.order G (M 0) (P0.order.factorial*A) from hz.symm ▸ t.pay).comp (allows_linear hx (by rw [M.map_zero, norm_zero]; exact zero_le_one.trans (rootA P0 o X K_ tH))); exact he.germ (germA P0 o X V_ K_ tH f p w h)
end YM.CF.Nor
