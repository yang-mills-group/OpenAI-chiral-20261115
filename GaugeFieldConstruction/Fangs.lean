import GaugeFieldConstruction.Jubila
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
-- Waves API packaged (complex).
private lemma smul_f {E:Type}(P:TPack E)(q:ℂ):letI:=P.G; letI:=P.S; q • (0:E)=0:=by letI:=P.G; letI:=P.S; exact smul_zero ..
abbrev ΓProj (r:ℕ) : Waves→ₗ[ℂ] Waves where
 toFun:=MSlot r
 map_add':=MSlot_k
 map_smul':= fun a z=>by
    dsimp only [MSlot]; split_ifs <;> apply Prod.ext <;> first| rfl | apply Prod.ext <;> first| rfl| exact (smul_f (CartPack PackG PackP) _).symm| exact (smul_f (CartPack PackH (CartPack PackM PackS)) _).symm
set_option maxHeartbeats 150000 in
lemma MGate {i j:ℕ}(p:i≤j)(x:Waves):ΓProj j (ΓProj i x)=ΓProj i x:=by change MSlot j (MSlot i x)=MSlot i x; unfold MSlot; split_ifs <;> first|rfl|omega
private abbrev T4 :TPack J4:= CartPack PackG PackP
private abbrev T5 :TPack J5:= CartPack PackH (CartPack PackM PackS)
-- To express Crown simplifies using small scalar. norms choose from pack via helper.
private lemma smul_a {E:Type}(P:TPack E)(q:ℂ):letI:=P.G; letI:=P.S;∀ u v:E,q • (u+v)=q • u+q • v:=by letI:=P.G; letI:=P.S; intro u v; exact smul_add ..
private lemma smul_b {E:Type}(P:TPack E)(q p:ℂ):letI:=P.G; letI:=P.S;∀ u:E,q • p • u= p • q • u:=by letI:=P.G; letI:=P.S; intro u; exact smul_comm ..
private lemma smul_c {E:Type}(P:TPack E)(q r p t:ℂ)(e:r=t*p/q) (h:q≠0):letI:=P.G; letI:=P.S;∀ u:E, r • u=t • p • q⁻¹ • u:=by letI:=P.G; letI:=P.S; intro u; simp [smul_smul,e,div_eq_mul_inv,mul_assoc]

private lemma smul_n {E:Type}(P:TPack E)(q:ℝ):letI:=P.G; letI:=P.S;∀ x:E, ‖(q:ℂ) • x‖= |q| * ‖x‖:=by letI:=P.G; letI:=P.S; intro x; exact (norm_smul ..).trans (congrArg (·*‖x‖) (Complex.norm_real _)) -- tune
abbrev PrintQ (x r:ℝ):Waves→ₗ[ℂ] Waves where
 toFun:= Crown x (x*r^2) (x*r^2) (x*r)
 map_add':= fun u v=> Prod.ext (smul_a PackL ..) (Prod.ext (Prod.ext (smul_a PackG ..) (smul_a PackP ..)) (Prod.ext (smul_a PackH ..) (Prod.ext (smul_a PackM ..) (smul_a PackS ..)))) -- dots infer
 map_smul':=fun u v=> Prod.ext (smul_b PackL ..) (Prod.ext (Prod.ext (smul_b PackG ..) (smul_b PackP ..)) (Prod.ext (smul_b PackH ..) (Prod.ext (smul_b PackM ..) (smul_b PackS ..))))
lemma PrintsQ (s z:ℝ)(i:ℕ)(x:Waves): PrintQ s z (ΓProj i x)=ΓProj i (PrintQ s z x):=by
 change Crown _ _ _ _ (MSlot _ _)= MSlot _ (Crown _ _ _ _ _); unfold MSlot; split_ifs <;> apply Prod.ext <;> first| rfl| apply Prod.ext <;> first|rfl|exact Prod.ext (smul_f PackG _) (smul_f PackP _) | exact Prod.ext (smul_f PackH _) (Prod.ext (smul_f PackM _) (smul_f PackS _)) -- tune
lemma loan_κ {E:Type}(P:TPack E)(s:ℝ)(p:1 / 8 ≤ s):letI:=P.G; letI:=P.S;∀ x:E,‖x‖≤ (8:ℝ)*‖(s:ℂ) • x‖:=by
 letI:=P.G; letI:=P.S; intro i; rw [smul_n P,abs_of_nonneg (by linarith only [p]:0 ≤ s), ←mul_assoc]; exact le_mul_of_one_le_left (norm_nonneg _) (by linarith only [p])
-- use norm max.Cycle.S. Ratio both ≥1/2.
lemma ValleyQ {s z:ℝ}(p:1 / 2 ≤ s)(v:1 / 2 ≤ z)(U:Waves):‖U‖ ≤ 8*‖PrintQ s z U‖:=by
 have hv : (1:ℝ)/8 ≤ s*z^2:=by nlinarith only [mul_le_mul_of_nonneg_right p (sq_nonneg z), sq_nonneg (z-1/2),v]
 let T:=PrintQ s z U
 apply max_le ((loan_κ PackL s (by linarith) U.1).trans (mul_le_mul_of_nonneg_left (le_max_left ..) (by norm_num: (0:ℝ)≤8)))
 have he:= show ‖T.2‖ ≤ ‖T‖ from le_max_right ..
 have hx:= show ‖T.2.1‖ ≤ ‖T‖ from (le_max_left ..).trans he; have hg:= show ‖T.2.2‖ ≤ ‖T‖ from (le_max_right ..).trans he
 have hk:= show ‖T.2.2.2‖ ≤ ‖T‖ from (le_max_right ..).trans hg
 refine max_le (max_le ?_ ?_) (max_le ?_ (max_le ?_ ?_))
 · exact (loan_κ PackG _ hv _).trans (mul_le_mul_of_nonneg_left ((le_max_left ..).trans hx) (by norm_num))
 · exact (loan_κ PackP s (by linarith) _).trans (mul_le_mul_of_nonneg_left ((le_max_right ..).trans hx) (by norm_num))
 · exact (loan_κ PackH _ hv _).trans (mul_le_mul_of_nonneg_left ((le_max_left ..).trans hg) (by norm_num))
 · exact (loan_κ PackM s (by linarith) _).trans (mul_le_mul_of_nonneg_left ((le_max_left ..).trans hk) (by norm_num))
 have ho:1/8 ≤ s*z:=by nlinarith only [mul_le_mul_of_nonneg_right p (le_trans (by norm_num : 0 ≤ (1:ℝ)/2) v),v]
 exact (loan_κ PackS _ ho _).trans (mul_le_mul_of_nonneg_left ((le_max_right ..).trans hk) (by norm_num))
lemma Price_eclipse (s z:ℝ){t:ℝ}(p:1 / 2 ≤ s)(v:1 / 2 ≤ z)(h:8 ≤ t): EclipseS ΓProj (PrintQ s z) t := ⟨fun x=> (ValleyQ p v _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)),PrintsQ _ _,fun _ _=>MSlot_m ..,fun h x=> MStore x h⟩
end
end YM.CF.Oath
end
