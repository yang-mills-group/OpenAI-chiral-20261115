import YM.CF.DPress.Rank.Tung
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open Cad Mercer
namespace Qzeta
variable {d a b c t:ℝ}{N:Side}(T S:BeatL N) -- explicit for inference
abbrev LM (N:Side):= Cad.Θ→ₗ[ℝ] Op (Single N)
abbrev MulZ(P R:Op (Single N))(A:LM N): LM N:={ toFun:= fun Q=>P * A Q * R, map_add':=fun X Y=>by rw [map_add,mul_add,add_mul], map_smul':=fun x y=>by rw [map_smul,Matrix.mul_smul,Matrix.smul_mul]; rfl }
abbrev Before(P:Op (Single N))(A:LM N): LM N:={ toFun:= fun Q=>P * A Q, map_add':=fun X Y=>by rw [map_add,mul_add], map_smul':=fun x y=>by rw [map_smul,Matrix.mul_smul]; rfl }
abbrev After (A:LM N)(P:Op (Single N)): LM N:={ toFun:= fun Q=>A Q * P, map_add':=fun X Y=>by rw [map_add,add_mul], map_smul':=fun x y=>by rw [map_smul,Matrix.smul_mul]; rfl }
lemma plank_plus(Q F: Op SU.Slot): plankP N (Q+F) = plankP N Q+plankP N F:=by simp_rw [plankP,headW,jump_replicate, Matrix.kronecker_add,map_add]
lemma plank_sm(Q:Op SU.Slot)(z:ℂ): plankP N (z • Q)= z • plankP N Q:=by simp_rw [plankP,headW,jump_replicate, Matrix.kronecker_smul,map_smul]
abbrev PushD(N:Side):LM N:= {
 toFun:= fun Q=> -plankP N Q.val
 map_add' :=fun X Y=>by rw [Submodule.coe_add,plank_plus,neg_add]
 map_smul' :=fun (c:ℝ) y=> by rw [Submodule.coe_smul_of_tower]; change -plankP N (c • _)= c • _; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) c,RCLike.real_smul_eq_coe_smul (K:=ℂ) c,plank_sm,smul_neg] }
-- Rise is complex 2 scalar commutes
abbrev film (U:Chin N):LM N:= MulZ (1-S U) (1+S U) (PushD N)
abbrev Rise (P:Op (Single N)) (F:LM N): LM N:={ toFun:=fun U=> Sault.rise P (F U), map_add':= fun i j=> by unfold Sault.rise; rw [map_add,mul_add,add_mul,←smul_add]; exact congrArg _ (by abel), map_smul':= fun r i=> by change ((2:ℂ)⁻¹ • (P*F (r • i)+F (r • i)*P-F (r • i)))=r • _; rw [map_smul, Matrix.mul_smul,Matrix.smul_mul, ←smul_add,←smul_sub, smul_comm (2:ℂ)⁻¹ r] }
abbrev τX (i:Bool)(U:Chin N):LM N:= if i then After (film S U) (1-T U) else Before (T U) (film S U)
variable {S T}(t) (A: BondL T S (body_Q 1) b c a d)(g:0≤t)
def Loans : BondL T S (body_Q t) (priceN t b) (priceN t c) a d:=⟨rentT t A.ela g,rentT t A.elt g,rentT t A.coreS g,fun i=>rentT t (A.cosY i) g,rentT t A.heel g, rises t _ g (fun _=>PushD N) A.Yh,rises t _ g (fun i=>film S i-PushD N) A.Th,rises t _ g (fun i=> Rise (T i) (film S i)-Rise (tickA N) (PushD N)) A.Ch,fun i=>by cases i; exact rises t _ g (τX T S false) (A.Hh false); exact rises t _ g (τX T S true) (A.Hh true), rises t _ g (fun i=> MulZ (T i) (1-T i) (film S i)) A.Hc,fun s=> ⟨leafJ_s t _ g _ s _ (A.sQ s).1,leafJ_s t _ g _ s _ (A.sQ s).2.1,leafJ_s t _ g _ s _ (A.sQ s).2.2.1,leafJ_s t _ g _ s _ (A.sQ s).2.2.2.1, fun i=>leafJ_s t _ g _ s _ ((A.sQ s).2.2.2.2 i)⟩⟩
include g
lemma faithful (z:pureB A 1): pureB (Loans t A g) (Cad.rent*t):=by
 refine ⟨((z.1.funds (mul_nonneg Cad.pos.le g))).book (le_of_eq (by ring)),?_⟩
 intro v y; funext i j; change Cad.rent*t*A.ela.W v i j=0; rw [z.2 _ y]; exact mul_zero _
end Qzeta
end YM.CF.Sour.Heath
