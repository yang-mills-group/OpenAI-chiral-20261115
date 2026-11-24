import YM.CF.Gully.Map
import YM.CF.Spire.Thick
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
variable {a v b c d:ℝ}
section
open Spark Scion Scree Skye Tulip
variable {hp:1≤H}{Z:Ewe m B}(Y:Scroll m B (northZ m B))(k:ℝ)(X:Briar m B e)
local notation "M₀"=>northZ m B
variable (g:motor (Ave.travel m B e H hp) (fun w=>exp (chillT Y k w)) X=exp Z)
private lemma hot (x:ℂ)(Y:Ewe m B)(p:Pastry.Poly (Hearth m B) (Elf m B)): p.cook (exp (hollow x+Y))=Complex.exp x • p.cook (exp Y):=by rw [expReal]; letI:NormedAlgebra ℚ (Ewe m B):=NormedAlgebra.restrictScalars ℚ ℝ _; letI : NormedAlgebra ℚ (FC (Elf m B)):=NormedAlgebra.restrictScalars ℚ ℝ _; rw [map_exp p.cook p.cookC]
include g
lemma deltaQ (V:Room B e)(F:FC (Elf m B)) : (∫ z, ratioRF Y e 0 k 1 M₀ (fun _=>F) (X.val,z)∂rains m)=inner ℂ (linearB Λ) (acts F (acts ((zeroOf X M₀ V).cook (exp (hollow ((k:ℂ)*energ m B M₀ X.val)+Z))) (sound m B M₀ X.val))):=by
 let s:= (zeroOf X M₀ V).cook; let U:= linearB Λ; let A:= sound m B M₀ X.val
 let R (p:Ewe m B) := inner ℂ U (acts F (acts (s p) A))
 let J : Ewe m B→L[ℝ] ℂ :=
    { toFun:=R
      map_add' p q:= by unfold R; rw [map_add s,act_add,map_add,inner_add_right]
      map_smul' p q:= by unfold R; change _= p • inner ℂ _ _; rw [map_smul s,actReal,eyeReal]
      cont := continuous_const.inner ((acts F).continuous.comp ((acts_cont.comp (zeroOf X M₀ V).cookC).clm_apply continuous_const)) }
 let W:= energ m B M₀ X.val; let M z:= law m B X.val z • exp (chillT Y k (X,z))
 have he(z:Cue m): ratioRF Y e 0 k 1 M₀ (fun _=>F) (X.val,z)=Complex.exp ((k:ℂ)*W)* J (M z):=by
    have ht: net m B 0 (X.val,z)=law m B X.val z:=by simp [net,massR, RP.top,Wilson.bare]
    by_cases l:law m B X.val z=0
    · unfold M; rw [l,zero_smul,map_zero,mul_zero]; exact Set.indicator_of_notMem (fun v=> (show net m B 0 (X.val,z)≠0 from (show (X.val,z)∈TallyR m B e 0 from v).2) (ht.trans l)) _
    have hK:= law_rich m B X.val z l
    rw [ratioRF,Set.indicator_of_mem (show (X.val,z)∈ TallyR m B e 0 from ⟨X.property,ht.symm ▸ l⟩),amplitudeF,ht]
    change _ * _ * inner ℂ U (acts (F*quant (grow (wiel m B M₀ X.val) k)) (pairWave (Phase.pair m B X.val z)))=_; unfold M; rw [act_mul,produced M₀ V X.property hK k,map_smul,inner_smul_right,map_smul J]
    let f:=Phase.fund m B M₀ X.val z; let K:=cabinQ Y (X.val,z)
    have hp: s (exp (chillT Y k (X,z)))=Complex.exp (f-K) • exp (sheet m B M₀ k X.val z):=by unfold s chillT; rw [expReal]; exact congrArg _ (congrArg NormedSpace.exp (show (zeroOf X M₀ V).cook _=_ from diect m B k (X,z) M₀ V))
    change ↑(law m B X.val z)*Complex.exp (-(↑(1:ℝ):ℂ)*K)*(Complex.exp ((k:ℂ)*W+f)*inner ℂ U (acts F (acts (exp (sheet m B M₀ k X.val z)) A)))=_ * (law m B X.val z • inner ℂ U (acts F (acts (s _) A)))
    rw [hp,act_smul,map_smul,inner_smul_right]; simp only [Complex.real_smul,Complex.ofReal_one,neg_mul,one_mul,smul_eq_mul]
    have ht:Complex.exp (-K)*Complex.exp ((k:ℂ)*W+f)=Complex.exp ((k:ℂ)*W)*Complex.exp (f-K):=by rw [←Complex.exp_add,←Complex.exp_add]; congr 1; ring
    linear_combination ↑(law m B X.val z)*inner ℂ U (acts F (acts (exp (sheet m B M₀ k X.val z)) A))*ht
 have hp:Integrable M (rains m):=by by_contra l; exact rise_ne Z (g.symm.trans (integral_undef l))
 simp_rw [he]; rw [integral_const_mul,hinge (n:=Hearth m B) J hp,show ∫ z,M z∂rains m=exp Z from g,hot,act_smul,map_smul,inner_smul_right]; rfl
variable {j:ℕ}{o:Odd L.val}{T: Pricing j L o (Thread j)}(P:Grasp T B e)(h:P.roundZ ≤ (CSide m B).val)
def CordQ(P:Grasp T B e)(k:ℝ)(X:Briar m B e)(Z:Ewe m B):Ewe m B:= Pastry.hollow (candle m B (P.cost m firstM) X.val)+ (k • hollow (energ m B M₀ X.val)+Z)
def setD (P:Grasp T B e) (x:Briar m B e)(K:Cipher Λ):= acts (tank (spar j firstM x.val) (exp K)) (changeM P x.val firstM)
include h
lemma chord_D(F:FC (Single Λ)): (∫ z, ratioRF Y e 0 k 1 M₀ (fun _=>Spark.crossL (helix _).symm F) (X.val,z)∂rains m)=inner ℂ (mateK Λ) (acts F (setD P X (Marsh m B (CordQ P k X Z)))):=by
 let U:= X.val; let M:= Marsh m B; let Y':= CordQ P k X Z; let W:= spar j firstM U; let A:= P.couture h firstM; have he:=frame_init P.topB P.baseY A X.property; have hv:IsStarProjection W:= frame_first P.topB P.baseY A X.property
 rw [deltaQ Y k X g P.baseY, cCash]; apply congrArg (fun x=>inner ℂ (mateK Λ) (acts F x)); unfold setD changeM
 change _ = acts (tank W (exp (M Y'))) (Complex.exp (-candle _ _ _ U) • _); rw [fundus P.topB P.baseY A U X.property,tank_eq W _ hv,map_smul]; letI : NormedAlgebra ℚ (Ewe m B):=NormedAlgebra.restrictScalars ℚ ℝ _; letI : NormedAlgebra ℚ (Cipher Λ):=NormedAlgebra.restrictScalars ℚ ℝ _; rw [←map_exp M M.toLinearMap.continuous_of_finiteDimensional];
 rw [← cubic_C (helix _) hv (lensP M₀ P.baseY X.property) he]; unfold Y' CordQ;  unfold U; rw [hot (m:=m) (B:=B) (candle m B (P.cost m firstM) X.val),act_smul,carts_s,smul_smul,Complex.exp_neg,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_smul]
 have ht(y:ℂ):k • hollow (n:=Hearth m B) y=hollow ((k:ℂ)*y):=Subtype.ext (by change k • (y • (1:FC _))= _; rw [←smul_assoc]; rfl) -- tune
 rw [ht]; rfl
end
end YM.CF.Gully
