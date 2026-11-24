import GaugeFieldConstruction.Zine
import YM.CF.Moto.Road
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
structure KnotK (A:Pane n→Pal): Prop where
 motion(V:Pane n)(g:Skye.Seat n→SU.E): A (Lattice.gauge g V) = KinX (g o)* A V* star (KinX (g o))
 binned(V):baseF false*A V*baseF true=A V
lemma KinId : KinX 1=1:=by unfold KinX; rw [map_one]; exact Matrix.one_kronecker_one
lemma Kin_mul (i j: SU.E): KinX (i*j)=KinX i*KinX j:=by unfold KinX; rw [map_mul,op_kron_mul, mul_one]; rfl
lemma Kin_inv(i:SU.E): KinX i⁻¹=star (KinX i):=by unfold KinX; rw [op_star_kron,map_inv,star_one]; rfl
lemma Kin_R (i:SU.E): star (KinX i)*KinX i=1:=by rw [←Kin_inv,←Kin_mul,inv_mul_cancel,KinId]
lemma Kin_S (i:SU.E): KinX i * star (KinX i)=1:=by rw [←Kin_inv,←Kin_mul,mul_inv_cancel,KinId]
lemma Knot_c (A:Pal)(u:SheetQ A) : KnotK o (fun _=>A):=by refine ⟨fun V g=> ?_,fun _=>u.bin⟩; rw [← (u.tax _).eq,mul_assoc,Kin_S,mul_one]
variable (k:lotV)
abbrev shoreX (k:lotV):Cover := (knots k).1
abbrev shoreY (k:lotV):Cover := (knots k).2
variable {k}
abbrev landX (o:Skye.Seat n)(k:lotV): Site n:= parked o (shoreX k)
abbrev landY (o:Skye.Seat n)(k:lotV): Site n:= parked o (shoreY k)
variable (k)
def carryU (V:Pane n)(A:Pal):Pal := star (LedgeK (shoreX k) o V)* A * LedgeK (shoreY k) o V
abbrev keyFare (h:ℝ):ℂ:=saleCoeff o (landX o k) (landY o k) h
abbrev beamer(A:Pane n→Pal)(h:ℝ)(V:Pane n): Op (Single n):= modelK o (landX o k) (landY o k) h (carryU o k V (A V))
def viewW (A:Pane n→Pal)(h:ℝ): InkD n:= pulseH ∘ beamer o k A h
lemma ledger_nil(A:Pal): carryU o k 1 A=A:=by unfold carryU LedgeK; simp only [comp_apply,TarOne,KinId,star_one,mul_one,one_mul]
-- orientation g prescription
lemma nana (A:Pane n→Pal)(z: KnotK o A)(V:Pane n)(g:Skye.Seat n→SU.E) : carryU o k (Lattice.gauge g V) (A (Lattice.gauge g V))= KinX (g (node (landX o k)))* carryU o k V (A V)*star (KinX (g (node (landY o k)))):=by
 let R:= KinX (g o); let X:=KinX (g (node (landX o k))); let Y:=KinX (g (node (landY o k))); let B:=A V; let H:=LedgeK (shoreX k) o V; let K:= LedgeK (shoreY k) o V
 unfold carryU; simp only [LedgeK,comp_apply,tare, z.motion, Kin_mul, Kin_inv, star_mul, star_star]; change X*(star H*star R)*(R*B*star R)*(R*K*star Y)= X*(star H*B*K)*star Y; have ht:star R*R=1:= Kin_R _
 simp only [mul_assoc]; -- slightly grouped use chunk cancels
 simp_rw [←mul_assoc (star R) R,ht,one_mul] -- tune
lemma eta_q (A:Pane n→Pal)(q: KnotK o A)(V:Pane n)(h:ℝ):let F:= keyFare o k h • carryU o k V (A V)
 baseF false* F*baseF true=F:=by
 intro F; let X:= carryU o k V (A V); have he:baseF false * X *baseF true=X:=by
    let x:=(TarA o (shoreX k) V)⁻¹; let y:=TarA o (shoreY k) V; let B:=KinX x; let H:= KinX y; have he: X=B*A V* H:=by unfold B H X carryU LedgeK x y; rw [Kin_inv]; rfl
    let P:=baseF false; let Z:= baseF true; have hx:P* A V * Z=A V:= q.binned _; have hy:P* B=B*P:=(stake_M x false).eq; have hz:H*Z= Z*H:= (stake_M y true).eq.symm; rw [he]; change P*(B*A V*H)*Z= _
    rw [mul_assoc P _ Z, mul_assoc _ H Z,hz, ←mul_assoc (B*_ ) Z H,←mul_assoc P _ H, ←mul_assoc P _ Z,←mul_assoc P B, hy,mul_assoc B P,mul_assoc B, hx]
 unfold F; simp only [Matrix.mul_smul,Matrix.smul_mul]; rw [show _= X from he]
lemma ph_caps(A:Pane n→Pal)(V:Pane n): orbitPH (viewW o k A h V)=beamer o k A h V:=spinW _
lemma ph_nest(A:Pane n→Pal)(h:ℝ):lifeH (viewW o k A h)=0:= funext fun i=> pulse_sc _
lemma beam_flat(A:Pane n→Pal)(h:ℝ):beamer o k A h 1=modelK o (landX o k) (landY o k) h (A 1):=by unfold beamer; rw [ledger_nil]
lemma scale_norm (x:ℝ) : ‖keyFare o k x‖= (x^2)⁻¹:=by unfold keyFare saleCoeff; rw [norm_inv,norm_mul,norm_mul,norm_pow,call_bit,call_bit,mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
private def inxZ : Pal→L[ℝ]Pal:= LinearMap.toContinuousLinearMap ({toFun:=star, map_add':=star_add,map_smul':=fun i j=> by rw [star_smul,star_trivial]; rfl}) -- tune
private def directT:= ContinuousLinearMap.mul ℝ Pal
omit k
private lemma Tax_τ {x:Cover} (v:lateral x ≤4)(u:p.power≤3)(f:p.order≤6): Housing.Haw p o (Pax o) (fun i=> star (LedgeK x o i)) (tautF inxZ* Ledge_Pay.choose):= Housing.svelte (Ledge_Pay.choose_spec.2 n o x p v f u) inxZ
private def FeeV {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](F:E→L[ℝ] E→L[ℝ] E):ℝ:= ‖F‖
private abbrev legY:= (2:ℝ)^6*FeeV directT
private lemma tax_Q {A B:Pane n→Pal}(q:ℝ)(h:Housing.Haw p o (Pax o) A c)(v:Housing.Haw p o (Pax o) B q) (k:p.order ≤6): Housing.Haw p o (Pax o) (fun U=> A U *B U) (legY * c * q):=by
 let L:=directT; have hf:0≤c:=(h.rends 1 (ping_f p _)).grade; have hx:0≤ q:=(v.rends 1 (ping_f p _)).grade; exact Housing.gum (Housing.witch L h v) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) k) (show 0≤ FeeV directT from (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](F:E→L[ℝ] E→L[ℝ] E),0 ≤ FeeV F from fun {_} _ _ F=> norm_nonneg F) directT)) hf) hx)
abbrev palCost:= legY * legY * (tautF inxZ * Ledge_Pay.choose)* Ledge_Pay.choose
def pawnC(x:ℂ) : Pal→L[ℝ] Pal:= x • ContinuousLinearMap.id ℝ Pal
lemma StampC (x:ℂ): tautF (pawnC x) ≤ ‖x‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro i; exact (norm_smul x (β:=Pal) i).le -- tune binder
include k
lemma Köp {A: Pane n→Pal}(p₀:p.power ≤3)(t:p.order ≤6)(u:Housing.Haw p o (Pax o) A c): Housing.Haw p o (Pax o) (fun i=> carryU o k i (A i)) (palCost*c):=by
 obtain ⟨g,l⟩:= knot_rad k; let W:= legY*(tautF inxZ* Ledge_Pay.choose)*c
 let X:= Tax_τ (p:=p) o g p₀ t; let P:= tax_Q o c X u t; apply gum (tax_Q o _ P (Ledge_Pay.choose_spec.2 n o _ p l t p₀) t); unfold palCost; exact le_of_eq (by ring)
abbrev coreΔ (A:Pane n→Pal)(h:ℝ)(U: Pane n):= keyFare o k h • carryU o k U (A U)
lemma RegPay {A: Pane n→ Pal}(p₀:p.power ≤3)(t:p.order≤6)(v: Housing.Haw p o (Pax o) A c)(h:ℝ): Housing.Haw p o (Pax o) (coreΔ o k A h) ((h^2)⁻¹*(palCost*c)):=by
 let P:= Köp o k p₀ t v; rw [←scale_norm o k h]; apply Housing.gum (Housing.svelte P (pawnC _)); exact mul_le_mul_of_nonneg_right (StampC _) (P.rends 1 (ping_f p _)).grade -- tune
lemma vistaP (u:20<n.val)(p₀:p.power ≤3)(t:p.order ≤6)(A:Pane n→ Pal) (w:KnotK o A)(v:Housing.Haw p o (Pax o) A c)(r:h≠0): PressB p (Zhub o) (viewW o k A h) h (CargoMax*palCost*c):=by
 obtain ⟨a,e⟩:= knot_rad k; have ht(x:Cover)(v:lateral x ≤4) : node (parked o x)∈ Pax o:= halo_spec.mpr ⟨o,mem_singleton_self _, (spot_gap o x v u).trans (by decide)⟩; let Y:= RegPay o k p₀ t v h
 rw [show CargoMax *palCost*c= CargoMax*h^2*((h^2)⁻¹*(palCost*c)) from (by field_simp)]; apply CargoB _ _ (coreΔ o k A h) _ Y p₀ (ht _ a) (ht _ e); intro V g; unfold coreΔ; rw [nana o k A w V g, Matrix.mul_smul, Matrix.smul_mul]
end Layout
end Lenten
end YM.CF.TableF
end
