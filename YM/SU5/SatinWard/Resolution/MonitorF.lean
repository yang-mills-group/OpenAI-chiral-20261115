import YM.CF.Vp929.Canon.Cedar
import YM.SU5.SatinWard.Resolution.Orph
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
/-! # The Real criterion sees a flavor rotation. Not silently postulating it through the noncanonical projector -/
namespace SpinMeter
open CF.Mezzo
section Tune
abbrev χδ (s:Signed)(b:Bool)(i:Axis): Bool:= b.xor (s.flip i)
-- boundary of normalized momentum cube
abbrev boxing (s:Signed)(b:Bool): Equiv.Perm (Axis→Bool) :=
 let χ:=χδ s b ; {
 toFun η i:=(χ (s.perm.symm i)).xor (η (s.perm.symm i))
 invFun φ i:= (χ i).xor (φ (s.perm i))
 left_inv η:= funext fun i=>by simp
 right_inv η:= funext fun i=>by simp }
lemma cadenceSong(s:Signed)(b:Bool)(η:Axis→Bool): cadence s b (song q η)=song q (boxing s b η):=by
 funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; cases b<;>cases h:s.flip i <;>cases u:η i <;> simp [song,boxing, cadence,χδ,h,u,signs]
local notation "B✲"=> Ember.bins SU.Slot
abbrev tempo (q:ℝ)(W:Momentum→Pal)(i:Axis):Pal:= (16*q)⁻¹ • ∑ η:Axis→Bool, signs (η i) • W (song q η)
lemma tempo_eq (W:Momentum→Pal) : tempo q W 0=sovX q W:=rfl
variable (s:Signed)(b₀:Bool)(U:UNI SpinIdx) (u:JetS s b₀ (detX s) U)
local notation "b"=> b₀
local notation "r"=> detX s
local notation "ℤU"=> twoU U b
local notation "H"=> sings b ℤU
local notation "T"=> Thera.jazz r
variable (e:Frequency L n q){W:Momentum→Pal}(h:AxisP W)
include e h
include u
lemma turnTempo (i:Axis): H (tempo q W (s.perm i))= T (hush (χδ s b i) (tempo q W i)):=by
 unfold tempo
 conv_lhs=> rw [←Equiv.sum_comp (boxing s b)]
 simp only [singT,Scroll.win_r,win_sum,map_sum,map_smul]
 -- use signed price for each argument
 simp_rw [←singT b ℤU, ←cadenceSong,h.rise s b U u _ (sung e _), boxing, Equiv.coe_fn_mk, Equiv.symm_apply_apply] -- tune lemma
 have hc(x:Bool): signs (!x)= -signs x:=by cases x <;> simp [signs]
 cases hz:χδ s b i <;> cases ht:r <;> simp [Thera.jazz,hc,sum_neg_distrib]

omit h e
lemma vanish_f (A X:Pal)(v:H A=T X): H (Mezzo.vanish A)=T (Mezzo.vanish X):=by
 unfold Mezzo.vanish; rw [singm,singm,v]
 have ht (k:Bool): sings b ℤU ((angle k) ⊗ₖ (1:Op SU.Slot))=angle (Bool.xor r k) ⊗ₖ (1:Op SU.Slot) :=by rw [Scroll.wingK,angleX u,singT b _ _,win_i,map_one] -- check
 have hu:B✲=angle true ⊗ₖ (1:Op SU.Slot):=rfl
 have hB:sings b ℤU B✲= if r then 1-B✲ else B✲ :=by rw [hu,ht]; cases r; rfl; change (1-Aop) ⊗ₖ (1:Op SU.Slot)=1-_; rw [sub_eq_add_neg,Matrix.add_kronecker,Matrix.one_kronecker_one, op_kron_neg, ←sub_eq_add_neg]; rfl
 rw [show H (1-B✲)=1-H B✲ from by rw [singT,win_l,win_i,map_sub,map_one,singT],hB]
 cases hx:r; rfl
 change (1-B✲)*(-star X)*(1-(1-B✲))= -star (B✲*X*(1-B✲)); have he: star B✲=B✲:=Ember.binsAdj _ 
 rw [star_mul,star_mul,star_sub,he,star_one]; simp [mul_assoc]
include e h
lemma turnCourse (i:Axis): H (Mezzo.vanish (tempo q W (s.perm i)))= T (hush (χδ s b i) (Mezzo.vanish (tempo q W i))):=by
 rw [vanish_f s b U u _ _ (turnTempo s b U u e h i)]
 apply congrArg; cases χδ s b i <;> simp [Mezzo.vanish]
omit u
private lemma command (i:Axis)(x:SU.E): Commute (Mezzo.vanish (tempo q W i)) ((1:Op SpinIdx)⊗ₖ (matter x).val):=by
 have hu: Commute B✲ (KinX x):=by unfold Commute SemiconjBy KinX; change (_⊗ₖ (1: Op SU.Slot))*_=_*(_⊗ₖ (1: Op SU.Slot)); rw [op_kron_mul,op_kron_mul,one_mul,one_mul,mul_one,mul_one]
 apply Commute.mul_left (hu.mul_left ?_) ((Commute.one_left _).sub_left hu)
 refine Commute.smul_left (Commute.sum_left _ _ _ (fun η _=> Commute.smul_left (h.hold x _ (sung e η)) _)) _ -- tune
lemma stays_Mind: Mind (spaX (sovX q W) 0):=by
 have ht:=color_all (fun i=> Mezzo.vanish (tempo q W i)) (fun i=> vBinned _) (fun _ _ _ h' i=> turnCourse _ _ _ h' e h i) (command e h)
 have he:=ht.1; rw [spa_vanish,tempo_eq] at he; exact he
end Tune
-- The plane-wave **payment** on the actual discrete ring, not an overflight in the
-- continuous tangent of a different configuration.
open Cycle929
variable (e:Frequency L n q)(x:Axis→Bool)(g:UNI SU.Slot){X Y:Op (Single n)}
local notation "u✥"=> song q x
local notation "S"=> spar j M (1:Pane n)
local notation "U" => singlet n g
local notation "P"=> Mezzo.pal g
include e
lemma paid_ear (h: twist (singlet n g) ((1-S)*X*S)=(1-S)*Y*S)(u: Scoria j M X v)(w:Scoria j M Y a): twist P (potion j M (WW X) u✥)=potion j M (WW Y) u✥:=by
 obtain ⟨hX,_,t⟩:= u.earm; obtain ⟨hY,_,d⟩:= w.earm
 let A:= Tap.Tern j M (loft X); let B:= Tap.Tern j M (loft Y)
 let C:=duet n g; let f(y:E2→ℂ): Site n × E2→ℂ:=fun z=> mode u✥ (Rush.natural z.1)*y z.2
 have hφ (W:UNI (SpinIdx×SU.Slot))(y:E2→ℂ)(k:Site n):((1:Op (Site n)) ⊗ₖ W.val) *ᵥ f y=f (W.val *ᵥ y):=by
    funext ⟨y₀,i⟩; unfold f; rw [←jump_replicate]; simp only [Matrix.mulVec, dotProduct,Fintype.sum_prod_type,jump_apply,Equiv.refl_apply,ite_mul,zero_mul,sum_ite_irrel,sum_const_zero]; rw [sum_ite_eq _,if_pos (mem_univ _)]; rw [Finset.mul_sum]; apply sum_congr rfl; intro b _; simp only [Finset.mul_sum]; simp only [mul_comm,mul_left_comm,mul_assoc]
 have he: C.val*cart n A= cart n B*C.val:=by
    rw [hX,hY,twist_formula,← love_coat n g, ← map_star (love n), ← map_mul, ← map_mul] at h
    have ht: C.val * cart n A * star C.val=cart n B:=(love n).injective h
    rw [←ht,mul_assoc _ _ C.val,show star C.val*C.val=1 from C.property.1,mul_one]
 apply Mir.twist_comm
 ext i j'
 let y:=fun k:E2=>(1:Pal) k j'; let z:Site n:=0
 let R:= potion j M (WW X) u✥; let D:=potion j M (WW Y) u✥
 have hA(y:E2→ℂ):cart n A *ᵥ f y=f (R *ᵥ y):=funext fun i=>Rush.earns t (sung e _) (sung_fee e _) y i.1 i.2
 have hB(y:E2→ℂ):cart n B *ᵥ f y=f (D *ᵥ y):=funext fun i=>Rush.earns d (sung e _) (sung_fee e _) y i.1 i.2
 have hC(y:E2→ℂ): C.val *ᵥ f y=f ((P).val *ᵥ y):=hφ P y z
 have hx:=congrArg (fun v=>v *ᵥ f y) he
 rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hA, hC,hC,hB,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec] at hx
 have hl:= mul_left_cancel₀ (show mode u✥ (Rush.natural z) ≠ 0 from Complex.exp_ne_zero _) (show mode u✥ (Rush.natural z)* _ =_ from congr_fun hx (z,i))
 simpa only [y,Matrix.mulVec,dotProduct,Matrix.one_apply,mul_ite,mul_one,mul_zero,Fintype.sum_ite_eq',Fintype.sum_ite_eq] using hl
lemma price_represent {F' : RegBudget n}{P₀:BudgetPoint} (hPQ:IncX Utrue F P₀ a b)(pA:1≤a)(u':P₀.power=2)(w:1≤j)(hZ:IncX Utrue F' P₀ a t)
 (hv: twist U ((1-S)*(StackL F univ)*S)=(1-S)*(StackL F' univ)*S):
 twist g (waveTest q F j M).val= (waveTest q F' j M).val:=by
 have h':=gem (live_full n) hPQ pA u' w M 0 fun _ _=>Nat.zero_le _; have h:=gem (live_full n) hZ pA u' w M 0 fun _ _=> Nat.zero_le _
 let H:=sovX q (potion j M (WW (StackL F univ))); let K':=sovX q (potion j M (WW (StackL F' univ)))
 change twist g (pickM H).val=(pickM K').val; rw [pickM_left (stays_Mind e (Psy j w M h'.axisP)),pickM_left (stays_Mind e (Psy j w M h.axisP))]
 have he: twist P H=K':=by unfold H K' sovX; rw [map_smul,map_sum]; simp_rw [map_smul,paid_ear e _ g hv h' h]
 change twist g (spaX H 0) = spaX K' 0
 rw [←he,turn_spa]

end SpinMeter
end TestW
end Test
end YM.CF.Py.Rate
