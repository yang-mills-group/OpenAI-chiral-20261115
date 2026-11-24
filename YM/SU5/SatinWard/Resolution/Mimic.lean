import YM.SU5.SatinWard.Resolution.Bokeh
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU


namespace SignSlot
open Buffered Swell Porticus Hest Nacre StressExchange Merino.Brooch
local notation "K0"=> Op SU.Slot
variable {p:BudgetPoint}

open Sour
lemma block_γ (s:Sweep n)(P:Op (Single n))(x y:Site n): let A:=castX s; matPH (sings s.charge (γS s) P) x y=(A.payA x*A.payA y) • sings s.charge (twoU (spinU s.charge s.s) s.charge) (matPH P (mPath s x) (mPath s y)) := by
 obtain ⟨Y,rfl⟩:=(love n).surjective P; intro a
 unfold matPH Haro.rentH; change Scroll.tap ((love n).symm (sings s.charge (prepU ..) ((love n) Y))) _ _= _
 rw [wingX,StarAlgEquiv.symm_apply_apply,show (love n).symm ((love n).toRingEquiv Y)=Y from (love n).symm_apply_apply Y,tap_sg]
 let K:=Scroll.tap Y (mPath s x) (mPath s y); let r:=s.charge; let V:=twoU (spinU r s.s) r
 change (a.payA x • V.val)*windX r K*star (a.payA y • V.val)= (a.payA x*a.payA y) • sings r V K -- tune
 rw [Matrix.smul_mul,star_smul,a.real_payA,Matrix.smul_mul,Matrix.mul_smul,singT,twist_formula,mul_smul]
lemma block_toe (s:Sweep n){x y:Site n}(h:Earlier s x y)(V:Pal): sings s.charge (γS s) (bud_k x x x V)= bud_k y y y (sings s.charge (twoU (spinU s.charge s.s) s.charge) V):=by
 rw [latticeFieldEstimates,latticeFieldEstimates]
 ext ⟨⟨p,j⟩,k⟩ ⟨⟨q,l⟩,w⟩
 change matPH (sings s.charge (γS s) (seed_k x x V)) p q (j,k) (l,w)=matPH (seed_k y y (sings _ (twoU (spinU s.charge s.s) s.charge) V)) p q (j,k) (l,w)
 rw [block_γ]; simp_rw [Moto.star_P]; have he:mPath s y=x:= (earlier_mills ..).mp h
 by_cases p':p=y; swap; · rw [if_neg (fun u=>p' ((mPath s).injective (u.1.symm.trans he.symm))), if_neg (mt And.left (Ne.symm p'))]; rw [singT,win_z,map_zero,smul_zero]
 by_cases q':q=y; swap; · rw [if_neg (fun u=>q' ((mPath s).injective (u.2.symm.trans he.symm))), if_neg (mt And.right (Ne.symm q'))]; rw [singT,win_z,map_zero,smul_zero]
 rw [p',q',if_pos (And.intro he.symm he.symm),if_pos (And.intro rfl rfl), show (castX s).payA y* (castX s).payA y=1 from fee_one _,one_smul]
lemma block_hush (s:Sweep n){x y:Site n}(h:Earlier s x y)(V:Pal): jazz (detX s.s) (sings s.charge (γS s) (bud_k x x x V)) = bud_k y y y (castPal s.charge (detX s.s) (spinU s.charge s.s) V):=by
 rw [block_toe s h]; cases detX s.s
 · rfl
 change -star _=bud_k y y y (-star _); rw [bud_neg,bud_star]
lemma dyad_trace (V:Op (Single n))(z:ℝ): (z • V).trace=(z • V.trace):=Matrix.trace_smul ..
lemma spot_line (s:Sweep n){x y:Site n}(h:Earlier s x y)(A B:K0)(z:ℝ)(i j:Axis)
 (u:castPal s.charge (detX s.s) (spinU s.charge s.s) (petal i⊗ₖ A)= z • (petal j⊗ₖ B)):
   flyMark s (onsiteSensor x (petal i⊗ₖ A))= z • onsiteSensor y (petal j⊗ₖ B):=by
 funext V
 unfold flyMark; rw [spin_current] -- remove nomZ
 let X:= bud_k x x x (petal i⊗ₖ A); let Y:= bud_k y y y (petal j⊗ₖ B)
 let U:=γS s; let b:=s.charge; let t:=detX s.s; change Spire.tourP U b t (dg X)= z • onsiteSensor _ _ V
 rw [spin_current,Merino.Brooch.dd]; have he:jazz t (sings b U X)= z • Y:= (block_hush s h _).trans (u ▸ bud_scale ..) -- orientation
 split; next r=>
    have hh: - form b true U X=z • Y:=by rw [r] at he; exact he
    rw [r, neg_eq_iff_eq_neg.mp hh]; -- tune sign
    rw [Matrix.trace_neg,Matrix.trace_smul,spin_small,smul_zero,neg_zero,dg_neg,dg_scale,zero_smul]; abel
 next r=>
    change ¬t=true at r; replace r:= Bool.eq_false_iff.mpr r
    rw [r, show form b false U X=z • Y from by rw [r] at he; exact he]; exact dg_scale ..
open Lampshade
lemma Jattired (A: K0)(p:star A=A)(i:Axis): SignBent (spinCharacter n i) BodyPull (fun x=>onsiteSensor x (petal i⊗ₖ A)):=by
 intro s w x y t; change flyMark _ _= _; apply spot_line s⁻¹ t.backward; obtain ⟨u,h,g⟩:= (mem_spin ..).1 w
 have ht:= castPet (spinZ s⁻¹.charge s⁻¹.s) i A
 have he:s⁻¹.s.perm i=i:= by change s.s.perm.symm i=i; rw [h]; rfl
 rw [he, show s⁻¹.charge=false from g] at ht; rw [show s⁻¹.charge=false from g, ht]; change _ = sign s.s i • (petal i⊗ₖ A); rw [show sign s.s i=sign s⁻¹.s i from (spin_sgn_inv i s h).symm,sign_hush,hush_false]; split; exact congrArg (fun u=>hush (s⁻¹.s.flip i) (petal i⊗ₖ u)) p; rfl
-- scalar mark cancel by ℓ on both phase tests.
def mapCoin : ℂ→ₗ[ℝ] Mark n where
 toFun c:= c • 1
 map_add' x y:= add_smul x y _
 map_smul' _ _:= smul_assoc ..
lemma coin_living (s:Sweep n)(x:ℂ): BodyPull s (mapCoin x)=mapCoin (tρ s x):=by
 funext i; change Hive.teen s⁻¹ (x • 1)= phaseB s x • 1
 rw [show Hive.teen s⁻¹ (x • 1)=phaseB s x • Hive.teen s⁻¹ 1 from ?_,map_one]
 unfold phaseB; rw [castT]; exact Scree.cumin s⁻¹.charge _ (γS s⁻¹) _ _
lemma empties {χ:SweepSign n}(i:Site n)(K:χ.KillsScalar)(x:ℂ) : orbitAverage BodyPull i χ (mapCoin x)=0:=by
 have he:orbitAverage tρ i χ x=0:=K _ (orbitAvg_t χ i x); funext j; rw [show orbitAverage _ i χ _ j= (mapCoin (n:=n)) (orbitAverage tρ i χ x j) from ?_,he]; exact mapCoin.map_zero
 unfold orbitAverage alleyS; rw [map_smul,map_sum]; simp_rw [coin_living,map_smul]
lemma silent_dark {χ:SweepSign n}(i:Site n)(A:K0) (K:χ.KillsScalar): orbitAverage BodyPull i χ (onsiteSensor i (silenceΦ A))=0:=by rw [show onsiteSensor i _= mapCoin _ from funext fun x=>silent_plain i A x]; exact empties i K _
-- work proofs
end SignSlot
end YM.CF.QuadClock
