import GaugeFieldConstruction.SconceFe
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 50000
noncomputable section
namespace YM.CF.BrentFe
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Precision Tree Push.SectorMeasure
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure Girt Tap
open YM.GaugeFieldConstruction (Flavor)
open YM.GaugeFieldConstruction.Flavor
section mat
variable {I:Type*}[Fintype I][DecidableEq I]
lemma tw_fe (U:UNI I)(P:Op I): twist U P=P ↔ U.val*P=P*U.val:=by
 refine ⟨fun h=>?_,twistFE U P⟩; nth_rw 2 [←h]; exact (twist_product U P).symm
 -- tune
lemma inverse_fe(U:UNI I)(P:Op I)(h:twist U P=P):twist U P⁻¹=P⁻¹:=by
 rcases Matrix.nonsing_inv_cancel_or_zero P with ⟨p,q⟩|g
 · apply Eq.symm; apply Matrix.inv_eq_right_inv; nth_rw 1 [←h]; rw [←map_mul,q,map_one]
 rw [g,map_zero]
lemma twistSumFE (U:UNI I)(f:ℕ→Op I)(h:∀ i,twist U (f i)= f i): twist U (∑' i,f i)=∑' i,f i:=by
 have ht(V:UNI I):Continuous (twist V):=by change Continuous (fun P=>V.val*P*star V.val); fun_prop
 change (twist U).toRingEquiv.toAddMonoidHom _=_; rw [Function.LeftInverse.map_tsum (g:=(twist U).toRingEquiv.toAddMonoidHom) (g':=twist (star U)) (f) (ht U) (ht _) (fun v=>twist_inv U v)]
 exact tsum_congr h
lemma matFe (x:BigFe)(g: SU.E) : (Ferr x).val*(matter g).val=(matter g).val*(Ferr x).val:= (YM.GaugeFieldConstruction.Matter.coeff_ok _ _).symm
lemma panelFe(i j:I)(f:Op Slot)(x:BigFe)(p:(Ferr x).val*f=f*(Ferr x).val): twist (RiseFe I x) (panel i j f)=panel i j f:=by
 let A:Op I:= Matrix.of fun s t=> if s=i ∧ t=j then 1 else 0; let M:= (Ferr x).val
 have he:panel i j f=A⊗ₖ f:=by ext a b; by_cases hx:a.1=i∧b.1=j <;> simp [panel,hx,A]
 rw [he]; apply twistFE; change TkFe _ M*_= _* TkFe _ M; unfold TkFe; rw [op_kron_mul, op_kron_mul,p,one_mul,mul_one]
end mat
variable {N P:Side}
abbrev ΨtFe(G:Ratio N P): BigFe→* UNI (Iota G):= RiseFe _
variable (x:BigFe)(G:Ratio N P)(U:Nom N P)
lemma dragFe (u v:Bool)(r t:Fir.St G.count)(k:Cover)(c:ℂ)(o:Lattice.Order): twist (ΨtFe G x) (drag G u v r t k c o (unionP U))=drag G u v r t k c o (unionP U):=by
 unfold drag; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; apply panelFe; unfold unionP; dsimp only; rw [track_pr, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; exact congrArg _ (matFe ..)
lemma douseFe(u v:Bool)(f:Track G.count)(o:Lattice.Order): twist (ΨtFe G x) (douse G u v f o (unionP U))= douse G u v f o (unionP U):=by
 unfold douse; simp_rw [map_sum]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => twistSumFE _ _ fun k=> dragFe ..
lemma mosaicFe(u v:Bool)(f:Track G.count): twist (ΨtFe G x) (mosaic G u v f (unionP U))= mosaic G u v f (unionP U):=by simp_rw[mosaic,map_smul,map_sum,douseFe]
lemma lapFe (u:Bool): twist (ΨtFe G x) (lobe G u)=lobe G u:=by
 apply twistFE; unfold lobe; change TkFe _ (Ferr x).val*_= _* TkFe _ (Ferr x).val; unfold TkFe; rw [op_kron_mul, op_kron_mul]; simp
lemma clothFe(j:ℕ)(M:Male): twist (ΨtFe G x) (Thread j M G (unionP U))= Thread j M G (unionP U):=by simp only [Thread,Peaks.cloth,map_add,map_mul,mosaicFe,lapFe,ΨtFe] -- tune
lemma ticketFe(j:ℕ)(v:Bool)(M:Male): twist (ΨtFe G x) (ticketT (Thread j) v M G (unionP U))= ticketT (Thread j) v M G (unionP U):=by unfold ticketT; rw [Peaks.revI]; simp only [map_add,map_mul,map_sub,map_one,map_star,inverse_fe _ _ (clothFe ..),clothFe,lapFe]
lemma cartsFe (v:Scree.Phys P): effectK (ΨtFe G x).val (cartsL (switchG G).symm v)= cartsL (switchG G).symm (effectK (FieldFe P x).val v):=by
 have hx:(ΨtFe G x).val=portW (switchG G).symm (FieldFe P x).val:=by
    let f:=blast G; ext i j; change ((1:Op _)⊗ₖ (Ferr x).val) i j = ((1:Op _)⊗ₖ (Ferr x).val) (f i.1,i.2) (f j.1,j.2); rw [Matrix.kronecker_apply,Matrix.kronecker_apply]; simp [Matrix.one_apply] -- tune
 rw [hx]; exact pompK ..

variable (b:Flavor)
abbrev TVFFe:=ΨtFe G (chipUFe b) -- bind x? b placed second
lemma oceanFe: acts (quant (TVFFe G b).val) (oceanA G)=oceanA G:=by
 unfold oceanA; rw [show acts _ _= _ from cartsFe (chipUFe b) G (mateK P)]; exact congrArg _ (tick_Fix P b)
lemma patchFe (k: Ket (Single N)): acts (ΨtFe G x).val (coat (patchQ G) k)= coat (patchQ G) (acts (FieldFe N x).val k):=by
 nth_rw 1 2 [←basis_expand k]; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=> congrArg _ ?_; rw [basis_shell]; apply PiLp.ext; intro t; rw [basis_act]; let J:= (Ferr x).val
 by_cases h:t∈ lows (patchQ G)
 · obtain ⟨l,v,rfl⟩:=mem_map.mp h; rw [←seamK,trails,basis_act]; change TkFe _ J _ _= TkFe _ J _ _; rcases i with ⟨⟨p,a⟩,c⟩; rcases l with ⟨⟨q,e⟩,g⟩; simp [TkFe,patchQ,rideG,Matrix.one_apply] -- tune
 rw [basin _ _ _ h]; change TkFe _ J _ _=0; rcases i with ⟨⟨p,a⟩,c⟩; rcases t with ⟨⟨q,o,d⟩,s⟩; simp [TkFe,patchQ,rideG,Matrix.one_apply]; rintro rfl H rfl; subst o; exfalso; exact h (mem_map.mpr ⟨((q,d),s),mem_univ _,rfl⟩)
lemma hoistFe (v:Scree.Phys N): hoist (patchQ G) (reefS G true) (acts (quant (TVfe N b).val) v)= acts (quant (TVFFe G b).val) (hoist (patchQ G) (reefS G true) v):=by
 refine Pyx.charge_i _ _ (reefS_deck ..) (TVFFe G b) (TVfe N b) (Tset N) (mateK N) (touchP N ▸ tickB N) (patchFe (chipUFe b) G) (tick_Fix N b) ?_ v
 have he:= oceanFe G b; rw [sec_phase,map_smul] at he; exact smul_right_injective _ (norm_pos_iff.mp ((sectorU G).symm ▸ zero_lt_one)) he
lemma pailFe (k:Wave (Iota G)): pailL (patchQ G) (reefS G true) (acts (quant (TVFFe G b).val) k)=acts (quant (TVfe N b).val) (pailL (patchQ G) (reefS G true) k):=by
 have h:= reefS_deck G true; let T:= pailL (patchQ G) (reefS G true); let A:= quantU (TVfe N b); let L:=quantU (TVFFe G b)
 apply PiLp.ext; intro i; rw[←basis_inner,←basis_inner]; let c:=basisKet i; let q:=acts (star A.val) c; have he:c=acts A.val q:=by unfold q; rw [←act_mul,A.property.2,act_one]
 change inner ℂ c (T (acts L.val k))= inner ℂ c (acts A.val (T k)); rw[he,act_unit_inner A]; unfold T; rw [pails _ _ h]; change inner ℂ (hoist _ _ (acts (quant _) q)) (acts L.val k)=_; rw [hoistFe]; exact Eq.trans (act_unit_inner L _ k) (pails _ _ h _ _|>.symm)
lemma fireFe (j:ℕ)(M:Male)(v:Scree.Phys P): fire (Thread j) G M (unionP U) (cartsL (switchG G).symm (effectK (TVfe P b).val v))=effectK (TVfe N b).val (fire (Thread j) G M (unionP U) (cartsL (switchG G).symm v)):=by
 rw [fire,fire]; rw [show ∀ v, effectK (TVfe N b).val v=acts (quant (TVfe N b).val) v from fun _=>rfl,map_smul]; apply congrArg; rw [← cartsFe]; unfold effectK
 rw [← act_mul, ←quant_mul, ← (tw_fe _ _).mp (ticketFe _ _ _ _ _ _), quant_mul, act_mul]; exact pailFe ..
lemma plankFe (Q:Op Slot)(h:(Ferr x).val*Q=Q*(Ferr x).val): twist (FieldFe N x) (plankP N Q)=plankP N Q:=by
 apply twistFE; rw [FieldPay]; unfold plankP headW; rw [←map_mul,←map_mul]; apply congrArg; unfold coΛ Lat.conjG; dsimp only; rw [jump_mul,jump_mul]; congr 1; ext1 i; simp only [Lat.color, op_kron_mul,h,one_mul,mul_one]
lemma scaleFe(Q:Op Slot)(h:(Ferr (chipUFe b)).val*Q=Q*(Ferr (chipUFe b)).val)(v:Scree.Phys N): scaleZ Q (effectK (TVfe N b).val v)=effectK (TVfe N b).val (scaleZ Q v):=by
 unfold scaleZ effectK; rw [map_smul]; apply congrArg; let V:=TVfe N b; let Z:= exp (-(plankP N Q)); have he:twist V Z=Z:=by unfold Z; rw [breeze_exp,map_neg,plankFe _ Q h]
 rw [←act_mul, ←quant_mul]; rw [←act_mul, ←quant_mul, show V.val*Z= _ from (tw_fe V Z).mp he] -- tune
#print axioms scaleFe
#print axioms fireFe
end YM.CF.BrentFe
