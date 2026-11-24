import YM.SU5.SatinWard.Resolution.Timpani
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
variable {N n B₀:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

-- End and turns. Preliminary rank receipts. Don't replace operator norm on preparation.
namespace SoulField
open Mezzo
variable {j:Axis}{U V:UNI SU.Slot}(h:Registrar U)(v:Registrar V)
local notation "Jι"=> Wage3

namespace Treaty
local notation "M"=> TuneM
-- use index `b:: true=ten`. exact color projection. natural basis cost `genCanon b` in full color. $Real Trace shadow`. holdings.
variable (b:Bool)(z y:Soul)
local notation "Θ" z:max=> (Reg z).val
abbrev gateH(b:Bool):Sheet:= if b then ac else ab
noncomputable abbrev ribbon (b:Bool): Soul→ₗ[ℝ] TuneM where
 toFun z:= passage (Reg z).val (gateH b) (gateH b)
 map_add' z w:=by simp only [map_add,Submodule.coe_add]; rfl
 map_smul' a z:=by simp only [map_smul]; rfl
local notation "R" b:max z:max=> ribbon b z
lemma ribbon_star : star (ribbon b z)=ribbon b z:=by
 obtain ⟨hx,h,_⟩:= paid_shape (Reg z); cases b; exact h; exact hx
lemma score_bracket : sonnet (ribbon true z) (ribbon false z)= Θ z:= (paid_shape (Reg z)).2.2.symm
lemma equivalent {z y:Soul} : z=y ↔ R true z=R true y∧R false z=R false y:=by
 refine ⟨fun g=>g ▸ ⟨rfl,rfl⟩,fun h=>Reg.injective ?_⟩; apply Subtype.ext; rw [←score_bracket z, ← score_bracket y,h.1,h.2]
-- lift from real Hermitian.Hold.Width.Clock.Leg.
noncomputable def felt (A B: TuneM) (p:star A=A)(q:star B=B): Soul:= Reg.symm (keepsake A B p q)
variable {A B:TuneM}(p:star A=A) (q:star B=B) -- B collision earlier B₀:Side! rename
lemma columnsH : R true (felt A B p q)=A ∧ R false (felt A B p q)=B:=by
 have hx: Θ (felt A B p q)=sonnet A B:=by unfold felt; rw [Reg.apply_symm_apply]; rfl
 exact (show passage (Reg (felt A B p q)).val ac ac=A ∧ passage (Reg (felt A B p q)).val ab ab=B from (by rw [hx]; exact coeffJoint ..)) -- v unused.B
noncomputable def patchH (b:Bool)(A:TuneM)(p:star A=A):Soul:= if b then felt A 0 p (star_zero _) else felt 0 A (star_zero _) p
lemma patch_here : R b (patchH b A p)=A:=by cases b; exact (columnsH (star_zero _) p).2; exact (columnsH p (star_zero _)).1
lemma patch_away : R (!b) (patchH b A p)=0:=by cases b; exact (columnsH (star_zero _) p).1; exact (columnsH p (star_zero _)).2
lemma duplicate (b:Bool){z y:Soul}(s:R b z=R b y)(h:R (!b) z=R (!b) y): z=y:= equivalent.mpr (by cases b; exact ⟨h,s⟩; exact ⟨s,h⟩)
lemma patches : z=patchH true (ribbon true z) (ribbon_star ..)+patchH false (ribbon false z) (ribbon_star ..):=by
 apply equivalent.mpr; rw [map_add, patch_here, show R true (patchH false _ _)=0 from patch_away (b:=false) _,map_add, patch_here, show R false (patchH true _ _)=0 from patch_away (b:=true) _, zero_add,add_zero]; exact ⟨rfl,rfl⟩
lemma invariant (z:Soul) : cc (Reg z).val=(Reg z).val↔∀ b,cc (ribbon b z)= ribbon b z:=by
 constructor; · intro h b; rw [←score_bracket z,←coeffCC] at h; cases b; exact (coeffInj h).2; exact (coeffInj h).1
 intro h; nth_rw 1 [←score_bracket z]; rw [←coeffCC,h,h,score_bracket]
lemma valid_arm (u: cc A=A): cc (Θ (patchH b A p))=(Θ (patchH b A p)):=by
 refine (invariant _).2 (fun i=>?_); have e': i=b∨i=!b:=by cases b<;> cases i<;>simp
 rcases e' with e|e; rw [e,patch_here]; exact u; rw [e,patch_away,cc_zero]
-- traces and means. real prices generation traces; color normalization separate.
noncomputable abbrev zen (x:TuneM):ℝ:=x.trace.re
noncomputable def generation (b:Bool):Soul→ₗ[ℝ]ℝ where
 toFun z:= zen (ribbon b z)
 map_add' z w:=by rw [map_add, zen, Matrix.trace_add,Complex.add_re]
 map_smul' z w:=by rw [map_smul,zen,Matrix.trace_smul,Complex.smul_re]; rfl
local notation "Uq"=> generation
lemma Zen_trace(A:M)(p:star A=A): (↑(zen A):ℂ)=A.trace:= by
 have hx:star A.trace=A.trace:= ((Matrix.trace_conjTranspose A).symm.trans (congrArg Matrix.trace p)) -- rewrite?
 unfold zen; rw [Complex.star_def, Complex.conj_eq_iff_re] at hx; exact hx
lemma z_at : (↑(generation b z):ℂ)=(ribbon b z).trace:=Zen_trace _ (ribbon_star b z)
noncomputable def genCore (b:Bool):Soul:= patchH b 1 (star_one _)
lemma core_bill : Uq b (genCore b)= 3:=by change zen _= _; rw [genCore,patch_here,zen,Matrix.trace_one]; simp
lemma core_other : Uq (!b) (genCore b)=0:=by change zen _= _; rw [genCore,patch_away,zen,Matrix.trace_zero]; rfl
noncomputable abbrev depth : Submodule ℝ Soul:= (Uq true).ker ⊓ (Uq false).ker
lemma depth_iff : z∈ depth ↔ ∀ i:Bool, Uq i z=0:= by
 rw [Submodule.mem_inf]; refine ⟨fun h i=>?_,fun h=>⟨h true,h false⟩⟩; cases i; exact h.2; exact h.1
noncomputable abbrev reconstructH (z:Soul): Soul:= ((generation true z)/3) • genCore true+ ((generation false z)/3) • genCore false
lemma blendRem: z-reconstructH z∈ depth:=by
 refine (depth_iff _).2 (fun i=>?_); rw [map_sub,reconstructH,map_add,map_smul,map_smul]; cases i <;> rw [core_bill]; · rw [show generation false (genCore true)=0 from core_other true, smul_zero,zero_add]; change _-(_*3:ℝ)=0; ring -- core_other (!true). defeq.
 rw [show generation true (genCore false)=0 from core_other false, smul_zero,add_zero]; change _-(_*3:ℝ)=0; ring
-- Unit block light; any registrar acts by genuine generation unitary, not involving ir weights. Exact. Recital.Formal
variable {U': UNI SU.Slot}(h':Registrar U')
include h'
lemma cred_full : ∃ a: UNI (Fin 3) × UNI (Fin 3), U'= vote a := by
 let A:= passage U'.val ac ac; let B_:= passage U'.val ab ab; have he: U'.val=sonnet A B_:= collaborations _ (fun i=> (still_U.mp (h' i)).symm); have hp:= U'.property.2; rw [he,←coeffStar,←coeffMul,←initial_jet] at hp; obtain ⟨hx,hy⟩:= coeffInj hp; refine ⟨(⟨A,Matrix.mem_unitaryGroup_iff.mpr hx⟩,⟨B_,Matrix.mem_unitaryGroup_iff.mpr hy⟩),Subtype.ext he⟩
lemma genConcert : generation b (rotor h' z)= generation b z:=by
 obtain ⟨x,hx⟩:=cred_full h'; set A:= R true z; set B₁:=R false z
 let z':= rotor h' z; have ht:sonnet (ribbon true z') (ribbon false z')=sonnet (twist x.1 A) (twist x.2 B₁):=by rw [score_bracket]; rw [show (Reg z').val= twist U' (Reg z).val from rotor_pay ..,hx,show (Reg z).val= sonnet A B₁ from (score_bracket z).symm,rotate_vote]
 have hp(x:UNI (Fin 3))(A:TuneM):zen (twist x A)=zen A:=by
    unfold zen; rw [twist_formula, Matrix.trace_mul_comm,←mul_assoc, show star x.val*x.val=1 from x.property.1,one_mul]
 obtain ⟨h₁,h₂⟩:= coeffInj ht; change zen (ribbon b z')= zen (ribbon b z); cases b
 · rw [h₂,hp]
 rw [h₁,hp]
lemma depth_rotate (x:Soul) : x∈ depth ↔ rotor h' x∈ depth:=by simp_rw [depth_iff, genConcert _ x h']
omit h'
-- real appointments traced.CC. means & center characterization via commutation.Memory. Keep equivalences both.
noncomputable abbrev pureHeart :Submodule ℝ Soul:=Submodule.span ℝ {genCore true,genCore false}
lemma reconstructS : reconstructH z ∈ pureHeart:=by
 unfold reconstructH; exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert ..))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
include h' in
lemma genCore_shift : rotor h' (genCore b)=genCore b:=by
 apply Reg.injective; apply Subtype.ext; rw [rotor_pay, ←score_bracket]; obtain ⟨x,hx⟩:=cred_full h'; rw [hx,rotate_vote]; -- need rewrite rhs bracket as well
 cases b
 · rw [genCore,patch_here, show R true (patchH false 1 _)=0 from patch_away false _, map_zero,map_one]
 rw [genCore,patch_here, show R false (patchH true 1 _)=0 from patch_away true _, map_zero,map_one]
lemma purist(u:z∈pureHeart) (h:Registrar U'): rotor h z=z:=by
 let Z: Soul →ₗ[ℝ] Soul:= rotor h - LinearMap.id; have hp: pureHeart ≤ Z.ker:=by refine Submodule.span_le.mpr (fun x hx=>?_); change Z x=0; obtain v:= Set.mem_insert_iff.mp hx; change rotor h x-x=0; rcases v with v|v; rw [v,genCore_shift ..,sub_self]; rw [Set.mem_singleton_iff.mp v,genCore_shift ..,sub_self]
 exact sub_eq_zero.mp (show Z z=0 from hp u)
lemma purity (t:∀ (x:UNI SU.Slot)(p:Concert x),cc x.val=x.val→ rotor p.gate z=z) : z∈ pureHeart:=by
 let X:= (Reg z).val; have he:∀ i:SU.E,Commute (matter i).val X:=fun i=> ((show ChiralX 0 X from (Reg z).property).1 i).symm; obtain ⟨a,b,e⟩:= fiscal X he (fun x v p=>(rotor_pay v.gate z).symm.trans (congrArg (fun z:Soul=>(Reg z).val) (t x v p)))
 have h (c:ℂ)(q:Bool)(u:R q z=c • 1): generation q z=3*c.re ∧ c=↑c.re:=by
    have hp:= ribbon_star q z; rw [u, star_smul,star_one] at hp
    have hv:star c=c:=by simpa [Matrix.one_apply_eq] using Matrix.ext_iff.mpr hp 0 0
    refine ⟨?_,?_⟩; · change zen _=_; rw [u,zen,Matrix.trace_smul,Matrix.trace_one]; norm_num; ring
    rw [Complex.star_def,Complex.conj_eq_iff_re] at hv; exact hv.symm
 obtain ⟨u,v⟩:= coeffInj ((score_bracket z).trans e); let hx:=h a true u; let hp:=h b false v;
 rw [show z=reconstructH z from ?_]; exact reconstructS _
 refine equivalent.mpr ⟨?_,?_⟩
 all_goals (unfold reconstructH genCore; rw [map_add,map_smul,map_smul,patch_here]; simp_rw [hx.1,hp.1])
 · rw [show R true (patchH false 1 _)=0 from patch_away false _,u, smul_zero,add_zero,show (3*a.re)/3=a.re from (by ring),← Complex.coe_smul,hx.2.symm]
 rw [show R false (patchH true 1 _)=0 from patch_away true _,v, smul_zero,zero_add,show (3*b.re)/3=b.re from (by ring),←Complex.coe_smul,hp.2.symm]
#print axioms purity
end Treaty
end SoulField
end ShapeLab
end YM.CF.QuadClock
