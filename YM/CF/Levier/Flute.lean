import YM.CF.Levier.Ville
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
open Proa Hake Pastry
variable (W:Meter Grave G e)(x:cro G e)
-- piece - budget, missing δ at incidence ⊥ contributes no anchor
abbrev heal(i:Grave)(S:Seal (Site (More P)))(x: cro G e):Op (Iota G):= if i.1=i.2.1∧carL i≠beltG i then (2:ℂ)⁻¹ • (W i S x-star (W (giveX i) S (chillF G e x))) else W i S x
def feeX (i:Grave): Op (Iota G):= if i.1=i.2.1∧carL i≠beltG i ∧ !i.1 then (2:ℂ)⁻¹ • 1 else 0
lemma clam_p (i:Grave)(p:∀ i,Bisca G e true true d r (W i)): Bisca G e true true d r (heal G e W i):=by
 unfold heal; by_cases k:i.1=i.2.1∧carL i≠beltG i; swap; · simp only [if_neg k]; exact p i
 simp only [if_pos k]; have ht:= (p (giveX i)).flips; have hy: Bisca G e true true d r (-(fun S x=> star (W (giveX i) S (chillF G e x))): NoteS G e):=by
    let X:= ht.sm (-1); simp only [norm_neg,norm_one,one_mul,neg_smul,one_smul] at X; exact X
 let Y:= ((p i).plusK hy).sm (2:ℂ)⁻¹; simp only [Pi.add_apply,Pi.neg_apply,←sub_eq_add_neg] at Y; convert Y using 1; norm_num; ring -- tune sm syntax
lemma giveF : ∀ i:Grave,giveX (giveX i)=i:=fun _=>rfl
lemma bite_p (S:Seal (Site (More P)))(i:Grave)(h:i.1=i.2.1 ∧ carL i≠beltG i)(t:chillF G e x=x): heal G e W i S x+star (heal G e W (giveX i) S x)=0:=by
 unfold heal; rw [if_pos h,if_pos (show (giveX i).1=(giveX i).2.1∧ carL (giveX i) ≠ beltG (giveX i) from ⟨h.1.symm,Ne.symm h.2⟩), giveF,t]; rw [star_smul]; simp [star_sub,smul_sub]
lemma pays_p (i:Grave)(p:i.1=i.2.1 ∧ carL i≠beltG i): feeX G i+star (feeX G (giveX i))=if i.1 then 0 else 1:=by
 unfold feeX; have hv: (giveX i).1=i.1:=p.1.symm; have hp:carL (giveX i)≠beltG (giveX i):=Ne.symm p.2; rw [hv]; have hg: (giveX i).2.1=i.1:=rfl; rw [hg]; cases q:i.1<;> simp [p.1 ▸ q,p.2,hp, ←add_smul]; norm_num
lemma eve_p(he: chillF G e x=x)(Z: Grave→ Op κ)(c: KindX (Urn.soar (oakN G Z)))(p:∀ i,∑ S,W i S x=Z i)(i:Grave): (∑ S,heal G e W i S x)+feeX G i=Z i:=by
 rw [← stern G e W x he Z c p i]; unfold veilT heal; by_cases k:i.1=i.2.1∧carL i≠beltG i; swap; · simp only [if_neg k]; rw [feeX,if_neg fun h=> k ⟨h.1,h.2.1⟩,add_zero]
 simp only [if_pos k]; let V:= whorl G e i; simp_rw [smul_add,sum_add_distrib]; congr 1; rw [← smul_sum]; unfold feeX whorl; cases h:i.1<;>simp [k.1 ▸ h,k.2,halo_sum] -- tune conv
lemma wingV(U: Grave→Op κ)(p:∀ i:Grave,i.1=i.2.1 ∧ carL i≠beltG i→ U i+star (U (giveX i))= (if i.1 then 0 else 1)): KindX (Urn.soar (oakN G U)):=by
 constructor
 · rintro ⟨t,i⟩ ⟨u,j⟩; change (if t=u then 0 else cSignX t (U (true,true,t,u) i j))+(if u=t then 0 else cSignX u (U (true,true,u,t) j i))=_; by_cases h:t=u; simp[h]; rw [if_neg h,if_neg (Ne.symm h)]; have hx:=p (true,true,t,u) ⟨rfl,h⟩; have he: U (true,true,t,u) i j + star (U (true,true,u,t) j i)=0:= Matrix.ext_iff.mpr hx i j; cases t<;>cases u; contradiction; exact he; simpa [cSignX] using congr_arg star he; contradiction
 rintro ⟨t,i⟩ ⟨u,j⟩; change (if t=u then 0 else cSignX t (U (false,false,t,u) i j))+(if u=t then 0 else cSignX u (U (false,false,u,t) j i))= (if (t,i)=revertP (u,j) then 1 else 0); by_cases h:t=u; · subst u; cases t <;> simp [revertP]
 rw [if_neg h, if_neg (Ne.symm h)]; have he: U (false,false,t,u) i j+star (U (false,false,u,t) j i)=(1:Op κ) i j:=Matrix.ext_iff.mpr (p (false,false,t,u) ⟨rfl,h⟩) i j; cases t <;> cases u; contradiction; simpa [Matrix.one_apply,cSignX,revertP] using he; by_cases p:i=j <;>simpa [p,Matrix.one_apply,cSignX,revertP] using congr_arg star he; contradiction
end YM.CF.Levier
