import GaugeFieldConstruction.Glow3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner Ladder3 Branch Tenant XGarden.MastTin
variable (F:RegLime I α n)(Q:LeaseQ γ n)(k:I)(M:Mica I β n){J:Type}[Fintype J](C:J→Factor3 n)
section
variable (P:BudgetPoint)(L K:ℕ)(S:Ids n)(σ:I→Seat n)
local notation "G"=> Actors Q C
local notation "B"=> P.B
local notation "Φ" i:max=> C (i:Actors Q C).1
local notation "V0" i:max=> spark3 Q C P L i
local notation "Z" i:max=> (core3 Q (Φ i) i.2.1)
local notation "Hq" i:max=> (spark3 Q C P L i).val.2
-- storage A3 trigger $one label uses exactly k images on small$ include P.B halo.LAny.
structure Frosty (u:γ→ℝ)(h η:ℝ):Prop where
    burn(i:γ)(x:Seat n)(X:Support (More n))(p:Q.X i⊆ Lattice.halo P.B {x})(b:Lattice.halo (P.B+1) {x} ⊆ X) : Medal P X ∅ (Q.issue i ∅) h (η*u i)
variable {c ℓ r h p δ δ' η:ℝ}{U:γ→ℝ}{A:J→ℝ}
variable (X:KPower Q δ' c U)(Yt:∀ i, BasePower (C i) (A i)) (v:∀ i,Act3 (C i) P K h (A i))(W:Leased Q P K h U)
variable (t:1≤ h)(d:0 <r)(w:0<δ')
variable (i:Actors Q C)(s:i∈IIW Q C)
local notation "R"=> (C i.1)
local notation "Jμ"=> i.2.1
local notation "Uμ"=> i.2.1.2
local notation "hμ"=> AgeQ Q (C i.1) i.2.1
local notation "ρ"=> ThermalH L
local notation "Zκ"=> V0 i
local notation "Ξ"=> Win3 Q C r U A i
-- point.T. Numerical primitive
section
variable {V:γ→ℝ}
include s t i
lemma cento (u:Act3 (C i.1) P K h p) (H:Leased Q P K h U) (μ:Support (More n)) (F:(C i.1).H.val.2 ⊆ μ) (hp:0 ≤p) (E:∀ j: Fin (AgeQ Q (C i.1) i.2.1),Medal P μ ∅ (Q.issue (i.2.1.2.val j) ∅) h (V (i.2.1.2.val j))) : Medal P μ ∅ (oV (PoleQ Q C S i)) h (tank3 Q (C i.1) 1 p V i.2.1):=by
    let A':= Φ i; let p':=hμ
    let a:= A'.issue ∅; let f(i:γ):=Q.issue i ∅; let L':=List.ofFn i.2.1.2.val; let z:= Coral a f L'; let q:=discount hμ (AgeP Q (C i.1) i.2.1); let V':= q • z
    have Hg(y:Orbit n):oV (PoleQ Q C S i) y= fair (V' y):=by
       apply congrArg fair; change q • scar (A'.issue ∅ (y.1,S)) _= q • scar _ _; rw[u.turf]; apply congrArg (fun w=>q • (scar _ w)); apply List.map_congr_left; exact fun j _=>H.mint ..
    rw [funext Hg]; obtain ⟨a'',x⟩:=u.pays μ ∅ F (by simp [Lattice.halo])
    have he(j:γ)(v:j∈L'):Medal P μ ∅ (f j) h (V j):=by
       change j∈List.ofFn _ at v; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp v; exact E _
    have hs:= fair_port P μ ∅ V' ((Coralμ0 a f L' P V μ ∅ x (fun j w=> colorIn _ _ _ _ (he j w) t) (fun j w=> (he j w).wage (zero_le_one.trans t)) hp).sMul q) (opThemeScale _ (Coral0 a f L' μ a'' (fun j w=> (he j w).toThemeR)))
    apply Medal.big hs; unfold tank3 zcost3 L'; simp only [List.length_ofFn,List.map_ofFn,List.prod_ofFn,mul_one]
    let X:=AgeP Q (C i.1) i.2.1; change _ ≤ ‖q‖ * (2:ℝ)^(X+hμ)*p*_
    have h:X=0:= (mem_filter.mp s).2.1; rw [h,zero_add]; apply le_of_eq; dsimp only [AgeQ, Function.comp_apply]; -- tune power defeq
    ring
-- cereal.Bursar
omit s t i
include S
lemma earnZ(i:Hub n)(F:InkD n)(X:ℝ)(w:ℕ)(H:Medal P i.val.2 ∅ (oV F) h X)(g:0≤h): PressB (Py.KeyUp P) i F h (fareX w (Py.KeyUp P) i.val.2*X):=by
 have ht:Medal (Py.KeyUp P) i.val.2 ∅ (oV F) h X:=by
    obtain ⟨Zz,h,lB,m⟩:=H.pays; exact ⟨H.toThemeR,Zz,h,fun i e u q=>lB _ e q,m⟩
 apply ht.preservesE S g
end
open Py Py.Riant Nor
include i s X Yt v W t d
lemma lirp : Medal P (Hq i) ∅ (oV (PoleQ Q C S i)) h ((Win3 Q C r U A i)/r):=by
    have ht:=cento Q C P K S t i s (V:=U) (v i.1) W (Hq i) ((padd_on ..|>.steady i.2.1).1) (Yt i.1).pos (fun j=> W.ready _ _ _ (later_p Q (C i.1) Jμ j |>.trans subset_union_right) (by simp[Lattice.halo])) -- tune
    apply Medal.big ht; unfold Win3 γhop; rw[if_neg (by rw[(mem_filter.mp s).2.2]; simp)] -- tricky dependent HB
    unfold tank3 zcost3; apply le_of_eq; field_simp
variable (uη: 0 ≤η)(Uη:η≤1)(sU:Frosty Q P U h η)(h3:0< AgeQ Q (C i.1) i.2.1)
include uη Uη sU h3 w
lemma worth_t (hM:(core3 Q (Φ i) i.2.1).val.2.card≤P.B): Medal P (Hq i) ∅ (oV (PoleQ Q C S i)) h (η*Win3 Q C r U A i /r):=by
    by_cases x: Win3 Q C r U A i=0
    · apply Medal.big (lirp Q C P L K S X Yt v W t d i s)
      rw[x,mul_zero]
    let Jκ:= AgeQ Q R Jμ
    have hp:Grove (terr _) (core3 Q (C i.1) i.2.1).val.2:= portPatch Q C X Yt w W.later d.le i x
    let Z':= Lattice.halo P.B {(C i.1).H.val.1}
    have hq : (core3 Q (C i.1) i.2.1).val.2⊆ Z' :=by
       intro j f; apply halo_spec.mpr; refine ⟨(C i.1).H.val.1,Finset.mem_singleton_self _, (show separation _ j≤ (core3 Q (C i.1) i.2.1).val.2.card from ?_).trans hM⟩; exact (show separation _ _< (Z i).val.2.card from hp.lim _ (Z i).property _ f).le
    have b': (C i.1).pure=false:=Bool.eq_false_iff.mpr (fun t=> Nat.not_lt.mpr (le_trans (b:= (Jμ).1.val.1+(Jμ).1.val.2) (Nat.le_add_right ..) (((specs₃ ..).1 (Jμ).1.property).trans_eq (if_pos t))) h3) -- tune if_pos
    have H':Lattice.halo (P.B+1) {(C i.1).H.val.1}⊆ Hq i:= le_trans (b:=Lattice.halo (ThermalH L*P.B) _) (Lattice.Corona.halo_mono (by have hp:=P.B_pos; unfold ThermalH; nlinarith) le_rfl) (halo_pad Q R P L i.2.1 b')
    apply Medal.big (cento Q C P K S t i s (V:=η • U) (v i.1) W (Hq i) (by apply le_trans (padd_on Q R P L|>.steady i.2.1).1 le_rfl) (Yt i.1).pos (fun j=>sU.burn _ _ (Hq i) ((later_p Q R i.2.1 j).trans hq) H'))
    have hs:Win3 Q C r U A i=tank3 Q R r (A i.1) U i.2.1:= if_neg (by rw[(mem_filter.mp s).2.2]; simp)
    rw [hs]; unfold tank3 zcost3; simp only [Pi.smul_apply,smul_eq_mul, Finset.prod_mul_distrib,prod_const,card_univ,Fintype.card_fin, mul_one]; rw [le_div_iff₀ d];
    let A':=‖discount hμ (AgeP Q R Jμ)‖*(2:ℝ)^(i.2.1.1.val.2+i.2.1.1.val.1)* A i.1
    let B':= ∏ j:Fin hμ,U ((Uμ).val j)
    change (A'*(η ^ hμ* B')) * r≤ η* (A' * r * B'); have hu:0≤ B':=prod_nonneg (fun _ _=> X.pos _); have hx:0≤ A':=mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (by norm_num) _)) (Yt i.1).pos
    have he:η ^ hμ≤ η:=(pow_le_pow_of_le_one uη Uη (show 1≤ hμ from h3)).trans_eq (pow_one _)
    nlinarith only[mul_le_mul_of_nonneg_right he (show 0≤ A'*B'*r from by positivity)]
omit h3 uη Uη sU w
include t X Yt
lemma hue_B (q:AgeQ Q (C i.1) i.2.1=0): core3 Q (C i.1) i.2.1=(C i.1).H ∧ Medal P ((C i.1).H.val.2) ∅ (oV (PoleQ Q C S i)) h (Win3 Q C r U A i / r) ∧ Win3 Q C r U A i=A i.1*r ∧ PoleQ Q C S i=(fun u=> fair ((C i.1).issue ∅ (u,S))):=by
 let p:= i.2.1.1.val.1; let d':=i.2.1.1.val.2; have hp:p=0:=q; have hd:d'=0:= (mem_filter.mp s).2.1
 letI:IsEmpty (Fin p):=by rw[hp]; infer_instance
 let f:= C i.1; let G0:=cento Q C P K S t i s (V:=U) (v i.1) W f.H.val.2 le_rfl (Yt i.1).pos (fun i=> by exact Fin.elim0 (hp ▸ (show Fin p from i)))
 have he(u:ℝ): tank3 Q f u (A i.1) U i.2.1=A i.1*u:=by
    unfold tank3 zcost3; rw [univ_eq_empty,Finset.prod_empty,mul_one]; change ‖discount p d'‖* 2^(d'+p)*_ * _=_; rw [hp,hd]; simp [discount]
 have hx:Ξ=A i.1*r:= (if_neg (by rw[(mem_filter.mp s).2.2]; simp):γhop Q (C i.1) r _ U i.2 = tank3 Q f r (A i.1) U i.2.1).trans (he r)
 refine ⟨?_,?_,hx,?_⟩
 · unfold core3; apply Subtype.ext; refine Prod.ext rfl ?_; change (C i.1).H.val.2 ∪ ((univ:Finset (Fin p)).biUnion _)= _; rw[univ_eq_empty,biUnion_empty,union_empty]
 · exact G0.big (le_of_eq ((he 1).trans (show _= _ from (by rw[hx,mul_one,mul_div_cancel_right₀ _ d.ne']))))
 funext i₀; let Z0:= i.2.1.2
 apply congrArg fair; change discount p d' • scar _ ((List.ofFn Z0.val).map _) = _
 have ht: (List.ofFn Z0.val)=[]:= List.eq_nil_of_length_eq_zero (List.length_ofFn.trans hp)
 rw[ht,hp,hd]; simp only [discount,Nat.factorial_zero,Nat.cast_one,mul_one,inv_one,List.map_nil,one_smul]; rfl

end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
