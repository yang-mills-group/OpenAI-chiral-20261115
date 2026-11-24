import YM.CF.Gloss.Move
import YM.CF.Gloss.Lamp
import YM.CF.Spire.Elys
import YM.CF.Brace.Quartz
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable(B)(x:Era m)
open Dial Tulip Peaks Paige Vault Brace Rush
variable{L:Side}{j:ℕ}{ho:Odd L.val}{T:Pricing j L ho (Thread j)}{e:ℝ}{P:Grasp T B e}(X:Pearl P)(D:Stamped j L ho T)(h:1 ≤ j)(g:P.roundZ ≤(CSide m B).val)(q:0 < e)
local notation "aX"=> castX (netB m B x)
local notation "cn" => northZ m B
variable (U:Skin m B)(u:Guard U e)(v:ArrayF m)(t:Phase.Zone)(V:Verified m B margin U v t)
include X D h g q u V
lemma cry_h(z y:Sq)(YZ:z∈zone t)(uY:y∈zone t): Phase.ray m B cn (turnV B x U) (αRow x v) z y=payZ x (Phase.ray m B cn U v z y):=by
 let W:= P.topB; let F:= P.cost m firstM; let y':= P.couture g firstM; let d:= castX (netB m B x)
 let U':= turnV B x U; let Q(t):= airing m B U v t; let Q'(t):= airing m B U' (αRow x v) t
 have hv:= ζx_o B x e U u; let V₁:= αRow x v; have hV:Verified m B margin U' V₁ t:= (β B x U v t).mpr V
 -- use cantor lemma in Spire
 rw [←bridgeK W P.baseY y' u V z y YZ uY,←bridgeK W P.baseY y' hv hV z y YZ uY,Τs B x W q.le U u v t z YZ V,Τs B x W q.le U u v t y uY V]
 -- converse cantor. need check
 have ht(i: Sq)(t':i ∈ zone t) : Slow U (hook (airing m B U v i)) X.q:=fun j k=> (kleid X.ample u q.le V t' j k).trans_le X.wide
 let G:= truckW (X.tick m) _ P.small; obtain ⟨A,wA⟩:=det_sub x.charge d.s
 exact (cantor d (xtra x.charge) A wA h y' (D.fields_one _ (P.needed.trans g)) P.gem U u G (X.roof.trans P.small) _ _ (ht _ YZ) (ht _ uY)).symm
omit V
variable(k:Cue m)(h_k:ZeroF m B U k)
omit h u X D g q in
lemma thread_p(A E:Cue m): Phase.twin m (sumX _ x A) (sumX _ x E)= αRow x (Phase.twin m A E):=by
 ext i : 1; unfold Phase.twin αRow capRow sumX; by_cases t:i.2=1<;> simp [slot,t]
omit h u X D g q in
lemma θ_sub {m:Side} (x:Era m)(a b:ℂ): payZ x (a-b)=payZ x a-payZ x b:=by unfold payZ; cases wageZ x<;>simp [cSignX]
include h_k
lemma owns_H: Phase.accord m B cn (turnV B x U) (sumX m x k)=payZ x (Phase.accord m B cn U k):=by
 let I:=sumX m x; let Z:=turnV B x U; have hB:=ζx_o B x _ U u; have hg (Y) (p:ZeroF m B U Y): ZeroF m B Z (I Y):= (voxel B x _ (U,Y) ⟨u,p⟩).2
 have ht(y)(p:ZeroF m B U y): logs m B cn Z (I y) (I k)=payZ x (logs m B cn U y k):=by
    obtain ⟨f,p,H⟩:= arches p h_k; have he(y)(h:EdgeP m B U y f): EdgeP m B Z (I y) (I f):=by unfold EdgeP I; rw [thread_p]; exact (β B x U (Phase.twin m y f) _).mpr h
    rw [echoes _ P.baseY hB _ _ (I f) ⟨he _ p,he _ H⟩,echoes _ P.baseY u y k f ⟨p,H⟩]; unfold bill amount; rw [θ_sub, show Phase.twin m (I y) (I f)=_ from thread_p .., show Phase.twin m (I k) (I f)=_ from thread_p ..]; exact congrArg₂ (·-·) (cry_h B x X D h g q U u _ _ (show Verified m B margin U _ (insert 1 {0}) from p) _ _ (stick_in 0 (by simp)) (stick_in 1 (by simp))) (cry_h B x X D h g q U u _ _ (show Verified m B margin U _ (insert 1 {0}) from H) _ _ (stick_in 0 (by simp)) (stick_in 1 (by simp)))
 unfold Phase.accord; rw [← (ψRain x).integral_comp ((pasM x).measurableEmbedding) (lyre m B cn Z (I k))]
 have he(y:Cue m): lyre m B cn Z (I k) (I y)=payZ x (lyre m B cn U k y):=by
    unfold lyre; rw [show law m B Z (I y)=_ from lawful ..]; by_cases p: law m B U y=0; · rw [p]; unfold payZ; cases wageZ x<;> simp [cSignX]
    rw [ht _ (law_rich m B _ _ p)]; unfold payZ; cases wageZ x<;> simp [cSignX]
 change (∫ y, lyre m B cn Z (I k) (I y)∂rains m)=_; simp_rw [he]; unfold payZ; cases wageZ x
 · rfl
 exact integral_conj -- tune
lemma war_v : Phase.fund m B cn (turnV B x U) (sumX _ x k)=payZ x (Phase.fund m B cn U k):=by
 let S:=cutM (Lat.upperP (CSide m B)); let w:=slot m k; let x':=sumX m x k; let t:=netB m B x; let K:=turnV B x U; let v: Phase.Zone:=insert (0:Row) ∅; have he:K= _:= (rfl:K=flashA t U); have hv := voxel B x _ (U,k) ⟨u,h_k⟩; let F:=t.s; let T:= castX t
 have h_:K=turnV B x U:=rfl
 obtain ⟨A,wA⟩:= det_sub t.charge T.s; have hp:slot m x'=αRow x w:=rfl; let v':= P.couture g firstM
 let y:=stick (0:Row); have hY:y∈zone v:=stick_in _ (by unfold v; simp); let O:=airing m B U w y; have hK:Guard K e:=hv.1; have he : ZeroF m B K x':= hv.2; have hk:=ark_align P.topB P.baseY v' u (show Verified m B margin U w v from h_k) y hY; have hZ:=ark_align P.topB P.baseY v' hK (show Verified m B margin K _ v from he) y hY
 unfold Phase.fund; rw [owns_H B x X D h g q U u k h_k];
 have hg: netsal (lens m B cn K) (Phase.pair m B K x')=netsal (lens m B cn U) (Phase.pair m B U k):=by
    apply Real.exp_injective; rw [salary cn P.baseY hK he,salary _ P.baseY u h_k]
    let a:=helix (CSide m B); rw [←carts_n a.symm _,← carts_n a.symm (filled (lens m B cn U) (Phase.pair m B U k))]; change ‖cartsL (helix _).symm (filled (lens m B cn K) (bow m B K (slot m x') y))‖=‖cartsL (helix _).symm (filled (lens m B cn U) (bow m B U w y))‖; rw [←hk,←hZ,hp,show airing _ _ K (αRow x w) y=fireA t O from Τs B x P.topB q.le U u w v y hY h_k]
    exact chapelN X D g h O U u firstM T (xtra t.charge) A wA
 rw [hg]; unfold payZ; cases wageZ x <;> simp [cSignX]
end YM.CF.Gloss
