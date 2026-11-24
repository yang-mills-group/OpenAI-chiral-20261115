import YM.CF.Gas.Open
import YM.CF.Gas.Fiord
import YM.CF.Gloss.Core
import YM.CF.Ave.Current
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Maize
open Function Fock Filter Metric NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo RG Push.AbsoluteSums Trees Dial Paige Vault Brace
open scoped BoundedContinuousFunction Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Gloss Ave Phase.Sample
variable {H e p:ℝ} (s:Era m)
def WA (s:Era m)(B:Side) := Levier.spinU s.charge s.s -- tune
local notation "Ω" => netB m B s
abbrev LA (s:Era m)(B:Side) := mealU (castX (netB m B s)) (WA s B) (xtra s.charge) (CSide m B)
lemma style(s:Era m)(U:Skin m B): sings s.charge (LA s B) (wiel m B (northZ m B) U)=hush (detX s.s) (wiel m B (northZ m B) (turnV B s U)):= shutH _ (WA s B) _ (Levier.spinZ s.charge s.s) U
lemma pairs_h (F: ArrayF m)(k:Sq)(v:enoughV B e p)(h:0≤e)(U:Skin m B)(t: Guard U e)(z: Phase.Zone)(hz:k∈Phase.zone z)(he:Verified m B margin U F z): congrC (LA s B) (windX s.charge (bow m B U F k))= bow m B (turnV B s U) (αRow s F) k :=by
 let Y:= airing m B U F k; let X:=turnV B s U; have hx:=Τs B s v h U t F z k hz he; let W:=Ω; let q:=s.charge; let g:=prepU (castX W) (WA s B) (xtra q) Λ; have ht:= tickX (castX W) (xtra q) (WA s B) (Levier.spinZ q (castX W).s) Y
 let M:= Tulip.love Λ; have hm(A:Op (Model Λ)): windX q (M A)=M (windX q A):=by cases q<;>rfl
 apply M.injective; change congrC g (windX q (postC Y))=postC (fireA W Y) at ht; have hv : Verified m B margin X (αRow s F) z:=(β B s U F z).mpr he; rw [←hx] at ht
 have hu(A:Skin m B)(G:ArrayF m)(s:Guard A e)(g:Verified m B margin A G z): postC (airing m B A G k)=M (bow m B A G k):=by unfold postC spotC; rw [poet v s h g hz]; rfl
 unfold Y at ht; rw [hu U F t he,hu X (αRow s F) (ζx_o _ _ _ _ t) hv] at ht
 unfold congrC; rw [map_mul,map_mul]; rw [hm] at ht; exact ht
variable (g:Budget B e p)
def shotV(s:Era m)(x:Briar m B e):Briar m B e:=⟨turnV B s x.val,ζx_o _ _ _ _ x.property⟩
abbrev viewP (s:Era m)(x:Train m B e):Train m B e:=(shotV s x.1,sumX _ s x.2)
lemma toe(x:Train m B e)(p:x∈Breath m B e): viewP s x∈Breath m B e:=by change law _ _ (turnV _ _ _) (sumX _ _ _)≠0; rw [lawful]; exact p
abbrev Rayp (s:Era m)(B:Side): Ewe m B→ₐ[ℝ] Ewe m B := Scree.paintR s.charge (detX s.s) (LA s B)
lemma bendK (x:Train m B e)(p':x∈ Breath m B e)(τ:ℝ)(a:ℝ)(t:enoughV B e a)(q: Room B e): Rayp s B (retire m B (northZ m B) τ x)=retire m B (northZ m B) τ (viewP s x):=by
 let U:=x.1.val; let V:=turnV B s U; let Y:= wiel m B (northZ m B) U; let X:= wiel m B (northZ m B) V; let S:= Phase.pair m B U x.2; let A:=viewP s x; let r:=detX s.s
 have g:=x.1.property; have e:= A.1.property; have ht: Safe Y:=wiel_ok _ q g; have hx:Safe X:=wiel_ok _ q e; have he:=style s U; have hp : V=A.1.val:=rfl
 have hk: ZeroF m B U x.2:=(pays p').2; have hl:=chain_unit (northZ m B) q g hk; have hw:=kappa (northZ m B) q g hk
 change Rayp s B (Gas.brass (projector Y) S (decay Y τ))=Gas.brass (projector X) _ _; unfold Rayp; rw [Gas.poem s.charge (LA s B) _ ht.projection (C:=S) (show IsUnit (stage (projector Y) S) from hl) hw.1 hw.2.1 r, Gas.hymn_e s.charge _ r Y X ht hx he τ, fires_h _ _ (LA s B) Y X ht hx he,show swapX r (swapX r (projector X))= projector X from (by unfold swapX; split; abel; rfl)]
 let L:= pairs_h s (slot m x.2) (stick 0) t q.1 U g {(0:Row)} (stick_in 0 (by simp)) (show Verified m B margin U _ {(0:Row)} from hk)
 rw [show congrC (LA s B) (windX s.charge S)= pair m B A.1.val A.2 from L]; rfl -- tune
lemma H_tr(U: Skin m B) (c:Phase.Part m B): Matrix.trace (wiel m B c U)=0:=by
  let X := (3:ℂ) • (spin (CSide m B) SU.Slot grading)
  have hd j (t : Xmind m B) : Vplus c (links U) j t t=0 := by
    have he : advance j t.1≠t.1 := by
      intro h; have hp : t.1 j+1=t.1 j := by simpa [advance] using congr_fun h j -- tune
      have hq := add_eq_left.mp hp; have hk := suff_pos m B; haveI : Fact (1 < (CSide m B).val) := ⟨hk⟩; exact one_ne_zero (α:=Per (CSide m B)) hq
    rw [plus_block,jump_apply,if_neg he]
  have hk t : wiel m B c U t t=X t t := by rw [wiel,supportH,Matrix.add_apply,Matrix.sum_apply,sum_eq_zero,add_zero]; intro j _; simp [hd j t]
  rw [Matrix.trace]; change ∑ t:Xmind m B,wiel m B c U t t=0
  simp_rw [hk]; rw [Fintype.sum_prod_type]; apply sum_eq_zero; intro x _; rw [Fintype.sum_prod_type]; simp [X,spin,jump_apply,grading,SpinIdx,Fin.sum_univ_succ] -- tune
private lemma stripped {I:Type*}[Fintype I][LinearOrder I][Nonempty I](V:UNI I)(p k:Bool)(S T:Op I)(g:Safe S)(h:Safe T)(w:sings k V S=hush p T)(z:Matrix.trace T=0): Matrix.trace (T*projector T)=cSignX k (Matrix.trace (S*projector S)):=by
 have he:= fires_h k p V S T g h w; rw [← win_trace,← trace_twist V (windX k _),←singT, singm,w,he]
 cases p
 · rfl
 change _= (-T*(1-projector T)).trace; rw [mul_sub,mul_one, Matrix.trace_sub,neg_mul,Matrix.trace_neg,z,Matrix.trace_neg]; abel
lemma earn_H (U:Briar m B e)(q: Room B e) : energ m B (northZ m B) (shotV s U).val=energ m B (northZ m B) U.val:=by
 let H(X:Skin m B):=wiel m B (northZ m B) X; let X:=U.val; let V:=(shotV s U).val; have ht:sings s.charge (LA s B) (H X)=hush (detX s.s) (H V):=style s _; have he:= fires_h s.charge (detX s.s) (LA s B) (H X) (H V) (wiel_ok _ q U.property) (wiel_ok _ q (shotV s U).property) ht
 let W:= H X; let Y:= H V; have ho : cSignX s.charge (energ m B (northZ m B) U.val)=energ m B (northZ m B) U.val:=by generalize s.charge=v; cases v; rfl; exact realFlight q U _
 exact (stripped (LA s B) (detX s.s) s.charge W Y (wiel_ok _ q U.property) (wiel_ok _ q (shotV s U).property) ht (H_tr _ _)).trans ho -- exact via defeq
end YM.CF.Maize
