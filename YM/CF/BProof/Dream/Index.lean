import YM.CF.BProof.Dream.Gamma
/-! License T_z(s,v) interpolation. Smooth square filling over SU copy,
then descend by congruence. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix SU Finset Function Metric Complex Extension.Mar Mag
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {n : Type*}[Fintype n][DecidableEq n]
abbrev Sq := ℝ×ℝ
abbrev Bz(i:Fin 5) := species (locus i)

lemma curvesS : ContDiff ℝ ∞ each:=by
 apply smoothM
 let L(i j:F) : Op F →ₗ[ℝ] ℂ:=⟨⟨fun A=>A i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩; have he(i j:F):ContDiff ℝ ∞ (fun A:Op F=> A i j):= (L i j).toContinuousLinearMap.contDiff
 rintro (i|i) (j|j)
 · simp only [each,Join.both, fromBlocks_apply₁₁,ExTwo.wedge_entry]; exact ((he ..).mul (he ..)).sub ((he ..).mul (he ..))
 · exact contDiff_const
 · exact contDiff_const
 exact (starL ℝ : ℂ≃L[ℝ] ℂ).contDiff.comp (he i j)
lemma squareT {U:ℝ→Op Sheet}{i:Fin 5}(h:ContDiff ℝ ∞ U)(v:U 0=1)(t:U 1=Bz i)(p:∀ x,inK (U x)) :
   ∃ S:Sq→ Op Sheet, Extension.Mar.Suit Window S ∧ (∀ x∈Window,inK (S x)) ∧
   ∀ x∈Zone, S (0,x)=1 ∧ S (x,1)=1 ∧ S (x,0)=U x ∧ mold (S (1,x)) living=(gamma i).seat (1-x) := by
 let g:= gamma i; let V:=g.line (1/2); let W:=Bz i; have hw: mold W living=g.seat 1:=g.seat1.symm
 have hv:=g.road (1/2); change inK V at hv; let Y:=star V*W; have hy:mold Y living=living:=by rw [show Y=star V*W from rfl,layers,hw,g.seatLift,←layers, show star V*g.line (1/2)=1 from hv.1.1,mold_one]
 obtain ⟨P,H⟩:= flavourFactor lv living_star lk.1; obtain ⟨A,hA,e,w,T⟩:= smoother P (kingMul (kingStar hv) (classK _)) (show mold Y (mold P.val 1)=_ from by rw [H,hy])
 let S(x:ℝ):=g.line ((1-x)/2)*A x; have hs: ∀ x:ℝ, mold (S x) living=g.seat (1-x):=by intro x; unfold S; rw [layers, show mold (A x) living=_ from (by rw [←H]; exact (T x).2 : mold (A x) living=living),g.seatLift]
 have Hs:ContDiff ℝ ∞ S:= (g.smooth.comp (((contDiff_const.sub contDiff_id)).div_const 2)).mul hA
 have ht:S 0=W:=by unfold S; rw [e,sub_zero]; change V*(star V*W)= _; rw [← mul_assoc,hv.1.2,one_mul] -- tune semicolon
 have hz:S 1=1:=by unfold S; rw [w,sub_self,zero_div,g.line0,mul_one]
 let f(x:Sq) (A: Op Sheet):= (1-x.2) • A+x.2 • (1:Op Sheet); let F(x:Sq):= f x (U x.1)+x.1 • (S x.2-f x W)
 let B: Set Sq:= Window ∩ {x| x.1=0 ∨ x.1=1 ∨ x.2=0 ∨ x.2=1}
 have h0(x:ℝ): F (0,x)=1:=by unfold F f; dsimp only; rw [v,zero_smul, add_zero]; module
 have h1(x:ℝ): F (1,x)= S x:= by unfold F f; dsimp only; rw [t, one_smul]; change _+(_-_)=_; unfold W; abel -- tune
 have hv(x:ℝ): F (x,0)= U x:=by simp [F,f,ht]
 have hu(x:ℝ): F (x,1)=1:=by simp [F,f,hz]
 have hg(x:Sq)(hx:x∈ B):inK (F x):=by
   obtain ⟨x,y⟩:= x; rcases hx.2 with hp|hp|hp|hp; change x=0 at hp; subst x; rw [h0]; exact kingOne; change x=1 at hp; subst x; rw [h1]; exact kingMul (g.road _) (T _).1; change y=0 at hp; subst y; rw [hv]; exact p _; change y=1 at hp; subst y; rw [hu]; exact kingOne
 have Hb (g:Sq→Op Sheet)(h:ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x=> f x (g x)):= ((contDiff_const.sub contDiff_snd).smul h).add (contDiff_snd.smul contDiff_const)
 obtain ⟨G,hG,e,E⟩:= rect_climb F B (fun _ h=>h.1) ((Hb (fun x=>U x.1) (h.comp contDiff_fst)).add (contDiff_fst.smul ((Hs.comp contDiff_snd).sub (Hb (fun _=>W) contDiff_const)))) hg
 refine ⟨G,hG,E,fun x hx=>?_,⟩ -- tune trailing ,
 exact ⟨(e (show (0,x)∈B from ⟨⟨z0,hx⟩,Or.inl rfl⟩)).symm.trans (h0 x),(e (show (x,1)∈ B from ⟨⟨hx,z1⟩,Or.inr (Or.inr (Or.inr rfl))⟩)).symm.trans (hu x),(e (show (x,0)∈ B from ⟨⟨hx,z0⟩,Or.inr (Or.inr (Or.inl rfl))⟩)).symm.trans (hv x), by rw [←e (show (1,x)∈B from ⟨⟨z1,hx⟩,Or.inr (Or.inl rfl)⟩),h1 x]; exact hs _⟩

structure Scene (i:Fin 5) where
 A: ℝ→ E
 moved : ContDiff ℝ ∞ (fund ∘ A)
 sewn0 : A 0=1
 sewn1 : A 1=locus i
 line : Sq→ Op Sheet
 path : Extension.Mar.Suit Window line
 unit : ∀ x∈Window,inK (line x)
 zeroT : ∀ x∈Zone, line (0,x)=1
 oneT : ∀ x∈Zone,line (x,1)=1
 turn : ∀ x∈Zone,line (x,0)=species (A x)
 seat : ∀ x∈Zone,mold (line (1,x)) living=(gamma i).seat (1-x)
 quiet : i=0 → A=(fun _=>1) ∧ line=(fun _=>1)
lemma sceneX (i:Fin 5) : Nonempty (Scene i) := by
 by_cases p:i=0
 · subst i; refine ⟨⟨fun _=>1,contDiff_const,rfl,symm ?_,fun _=>1,fun _ _=>contDiffAt_const,fun _ _=>kingOne,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>speciesOne.symm,fun x hx=>?_,fun _=> ⟨rfl,rfl⟩⟩⟩; simp [locus]; rw [mold_one,(gamma 0).stays] -- tune symm tactic
 obtain ⟨U,h,e,v,w⟩:= jumpU 1 (fund (locus i)) kingOne (forU ..); let A(t:ℝ):E:= ⟨⟨U t,(w t).1⟩,(w t).2⟩; let V:=fun x=>species (A x); have ha: A 0=1:= group.mat_injective (show U 0=1 from e); have hp:A 1=locus i:= group.mat_injective v; obtain ⟨W,H,P,u⟩:=squareT (U:=V) (curvesS.comp h) (by simp [V,ha]) (show V 1=Bz i from congrArg species hp) (fun _=> classK _)
 exact ⟨⟨A,h,ha,hp,W,H,P,fun x hx=>(u x hx).1,fun x hx=>(u x hx).2.1,fun x hx=> (u x hx).2.2.1,fun x hx=> (u x hx).2.2.2,fun x=>(p x).elim⟩⟩
def scene (i:Fin 5):=Classical.choice (sceneX i)
end YM.CF.BProof.Dream
