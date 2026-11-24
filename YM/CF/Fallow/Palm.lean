import YM.CF.Tar.Rein
import YM.CF.Fallow.Sora
import YM.CF.Tar.Silt
import YM.CF.Paxos.Seed
set_option autoImplicit false

set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(nK B1:ℕ)(k₀:ℕ)
local notation "NK"=> trunkY nK B1
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht (trunkY nK B1) B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht (trunkY nK B1) B0
local notation "μh"=> hat R.L x
variable (φ:ℝ→ℝ)(T_:ArmorK)(Λp:Stock_V){Zζ Wκ VΦ KΦ:ℝ→ℝ}
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Loom_K V a p i N0 k₀ J q h T_ φ Zζ Wκ VΦ KΦ wα R0 E C δ y)(hy:y ≤ x)
variable (V0 Jx:ℕ→ℝ)(Fp:ℝ→ℝ)(Hμ:SnapPS V a p i N0 M k₀ J q h φ T_ Λp δ R0 E C y D' hy Fp nK B1 Jx V0)
local notation "S'"=> StarPS NK
open Oise
variable (W0:Cape M B R.L)(Wp:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (W0 j) (apt M B R.L j) q)
local notation "HR"=> (fun i=>(Hμ.rateB i).le)
local notation "Vq"=> θ_guess (l0:=trunkY nK B1) Jx (fun i=>(Hμ.rateB i).le)
local notation "Ωs"=> fun j:ℕ=> wage_B nK B1 j R.L x
variable (Ue: RegBudget (cell M B R.L (trunkY nK B1)))(sE:ℂ) (pS:∀ b:ℝ,Provides R.L K.j (color_b (hueR V a p i N0 T M ht (trunkY nK B1) B0 (trunkY nK B1)) b Ue 0 0 sE) h (V0 (trunkY nK B1)) (zone_F (trunkY nK B1) (post_H nK)))
local notation "Yr"=> Hymn_v V a p i N0 T M ht nK B1 B0
structure TrailΞ (A:∀ j:ℕ,StarPS (trunkY nK B1)→ RegBudget (cell M B R.L j))(Q:∀ j:ℕ,StarPS (trunkY nK B1)→ ForceBudget (cell M B R.L j))(v:ℕ→StarPS (trunkY nK B1)→ ℂ)(X:∀ j:ℕ,StarPS (trunkY nK B1)→ Haro.ΘS (Jx j))(D:ℕ→StarPS (trunkY nK B1)→ℝ) (ψ:ℕ→ℝ) (k:ℕ):Prop where
 wear (j:ℕ):k≤j→ j<(trunkY nK B1)→∀ c:StarPS (trunkY nK B1),θ_guess Jx (fun i=>(Hμ.rateB i).le) j c=X j c → D j c=guess_Q _ (Ωs) c j→∀ V':Orbit (cell M B R.L j),Rue.FleetS ((Hymn_v V a p i N0 T M ht nK B1 B0 A Q v c j).p.threshold) V'.1 → stove U (W0 j) (Hymn_v V a p i N0 T M ht nK B1 B0 A Q v c (j+1)) (W0 (j+1)) (apt M B R.L j) (V.L.op ((trunkY nK B1)-1-j) (kint M B R.L j)) q J.d (Haro.riseV (X j c)) V'=denZ (Hymn_v V a p i N0 T M ht nK B1 B0 A Q v c j) U (W0 j) V'
 score (j:ℕ):k≤j→ j<(trunkY nK B1)→∀ c:StarPS (trunkY nK B1),θ_guess Jx (fun i=>(Hμ.rateB i).le) j c=X j c → D j c=guess_Q _ (Ωs) c j→ Prism_Φ V U (V.L.op ((trunkY nK B1)-1-j) (kint M B R.L j)) (apt M B R.L j) (W0 j) (W0 (j+1)) (Hymn_v V a p i N0 T M ht nK B1 B0 A Q v c j) (Hymn_v V a p i N0 T M ht nK B1 B0 A Q v c (j+1)) (Haro.riseV (X j c)) q J.d h (hat R.L x j) T_ φ Λp
 fee(j:ℕ): k≤j→ j<(trunkY nK B1)→∀ z, |D j z|≤ mode_D nK j R.L x δ
 paid(j:ℕ): k≤j → j≤ (trunkY nK B1)→∀ z,Provides R.L K.j (Hymn_v V a p i N0 T M ht nK B1 B0 A Q v z j) h (V0 j) (zone_F j (post_H nK))
 keep(j:ℕ): Beau.LampF (A j)
 stay(j:ℕ):∀ i:Force (cell M B R.L j),∀ v,Continuous fun z=>Q j z i v
 contW(j:ℕ): Continuous (X j)
 contD(j:ℕ):Continuous (D j)
 cash:A (trunkY nK B1)=fun _=> Ue
 past:(Q (trunkY nK B1))=0
 heat:v (trunkY nK B1)= fun _=>sE
 good(j:ℕ): k≤j→ j<(trunkY nK B1)→∀ c:StarPS (trunkY nK B1),θ_guess Jx (fun i=>(Hμ.rateB i).le) j c=X j c → ‖Complex.exp (v (j+1) c)‖*ψ j ≤ ‖Complex.exp (v j c)‖
variable (hp:1 ≤ h)(hn:61≤ M.val)
include hn hp Wp D Hμ pS
set_option maxHeartbeats 2500000 in
lemma leap_E(l:ℕ)(h0:l ≤ (trunkY nK B1)) :∃ A Q v Y D, TrailΞ V a p i N0 T M ht nK B1 k₀ B0 J q h φ T_ Λp R0 E C δ y D' hy V0 Jx Fp Hμ W0 Ue sE A Q v Y D (fun j=> tide_W nK j (Θpane V a p i N0 M k₀ J q h φ T_ R0 E C δ y D' hy)) ((trunkY nK B1)-l):=by -- replace h
 induction l with
 |zero=>
    let A : ∀ j, S' →RegBudget (cell M B R.L j) := Function.update 0 NK (fun _=>Ue); let Z : ℕ→S'→ℂ:=fun i z=>sE
    have htA:A (trunkY nK B1)=fun _=>Ue:=Function.update_self ..
    refine ⟨A,0,Z,(Vq),0,⟨(fun i p q=>by omega),(fun i p q=>by omega),(fun i p q=>by omega),?_,?_,fun i j w=>continuous_const,fun i=>ts_θ ..,fun i=>continuous_const,htA,rfl,rfl,(fun i p q=>by omega)⟩⟩
    · intro j v l c; have hz:j=(trunkY nK B1):=by omega
      subst j; unfold Hymn_v; rw [htA]; exact pS _
    intro i; by_cases h:i=trunkY nK B1; subst i; rw [htA]; exact fun i j=>continuous_const
    rw [show A i= _ from Function.update_of_ne h (f:=(0:∀ j,S' →RegBudget (cell M B R.L j))) _]; exact fun i j=>continuous_const
 |succ l ih=>
    obtain ⟨A,X,w,Y,U',hV⟩:= ih (by omega); let j:= (trunkY nK B1)-(l+1)
    have hj:j<(trunkY nK B1):=by unfold j; omega
    have eq:(trunkY nK B1)-l=j+1:=by unfold j; omega
    haveI :Nonempty S':=⟨⟨0,by rw [norm_zero]; exact zero_le_one⟩⟩
    let t:= μh j; let c0:=Classical.arbitrary S'; have hu:y≤t:=hy.trans (crown ..)
    let N:=cell M B R.L j; let P:=cell M B R.L (j+1); let G_:=apt M B R.L j
    let Tc:=V.L.op ((trunkY nK B1)-1-j) (kint M B R.L j); let Tk:=V.L.mint ((trunkY nK B1)-1-j) (kint M B R.L j)
    let Ω(c):=Yr A X w c (j+1); let bu(c:S'):=tempo_v _ B0 (Ωs) c (j+1); let Rz(c):= pay_K (Fh j) (bu c+(B0 j-B0 (j+1))); let Lr':= V.L.charge ((trunkY nK B1)-1-j); let Jp:= (W.arm (T.large.trans ht) (trunkY nK B1)).shift j
    have hc(c:S'):StatV V G_ Tk U W (Rz c) (Ω c) Lr' Jp a t p i:= sized_F (N:=mesh M R.L j) (P:=mesh M R.L (j+1)) (B:=B) (S:=Tc) (T:=Tk) V a p i N0 T M ht (trunkY nK B1) B0 D j (Ω c) (show CloseC (Fh (j+1)) (Ω c) from ⟨rfl,rfl,rfl,rfl⟩) hj (tilt_rΦ V a p i N0 T M ht k₀ B0 J q h φ T_ Λp δ R0 E C y D' hy Hμ D c _ (by omega)) -- (trunkY nK B1) implicit
    let Xc'(c):= color_b (Rz c0) (bu c+(Lr'+Jp)) 0 0 0 0; let Vc(c):= color_b (Ω c0) (bu c) (A (j+1) c) 0 (X (j+1) c) (w (j+1) c)
    have hjp:B0 j-B0 (j+1)=Lr'+Jp:=add_left_cancel (show bu c0+(B0 j-B0 (j+1))=bu c0+(Lr'+Jp) from (hc c0).coat)
    have hRz(c):Xc' c= Rz c:=by unfold Xc' Rz; rw [←hjp]
    have hv(c):Vc c=Ω c:=rfl
    have ht'(c):Provides R.L K.j (Ω c) h (V0 (j+1)) (zone_F (j+1) (post_H nK)):=hV.paid _ (by omega) (by omega) c
    let Ks(c): Girt.BaseL U G_ (Ω c) (W0 j) (W0 (j+1)) q J.d:= Classical.choice (rig V U W J q (Wp j) (W0 _) (Wp _).paid (Ω c) (hc c).sound rfl (ward_m (show (Ω c).path.Bounds (Ω c).funds _ _ _ from by rw [(hc c).move,(hc c).coinY]; exact (hc c).hunt.up) (ht' c).lot))
    have ha:Tc.patch.L.val=R.L.val:=by unfold Tc; rw [V.L.patch_x]
    have uB:60<(More N).val:=by have ht:= hn.trans (amplit M B R.L j); change _< (cell M B R.L j).val*2; omega
    obtain ⟨Xs,TX,XQ,vQ,Dt,pC,pV,p1,p2,p3⟩:= (Hμ.step j hj).step Tk (W0 j) (W0 _) (Rz c0) (Ω c0) (Wp j).paid (Wp _).paid (Wp _).pose (Ks c0) (Subtype.ext ha) rfl (hc c0) (flat_v V a p i N0 T M ht j i) uB S' bu (A (j+1)) 0 (X (j+1)) (w (j+1)) (Vq j) (tilt_Qc _ _ _ _) (fun x y _=>hV.keep _ _ _) (fun i y _=>continuous_const) (fun i j _=>hV.stay ..) (ts_θ ..) Ks (fun c=>show StatV V G_ Tk U W (Xc' c) (Ω c) Lr' Jp a t p i from (hRz c) ▸ hc c) ht'
    let A':=Function.update A j TX; let Q':=Function.update X j XQ; let w':=Function.update w j vQ; let X':= Function.update Y j Xs; let Dψ:=Function.update U' j Dt
    have hh(u:ℕ)(q:u≠j)(c):Yr A' Q' w' c u=Yr A X w c u:=by unfold Hymn_v A' Q' w'; rw [Function.update_of_ne q,Function.update_of_ne q,Function.update_of_ne q]
    have hg(u:ℕ)(q:u≠ j):X' u=Y u:=Function.update_of_ne q ..; have hz(c):Yr A' Q' w' c j=color_b (Xc' c) (tempo_v _ B0 (Ωs) c j) (TX c) 0 (XQ c) (vQ c):=by unfold Hymn_v A' Q' w'; rw [Function.update_self,Function.update_self,Function.update_self]
    have hxq:X' j=Xs:=Function.update_self ..; have htD:Dψ j=Dt:=Function.update_self ..
    refine ⟨A',Q',w',X',Dψ,⟨?_,?_,?_,?_,?_,?_,?_,?_,(Function.update_of_ne hj.ne' ..).trans hV.cash,(Function.update_of_ne hj.ne' ..).trans hV.past,(Function.update_of_ne hj.ne' ..).trans hV.heat,?_⟩⟩
    · intro i (p : j ≤ i) h c; rcases eq_or_ne i j with p'|p'
      · subst i; intro q' z; rw [hxq] at q' ⊢; rw [htD] at z; rw [hh (j+1) (by omega),hz]; have he:tempo_v _ B0 (Ωs) c j=(Xc' c).beta - Dt c:=by
           change _=bu c+_ - Dt c; unfold bu; rw [boom_z, z, ←hjp]; ring
        rw [he]; exact ((p3 c).2.2 q').1
      rw [hh _ p',hg _ p', show Dψ i = U' i from Function.update_of_ne p' .., hh (i+1) (by omega)]
      exact hV.wear i (by omega) h c
    · intro i (p : j ≤ i) h c; rcases eq_or_ne i j with p'|p'
      · subst i; intro q' z; rw [hxq] at q' ⊢; rw [htD] at z; rw [hh (j+1) (by omega),hz]; have he:tempo_v _ B0 (Ωs) c j=(Xc' c).beta - Dt c:=by
           change _=bu c+_ - Dt c; unfold bu; rw [boom_z, z, ←hjp]; ring
        rw [he]; exact ((p3 c).2.2 q').2.2 (hero_P (N:=mesh M R.L j) (P:=mesh M R.L (j+1)) V _ _)
      rw [hh _ p',hg _ p', show Dψ i = U' i from Function.update_of_ne p' .., hh (i+1) (by omega)]
      exact hV.score i (by omega) h c
    · intro i (p:j ≤ i) h c; rcases eq_or_ne i j with p'|p'; subst i; rw [htD]; exact (p3 c).2.1
      rw [show Dψ i =U' i from Function.update_of_ne p' ..]; exact hV.fee i (by omega) h c
    · intro i (p: j ≤ i) z c; rcases eq_or_ne i j with p'|p'; swap; · rw [hh _ p']; exact hV.paid i (by omega) z c
      subst i; rw [hz]; exact Provides.tone_v _ _ _ _ _ _ (p3 c).1 -- note args e b t
    · intro i; by_cases p:i=j; subst i; exact (show A' j=TX from Function.update_self ..) ▸ p1; rw [show A' i=A i from Function.update_of_ne p ..]; exact hV.keep i
    · intro i; by_cases p:i=j; subst i; rw [show Q' j=XQ from Function.update_self ..]; exact p2; rw [show Q' i=X i from Function.update_of_ne p ..]; exact hV.stay i
    · intro i; by_cases p:i=j; subst i; rw [hxq]; exact pC; rw [hg i p]; exact hV.contW i
    · intro i; by_cases p:i=j; subst i; rw [htD]; exact pV; rw [show Dψ i = U' i from Function.update_of_ne p ..]; exact hV.contD i
    intro i (pti: j ≤ i) v c; obtain s|s:= eq_or_ne i j
    · subst i; rw [hxq,show w' j = vQ from Function.update_self ..,show w' (j+1)=w (j+1) from Function.update_of_ne (by omega) ..]; intro p_V; exact ((p3 c).2.2 p_V).2.1 -- syntax h shadow
    rw [hg i s,show w' i =w i from Function.update_of_ne s ..,show w' (i+1)=w (i+1) from Function.update_of_ne (by omega) ..]; exact hV.good i (by omega) v c
end YM.CF.Py
