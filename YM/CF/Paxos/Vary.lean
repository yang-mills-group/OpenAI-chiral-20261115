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
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Heron V a p i N0 k₀ J q h wα R0 E C δ y)(hy:y ≤ x)
local notation "S'"=> StarPS l0
open Oise
variable (HR:∀ j,0 ≤ R0 (hat R.L x j))(W0:Cape M B R.L)(Wp:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (W0 j) (apt M B R.L j) q)
local notation "Vq"=> θ_guess (l0:=l0) (fun i=>R0 (μh i)) HR
abbrev Rowt (A:∀ j:ℕ,StarPS l0→ RegBudget (cell M B R.L j))(Q:∀ j:ℕ,StarPS l0→ ForceBudget (cell M B R.L j))(v:ℕ→StarPS l0→ ℂ)(z:StarPS l0)(j:ℕ):GramM (cell M B R.L j):= color_b (hueR V a p i N0 T M ht l0 B0 j) (tempo_b R.L B0 z j) (A j z) 0 (Q j z) (v j z)
local notation "Yr"=> Rowt V a p i N0 T M ht l0 B0
structure Treble (A:∀ j:ℕ,StarPS l0→ RegBudget (cell M B R.L j))(Q:∀ j:ℕ,StarPS l0→ ForceBudget (cell M B R.L j))(v:ℕ→StarPS l0→ ℂ)(X:∀ j:ℕ,StarPS l0→ Haro.ΘS (R0 (hat R.L x j)))(D:ℕ→StarPS l0→ℝ) (ψ:ℕ→ℝ) (k:ℕ):Prop where
 wear (j:ℕ):k≤j→ j<l0→∀ c:StarPS l0,θ_guess (fun j=>R0 (hat R.L x j)) HR j c=X j c → D j c=ra_C R.L c j→∀ V':Orbit (cell M B R.L j),Rue.FleetS ((Rowt V a p i N0 T M ht l0 B0 A Q v c j).p.threshold) V'.1 → stove U (W0 j) (Rowt V a p i N0 T M ht l0 B0 A Q v c (j+1)) (W0 (j+1)) (apt M B R.L j) (V.L.op (l0-1-j) (kint M B R.L j)) q J.d (Haro.riseV (X j c)) V'=denZ (Rowt V a p i N0 T M ht l0 B0 A Q v c j) U (W0 j) V'
 fee(j:ℕ): k≤j→ j<l0→∀ z, |D j z|≤ δ (hat R.L x j)
 paid(j:ℕ): k≤j → j≤ l0→∀ z,Laurel (Rowt V a p i N0 T M ht l0 B0 A Q v z j) K.j h (dleaf R.L (hat R.L x j)) (dleaf R.L (hat R.L x j)) R.L.val
 keep(j:ℕ): Beau.LampF (A j)
 stay(j:ℕ):∀ i:Force (cell M B R.L j),∀ v,Continuous fun z=>Q j z i v
 contW(j:ℕ): Continuous (X j)
 contD(j:ℕ):Continuous (D j)
 cash:(A l0)=0
 past:(Q l0)=0
 heat:v l0=0
 good(j:ℕ): k≤j→ j<l0→∀ c:StarPS l0,θ_guess (fun j=>R0 (hat R.L x j)) HR j c=X j c → ‖Complex.exp (v (j+1) c)‖*ψ j ≤ ‖Complex.exp (v j c)‖
variable (hp:1 ≤ h)(hn:61≤ M.val)
include hn hp Wp D D' hy HR
set_option maxHeartbeats 2500000 in
private lemma lope_K(l:ℕ)(h0:l ≤ l0) :∃ A Q v Y D, Treble V a p i N0 T M ht l0 B0 J q h R0 δ HR W0 A Q v Y D (Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy) (l0-l):=by -- replace h
 induction l with
 |zero=>
    refine ⟨0,0,0,Vq,0,⟨(fun i p q=>by omega),(fun i p q=>by omega),?_,fun i x y=>continuous_const,fun i j w=>continuous_const,fun i=>ts_θ ..,fun i=>continuous_const,rfl,rfl,rfl,(fun i p q=>by omega)⟩⟩ -- pi type.Motive ht
    intro j v k c; have hz:j=l0:=by omega
    subst j; have he:= baseY V a p i N0 T M ht l0 B0 h K.j ((D'.me _ (hy.trans (crown R.L x l0))).1.le)
    exact ⟨he.buoy,rfl,he.nite,he.dawn,he.warp⟩
 |succ l ih=>
    obtain ⟨A,X,w,Y,U',hV⟩:= ih (by omega); let j:= l0-(l+1)
    have hj:j<l0:=by unfold j; omega
    have eq:l0-l=j+1:=by unfold j; omega
    haveI :Nonempty S':=⟨⟨0,by rw [norm_zero]; exact zero_le_one⟩⟩
    let t:= μh j; let c0:=Classical.arbitrary S'; have hu:y≤t:=hy.trans (crown ..)
    let N:=cell M B R.L j; let P:=cell M B R.L (j+1); let G_:=apt M B R.L j
    let Tc:=V.L.op (l0-1-j) (kint M B R.L j); let Tk:=V.L.mint (l0-1-j) (kint M B R.L j)
    let Ω(c):=Yr A X w c (j+1); let bu(c:S'):=tempo_b R.L B0 c (j+1); let Rz(c):= pay_K (Fh j) (bu c+(B0 j-B0 (j+1))); let Lr':= V.L.charge (l0-1-j); let Jp:= (W.arm (T.large.trans ht) l0).shift j
    have hc(c:S'):StatV V G_ Tk U W (Rz c) (Ω c) Lr' Jp a t p i:= sized_F (N:=mesh M R.L j) (P:=mesh M R.L (j+1)) (B:=B) (S:=Tc) (T:=Tk) V a p i N0 T M ht l0 B0 D j (Ω c) (show CloseC (Fh (j+1)) (Ω c) from ⟨rfl,rfl,rfl,rfl⟩) hj (mood_a V a p i N0 T M ht k₀ B0 D J q h R0 E C δ y D' hy c _ (by omega)) -- l0 implicit
    let Xc'(c):= color_b (Rz c0) (bu c+(Lr'+Jp)) 0 0 0 0; let Vc(c):= color_b (Ω c0) (bu c) (A (j+1) c) 0 (X (j+1) c) (w (j+1) c)
    have hjp:B0 j-B0 (j+1)=Lr'+Jp:=add_left_cancel (show bu c0+(B0 j-B0 (j+1))=bu c0+(Lr'+Jp) from (hc c0).coat)
    have hRz(c):Xc' c= Rz c:=by unfold Xc' Rz; rw [←hjp]
    have hv(c):Vc c=Ω c:=rfl
    have hm: dleaf R.L (μh (j+1)) ≤ Lr t:= (D'.me t hu).2 _ (by unfold t hat; push_cast; linarith [pitch R.L])|>.1
    have ht'(c):Laurel (Ω c) K.j h (dleaf R.L (μh (j+1))) (dleaf R.L (μh (j+1))) R.L.val:=hV.paid _ (by omega) (by omega) c
    let Ks(c): Girt.BaseL U G_ (Ω c) (W0 j) (W0 (j+1)) q J.d:= Classical.choice (rig V U W J q (Wp j) (W0 _) (Wp _).paid (Ω c) (hc c).sound rfl (ward_m (show (Ω c).path.Bounds (Ω c).funds _ _ _ from by rw [(hc c).move,(hc c).coinY]; exact (hc c).hunt.up) ((ht' c).lot_p hm hm)))
    have ha:Tc.patch.L.val=R.L.val:=by unfold Tc; rw [V.L.patch_x]
    have hr(c):∃ v,Tact G_ Tc (Ω c) h (Lr t) v:= (ht' c).drift_t ha (zero_le_one.trans hp) _ hm (hc c).down.hU (hc c).hunt.cert.size
    have uB:60<(More N).val:=by have ht:= hn.trans (amplit M B R.L j); change _< (cell M B R.L j).val*2; omega
    obtain ⟨Xs,TX,XQ,vQ,Dt,pC,pV,p1,p2,p3⟩:= (Classical.choose_spec (D'.step t hu Tc G_)).2 Tk (W0 j) (W0 _) (Rz c0) (Ω c0) (Wp j).paid (Wp _).paid (Wp _).pose (Ks c0) (hc c0) (flat_v V a p i N0 T M ht j i) uB S' bu (A (j+1)) 0 (X (j+1)) (w (j+1)) (Vq j) (mood_c _ _ _) (fun x y _=>hV.keep _ _ _) (fun i y _=>continuous_const) (fun i j _=>hV.stay ..) (ts_θ ..) Ks (fun c=>show StatV V G_ Tk U W (Xc' c) (Ω c) Lr' Jp a t p i from (hRz c) ▸ hc c) (fun c=>(ht' c).vest _ _ _ hm hm (D'.me _ hu).1.le) hr (fun c=> (ht' c).palm ha) (fun c=> (ht' c).ωact)
    let A':=Function.update A j TX; let Q':=Function.update X j XQ; let w':=Function.update w j vQ; let X':= Function.update Y j Xs; let Dψ:=Function.update U' j Dt
    have hh(u:ℕ)(q:u≠j)(c):Yr A' Q' w' c u=Yr A X w c u:=by unfold Rowt A' Q' w'; rw [Function.update_of_ne q,Function.update_of_ne q,Function.update_of_ne q]
    have hg(u:ℕ)(q:u≠ j):X' u=Y u:=Function.update_of_ne q ..; have hz(c):Yr A' Q' w' c j=color_b (Xc' c) (tempo_b R.L B0 c j) (TX c) 0 (XQ c) (vQ c):=by unfold Rowt A' Q' w'; rw [Function.update_self,Function.update_self,Function.update_self]
    have hxq:X' j=Xs:=Function.update_self ..; have htD:Dψ j=Dt:=Function.update_self ..
    refine ⟨A',Q',w',X',Dψ,⟨?_,?_,?_,?_,?_,?_,?_,(Function.update_of_ne hj.ne' ..).trans hV.cash,(Function.update_of_ne hj.ne' ..).trans hV.past,(Function.update_of_ne hj.ne' ..).trans hV.heat,?_⟩⟩
    · intro i (p : j ≤ i) h c; rcases eq_or_ne i j with p'|p'
      · subst i; intro q' z; rw [hxq] at q' ⊢; rw [htD] at z; rw [hh (j+1) (by omega),hz]; have he:tempo_b R.L B0 c j=(Xc' c).beta - Dt c:=by
           change _=bu c+_ - Dt c; unfold bu; rw [mood_z, z, ←hjp]; ring
        rw [he]; rw [←q']; exact (p3 c).zF q'
      rw [hh _ p',hg _ p', show Dψ i = U' i from Function.update_of_ne p' .., hh (i+1) (by omega)]
      exact hV.wear i (by omega) h c
    · intro i (p:j ≤ i) h c; rcases eq_or_ne i j with p'|p'; subst i; rw [htD]; exact (p3 c).zN
      rw [show Dψ i =U' i from Function.update_of_ne p' ..]; exact hV.fee i (by omega) h c
    · intro i (p: j ≤ i) z c; rcases eq_or_ne i j with p'|p'; swap; · rw [hh _ p']; exact hV.paid i (by omega) z c
      subst i; rw [hz]; obtain ⟨p,zP,g1,Nt,-,-,-⟩:=p3 c; refine ⟨?_,rfl,?_,g1,Nt⟩
      · obtain ⟨s,x,w⟩:=p.weight; exact ⟨⟨s,x,fun i=>(w i).trans (D'.pay _ hu).1⟩, p.face⟩
      obtain ⟨s,x,w⟩:=zP.weight; exact ⟨⟨s,x,fun i=>(w i).trans (D'.pay _ hu).2⟩,zP.face⟩
    · intro i; by_cases p:i=j; subst i; exact (show A' j=TX from Function.update_self ..) ▸ p1; rw [show A' i=A i from Function.update_of_ne p ..]; exact hV.keep i
    · intro i; by_cases p:i=j; subst i; rw [show Q' j=XQ from Function.update_self ..]; exact p2; rw [show Q' i=X i from Function.update_of_ne p ..]; exact hV.stay i
    · intro i; by_cases p:i=j; subst i; rw [hxq]; exact pC; rw [hg i p]; exact hV.contW i
    · intro i; by_cases p:i=j; subst i; rw [htD]; exact pV; rw [show Dψ i = U' i from Function.update_of_ne p ..]; exact hV.contD i
    have hf:(Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy) j=Classical.choose (D'.step t hu Tc G_):= swap_hrt ..
    intro i (pti: j ≤ i) v c; obtain s|s:= eq_or_ne i j
    · subst i; rw [hxq,show w' j = vQ from Function.update_self ..,show w' (j+1)=w (j+1) from Function.update_of_ne (by omega) ..]; intro p_V; rw [hf]; exact (p3 c).yF p_V -- syntax h shadow
    rw [hg i s,show w' i =w i from Function.update_of_ne s ..,show w' (i+1)=w (i+1) from Function.update_of_ne (by omega) ..]; exact hV.good i (by omega) v c
lemma able_c:∃ A Q v Y D,Treble V a p i N0 T M ht l0 B0 J q h R0 δ HR W0 A Q v Y D (Hertz V a p i N0 M k₀ J q h R0 E C δ y D' hy) 0:=by obtain ⟨A,Q,v,Y,D,t⟩:= lope_K V a p i N0 T M ht l0 k₀ B0 D J q h R0 E C δ y D' hy HR W0 Wp hp hn l0 le_rfl; exact ⟨A,Q,v,Y,D,Nat.sub_self l0 ▸ t⟩
end YM.CF.Py
