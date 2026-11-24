import YM.CF.Bloom.Kale
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
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0 k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Fossil V a p i N0 k₀ J q h wα R0 E C δ y)
variable (hy:y ≤ x)(U0: (l0:ℝ) ≤ x* plow x^k₀)(W0:Cape M B R.L)(Wp:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (W0 j) (apt M B R.L j) q)
structure Trait (L:Vestal M B R.L)(v:ℕ→ Haro.SpaceM)(Z:ℕ): Prop where -- D not guarantee all r>0 off valid j. wrap gives R0 positive? F.wrap on actual input with Stat guarantee R0 nonempty for one step, top index unconstrained choose partial use Op raw. adjust below
 wear (j:ℕ):Z≤j→ j<l0 →∀ V':Orbit (cell M B R.L j),Rue.FleetS (L j).p.threshold V'.1→ stove U (W0 j) (L (j+1)) (W0 (j+1)) (apt M B R.L j) (V.L.op (l0-1-j) (kint M B R.L j)) q J.d (v j).val V' = denZ (L j) U (W0 j) V'
 tip (j:ℕ): Z≤j→ j<l0→ ‖(v j)‖≤ R0 (hat R.L x j) -- fix
 owns(j:ℕ): Z≤ j→ j ≤ l0→ CloseC (hueR V a p i N0 T M ht l0 B0 j) (L j)
 note(j:ℕ): Z≤ j→j≤ l0→ Laurel (L j) K.j h (dleaf R.L (hat R.L x j)) (dleaf R.L (hat R.L x j)) R.L.val
 scent(j:ℕ):Z≤j→ j≤ l0→ |(L j).beta-B0 j|≤ ((l0-j:ℕ):ℝ) * rendK k₀ x
 shift(j:ℕ):Z≤j→ j< l0→ |((L (j+1)).beta - (B0 (j+1))) - ((L j).beta -B0 j)| ≤ δ (hat R.L x j)
 boot:L l0=hueR V a p i N0 T M ht l0 B0 l0
variable (hn:61≤ M.val)(hp:1 ≤ h)
include hn hp hy D D' U0 Wp
abbrev Ppath(F:ℝ→ℝ)(z:ℝ):=F z
private lemma manor(Z:ℕ)(qB: Z ≤ l0):∃ (X:Vestal M B R.L)(V':ℕ→Haro.SpaceM), Trait V a p i N0 T M ht l0 k₀ B0 J q h R0 δ W0 X V' (l0-Z):=by
 induction Z with
 |zero=>
    let V':ℕ→Haro.SpaceM:=fun _=>0; have hv:0 ≤ Lr (μh l0):=(D'.me _ (hy.trans (crown ..))).1.le
    refine ⟨Fh,V',⟨fun j p q=>by omega,fun j p q=>by omega,fun j p q=>⟨rfl,rfl,rfl,rfl⟩,fun j p' q=>?_ ,fun j p q=>?_,fun j p q=>by omega,rfl⟩⟩
    · have hp:j=l0:=by omega
      cases hp; exact baseY V a p i N0 T M ht l0 B0 h _ hv -- l0 subst
    have hz:j=l0:=by omega
    cases hz; change |B0 l0-B0 l0|≤_; simp
 |succ l ih=>
    obtain ⟨Lz,Vx,hV⟩:=ih (by omega); let j:=l0-(l+1)
    have hj:j< l0:=by unfold j; omega
    have eq: l0-l=j+1:=by unfold j; omega
    let N:= μh j; have hu:y≤N:=hy.trans (crown ..); let z:= Lz (j+1)
    have ht':Laurel z K.j h (dleaf R.L (μh (j+1))) (dleaf R.L (μh (j+1))) R.L.val:=hV.note (j+1) (by omega) hj
    have hP: y≤ μh (j+1):=hy.trans (crown ..); have hm: dleaf R.L (μh (j+1)) ≤ Lr N:= (D'.me N hu).2 _ (by unfold N hat; push_cast; linarith [pitch R.L]) |>.1
    let Tc:= V.L.op (l0-1-j) (kint M B R.L j); let G_:=apt M B R.L j; let x':=pay_K (Fh j) (z.beta+(B0 j-B0 (j+1)))
    let δβ:=hV.scent (j+1) (by omega) hj; have hg: matchedX (μh (j+1)) z.beta:= bond_β V a p i N0 T M ht l0 k₀ B0 D (j+1) (zero_lt_one.trans_le (D'.hu.trans hy)) (D'.buying.trans hy) hj U0 z.beta δβ -- signature
    let hc := sized_F (N:=mesh M R.L j) (P:=mesh M R.L (j+1)) (B:=B) (S:=Tc) (T:=V.L.mint (l0-1-j) (kint M B R.L j)) V a p i N0 T M ht l0 B0 D j z (hV.owns _ (by omega) hj) hj hg; let G:= (V.L.mint (l0-1-j) (kint M B R.L j))
    let hH:= ht'.lot_p hm hm; have hB': Girt.Ward z:=ward_m (show z.path.Bounds z.funds _ _ _ from by rw [hc.move,hc.coinY]; exact hc.hunt.up) hH
    obtain ⟨Db⟩:= rig V U W J q (Wp j) (W0 _) (Wp _).paid z hc.sound rfl hB'
    have ha: Tc.patch.L.val=R.L.val:=by unfold Tc; rw [V.L.patch_x]
    have hr:∃ v, Tact G_ Tc z h (Lr N) v:= ht'.drift_t ha (zero_le_one.trans hp) _ hm hc.down.hU hc.hunt.cert.size -- order
    have uB:60<(More (cell M B R.L j)).val:=by have ht:=hn.trans (amplit M B R.L j); change _< (cell M B R.L j).val*2; omega
    obtain ⟨l1,T',Q,Δ,v,hmT,hz,t,r0,β,hZ⟩:= (D'.step N hu Tc G_ G (W0 j) (W0 _) x' z (Wp j).paid (Wp _).paid (Wp _).pose Db hc (flat_v V a p i N0 T M ht j i) uB (ht'.vest _ _ _ hm hm (D'.me _ hu).1.le) hr (ht'.palm ha) ht'.ωact).goal
    let P:=spark_B x' T' Q Δ v; let V':=Function.update Lz j P; let M':=Function.update Vx j l1.val
    have hs:Laurel P K.j h (Lr N) (Lr N) R.L.val:=by
       refine ⟨?_ ,rfl,?_,t,r0⟩; · obtain ⟨I,v,x⟩:=hmT.weight; exact ⟨⟨I,v,fun i=> (x i).trans (D'.pay _ hu).1⟩, hmT.face⟩
       obtain ⟨I,v,x⟩:=hz.weight; exact ⟨⟨I,v,fun i=> (x i).trans (D'.pay _ hu).2⟩, hz.face⟩
    have hp': |P.beta-B0 j|≤ ((l0-j:ℕ):ℝ)*rendK k₀ x:=by
       have hh:0<plow x:= zero_lt_one.trans_le (Scales.size x); have hh': plow x≤ plow N:= (D'.me x hy).2 _ (crown ..)|>.2; have he:|Δ| ≤ rendK k₀ x:=by
          apply le_trans β; exact (le_abs_self _).trans ((D'.rise _ hu).trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hh _) (pow_le_pow_left₀ hh.le hh' _))) -- notation /
       change |z.beta+(B0 j-B0 (j+1))-Δ-B0 j| ≤_; rw [show z.beta+_ -Δ-B0 j=(z.beta-B0 (j+1))-Δ from (by ring)]; refine (abs_sub ..).trans ((add_le_add δβ he).trans_eq ?_); rw [show l0-j=l0-(j+1)+1 from (by omega)]; push_cast; ring
    have hh(i:ℕ)(v:i≠j): V' i=Lz i:=Function.update_of_ne v ..; have hh'(i:ℕ)(v:i≠j): M' i=Vx i:=Function.update_of_ne v ..; have he:V' j=P:=Function.update_self ..; have he':M' j=l1.val:=Function.update_self ..
    refine ⟨V',M',⟨fun i (pj : j ≤ i) v=>?_,fun i (pj : j ≤ i) v=>?_,fun i (pj : j ≤ i) v=>?_,fun i (pj : j ≤ i) v=>?_,fun i (pj : j ≤ i) v=>?_,fun i (pj : j ≤ i) v=>?_,(hh l0 hj.ne').trans hV.boot⟩⟩
    · rcases eq_or_ne i j with s|s; · subst i; rw [he,he',hh (j+1) (by omega)]; exact hZ
      rw [hh i s,hh (i+1) (by omega),hh' i s]; exact hV.wear i (by omega) v
    · obtain s|s:= eq_or_ne i j; · subst i; rw [he']; exact l1.property
      rw [hh' i s]; exact hV.tip i (by omega) v
    · rcases eq_or_ne i j with s|s; · subst i; rw [he]; exact ⟨rfl,rfl,rfl,rfl⟩
      rw [hh i s]; exact hV.owns i (by omega) v
    · rcases eq_or_ne i j with s|s; · subst i; rw [he]; exact hs
      rw [hh i s]; exact hV.note i (by omega) v
    · rcases eq_or_ne i j with s|s; · subst i; rw [he]; exact hp'
      rw [hh i s]; exact hV.scent i (by omega) v
    rcases eq_or_ne i j with s|s; · subst i; rw [he,hh (j+1) (by omega)]; change |(z.beta-B0 (j+1)) - ((z.beta + (B0 j-B0 (j+1))-Δ) - B0 j)| ≤ _; rw [show _-(_-B0 j)=Δ from ?_]; exact β; ring
    rw [hh i s,hh (i+1) (by omega)]; exact hV.shift i (by omega) v
lemma rune_t:∃ X V', Trait V a p i N0 T M ht l0 k₀ B0 J q h R0 δ W0 X V' 0:=by obtain ⟨X,Q,u⟩:=manor V a p i N0 T M ht l0 k₀ B0 D J q h R0 E C δ y D' hy U0 W0 Wp hn hp l0 le_rfl; exact ⟨X,Q,by simpa using u⟩ -- tune order!
end YM.CF.Py
