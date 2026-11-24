import YM.CF.Py.Chime
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
variable{B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a α:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W) (M:Side)(ht:T.q ≤ M.val)(l0:ℕ)
local notation "L'"=>R.L
-- RocketV requires for any M period, needs arbitrary Final multiplicity from Robes.Ro.M (M above actually N*m.L). pass final Side extra.
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
abbrev Vestal(M B L:Side):=(i:ℕ)→ GramM (cell M B L i)
abbrev Cape(M B L:Side):=(i:ℕ)→ Scree.Loom (cell M B L i)
variable (f g B0:ℕ→ℝ)(F G':ℕ→ℝ→ℝ)(Lx: Cape M B R.L)
variable (D: Due V a p i N0 T M ht l0 B0)
structure Flourish (L:Vestal M B R.L)(A':ℕ):Prop where
 wear(j:ℕ) : j < l0 → A' ≤j →∀ u:Orbit (cell M B R.L j),Rue.FleetS (L j).p.threshold u.1 →Scree.stove U (Lx j) (L (j+1)) (Lx (j+1)) (apt M B R.L j) (V.L.op (l0-1-j) (kint M B R.L j)) q J.d 0 u=denZ (L j) U (Lx j) u
 owns(j:ℕ): j ≤ l0 → A' ≤ j→ Costume (hueR V a p i N0 T M ht l0 B0 j) (L j)
 costP (j:ℕ): j≤ l0→ A'≤j→ LotR (L j) h (F j (hat R.L x j)) (G' j (hat R.L x j))
 top:L l0=hueR V a p i N0 T M ht l0 B0 l0
variable (Ta: Warm V U W N0 J.n i p q J.k J.d J.roomX a h)(Z:Valley V q J a h N0 p Ta l0 F G') (hB:∀ i',i'<l0→BillStep V q J a (F (i'+1)) (G' (i'+1)) (F i') (G' i') (hat R.L x i') h p i N0)
variable (v_R:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (Lx j) (apt M B R.L j) q)
local notation "Ξr"=> hueR V a p i N0 T M ht l0 B0
include D Z hB v_R
private lemma vill(j:ℕ)(t:j ≤l0): ∃ V': Vestal M B R.L, Flourish V a p i N0 T M ht l0 J q h B0 F G' Lx V' (l0-j):=by
 induction j with
 | zero=>
    refine ⟨(hueR V a p i N0 T M ht l0 B0),⟨fun j u h=>by omega,fun j p u=>?_,fun j p u=> ?_,rfl⟩⟩
    · exact ⟨0,0,0,rfl⟩ -- Exists structure tune
    have he:j=l0:=by omega
    subst j; rw [Z.top,Z.knot]; refine ⟨(Vale.lye ..).1,rfl,(Vale.lye ..).2⟩
 | succ j ih=>
    obtain ⟨K,X'⟩:=ih (by omega); let Y:=l0-(j+1); have he:Y<l0:=by unfold Y; omega
    have hh:l0-j=Y+1 ∧ i=i:=by unfold Y; omega
    let B_:= V.L.mint (l0-1-Y) (kint M B R.L Y); have ha:= sized_s V a p i N0 T M ht l0 B0 D Y (K (Y+1)) (X'.owns (Y+1) he (by omega)) he -- issue j+1≤
    let P' := X'.costP (Y+1) he (by omega); rw [hat_succ] at P';
    obtain ⟨E,C,v,u,i2,T'⟩:= ((hB Y he).ride B_ _ _ _ _ ha (flat_v V a p i N0 T M ht Y i) (v_R Y) (v_R _).paid P').earns
    let f:= PoleR (hueR V a p i N0 T M ht l0 B0 Y) E C v; let L:= Function.update K Y f
    have U'(j)(p:j ≠ Y):L j=K j:=Function.update_of_ne p _ _
    have h0:L Y=f:=Function.update_self ..
    refine ⟨L,fun j u v=> ?_, fun j p v=>?_ ,fun j p q=>?_ ,(U' l0 he.ne').trans X'.top⟩
    · by_cases h:j=Y
      · subst j; rw [h0,U' (Y+1) (by omega)]; exact T'
      rw [U' _ h,U' (j+1) (by change Y ≤ j at v; omega)]; exact X'.wear _ u (by change Y≤ j at v; omega)
    · by_cases p':j=Y; · subst j; rw [h0]; exact ⟨E,C,_,rfl⟩
      rw [U' _ p']; exact X'.owns _ p (by change Y≤j at v; omega)
    by_cases p':j=Y; · subst j; rw [h0]; exact ⟨u,rfl,i2⟩
    rw [U' _ p']; exact X'.costP _ p (by change Y≤ j at q; omega)
lemma plan_u: ∃ V':Vestal M B R.L,Flourish V a p i N0 T M ht l0 J q h B0 F G' Lx V' 0:=by obtain ⟨V',e⟩:=vill V a p i N0 T M ht l0 J q h B0 F G' Lx D Ta Z hB v_R l0 le_rfl; exact ⟨V',by simpa using e⟩ -- order D...
omit Z hB
variable (Q: Vestal M B R.L)(Pκ:Flourish V a p i N0 T M ht l0 J q h B0 F G' Lx Q 0)(vI:∀ i,Rue.IsleB SU.group (T.a i).threshold)
include vI Pκ
lemma sales (p':j<l0) :partitionZ (Q j) U (Lx j)=partitionZ (Q (j+1)) U (Lx (j+1)):=by
 let H:= (Pκ.costP (j+1) p' (Nat.zero_le _)); let R_:=(v_R (j+1)).paid
 have he:= sized_s V a p i N0 T M ht l0 B0 D j (Q (j+1)) (Pκ.owns (j+1) p' (Nat.zero_le _)) p'
 let U':= V.L.mint (l0-1-j) (kint M B R.L j); have hh: Girt.Ward (Q (j+1)):= ward_m (show (Q (j+1)).path.Bounds (Q (j+1)).funds _ _ _ from by rw [he.move,he.coinY]; exact he.hunt.up) H
 obtain ⟨D⟩:= rig V U W J q (v_R j) (Lx _) R_ (Q _) he.sound rfl hh
 let S':= V.L.op (l0-1-j) (kint M B R.L j); have hz:S'.patch.Branches S'.kernel SU.group:=by rw [V.L.patch_x]; exact V.L.cloth
 refine balanceBa D he.hunt.scaleP hz ?_ (Pκ.wear _ p' (Nat.zero_le _))
 obtain ⟨E,A,b,hp⟩:= (Pκ.owns _ p'.le (Nat.zero_le _)).reset; rw [hp]; exact vI _
lemma braidL(j:ℕ)(hp:j≤l0): partitionZ (Q j) U (Lx j)=partitionZ (Q l0) U (Lx l0):=by
 have he(i h:ℕ)(p:i ≤ h)(u:h≤l0): partitionZ (Q i) U (Lx i)=partitionZ (Q h) U (Lx h):=by
    induction h with| zero=>rw [show i=0 by omega]|succ h ih=>rcases p.eq_or_lt with ht|hc; rw [ht]; exact (ih (by omega) (by omega)).trans (sales V a _ _ N0 T M ht l0 J q _ B0 F G' Lx D v_R Q Pκ vI (show h<l0 from by omega)) -- tune replace proof
 exact he _ _ hp le_rfl
end YM.CF.Py
