import YM.CF.DPress.Calendar.Eqp
import YM.CF.Pso.Years
import YM.CF.BPress.Age.Summer

/- Adapted from FiniteGaugeData proofs in corresponding imported modules. Strengthening as in VolumeB-gate:
   keep q_P lower speed in same grant emitted while d, threshold still adjustable. This version is for
   comparator use; simultaneously need all Looms from those Robes to have Firm. -/
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
open Oath Feu Feu.Corset Nor
private lemma vibes_DP(z:ℝ): ∃ N:ℕ,∀ y:Side,N≤ y.val → z*(y.val:ℝ)⁻¹^2≤1:=by
 obtain ⟨n,h⟩:=exists_nat_gt z
 refine ⟨n,fun y p=>?_⟩
 let A:ℝ:= y.val; have hu:1 ≤ A:=Nat.one_le_cast.mpr y.property
 rw [inv_pow,←div_eq_mul_inv]; exact (div_le_one (sq_pos_of_pos (zero_lt_one.trans_le hu))).mpr (le_trans (h.trans_le (Nat.cast_le.mpr p) |>.le) (le_self_pow₀ hu (by norm_num))) -- tune
-- Power growth δ.Call pre fixed Chart. ALL roots.Kick after.Warning.CutBoost must choose η Health depth after V'. tuition.Cover. Protect grant even pole.SHAPE.
lemma elm_D (j k p:ℕ)(w:ℝ)(ht:6≤k)(hp:2≤p)(hb:4≤j)(u:Even j)(ha:0<w):∃ (K:Teller SU.group)(L:ChartRatio SU.group),K.j=j ∧ LocalRatio L ∧ K.top.clip.direct≤1∧ (∀ P:Patch,P.Branches K.bind SU.group) ∧∃ (D Z A:ℝ) (κ: SuitP k D),∃ N:ℕ,∀ (P:Patch),N ≤ P.L.val → P.J=j→ ∃ (V:Grace K P L)(T:Acorn.Repair K.j)(l:ℕ),∀ B:ℕ,l ≤ B → ∃ e yP:ℝ,0<yP∧0<e ∧∀ q:Chi,∀ d:ℝ,0<d→ d ≤ e →∃ (U:Grasp V.U (P.L^B) d)(W:GivenX V U)(M:Side)(J:Robes M V W),W.pearl.q=yP∧ U.baseline ≤ T.d∧ Embark J∧ Kneel  V q U W p k M J w A D Z κ:=by
 obtain ⟨K,Z,L',t,uK,A,v,N,P⟩:=Vale.scoreP j k p hb u ht hp
 obtain ⟨A',hA'⟩:= Stake.granted K.j p (by omega) (by rw [uK]; exact u); obtain ⟨M0,mC,C,C',w',hm,hmC,hC,hC',hw,hCk⟩:= Oath.cites K k p (by omega) hp (zero_le_one.trans t) -- `t`:≤. check
 obtain ⟨Xc⟩:=harvest k C (by omega) hC; obtain ⟨κ⟩:=Oath.prepare k C' (by omega) hC'
 let σ:=w+2+2; let Kp:=keyS σ A' 1 κ.C 5 p k; obtain ⟨n,l⟩:= scope_a w A' ha 5 k
 obtain ⟨D,h,N₀,f⟩:=slice_b σ 1 A' k p 5
 obtain ⟨N₁,ξ⟩:= vibes_DP κ.C; let Zr:= thermV σ M0 mC (w/4) D Kp 2 Xc p 5
 refine ⟨K,Z,uK,L',A,v,C',Zr,A',κ,N+n+N₀+N₁,fun L p' t'=>?_⟩
 obtain ⟨V,T,i,hp'⟩:= P L (by omega) t'; obtain ⟨Δ,hu,U⟩:= ample_strict V T (k+2) p (by omega) hA'
 obtain ⟨α,e,η⟩:= equipD V
 refine ⟨V,T,i,fun B h=>?_⟩; obtain ⟨ε,yP,pP,u',Y⟩:= hp' _ h
 refine ⟨min ε (min Δ α),yP,pP,lt_min u' (lt_min hu e),fun q d p'0 r=>?_⟩; have hx:= r.trans (min_le_right ..)
 obtain ⟨E,W,y₁,v,L1,S,hP⟩:=Y _ p'0 (r.trans (min_le_left ..)); obtain ⟨I,g',m,R⟩:=U E W (hx.trans (min_le_left ..)) L1
 let t:=κ.C*(L.L.val:ℝ)⁻¹^2; have hZ:0<t:=by have he:0<κ.C:=zero_lt_one.trans_le κ.lamp; unfold t; positivity
 obtain ⟨bP,b,β,kp⟩:= pact_l (d:=d) p'0 t hZ (k+2) p q
 obtain ⟨M,J,jk,kE,Zfirm⟩:=η E W (hx.trans (min_le_right ..)) bP b
 obtain ⟨D_,N',Jp⟩:= kp J.d J.hv kE J.knot
 let vρ:=m
 refine ⟨E,W,M,J,y₁,L1,Zfirm,jk,D_,N',Jp,fun kP=>?_⟩ -- order
 obtain ⟨F,hQ⟩:= flying K L V.L.cloth V.vor L' (k+2) 105 5 (by omega) (by omega) (by omega) q
 obtain ⟨g,x⟩:=l L (by omega); obtain ⟨a0,e0,p0,p1,p2⟩:=Wray.sapI; have hx:= f L (by omega); have htK:= ξ L.L (by omega); let O':= model_b V E W R g'
 obtain ⟨β,hβ,k₀,tQ⟩:=bolts V F E W I q q 5 M0 mC C C' w' σ (w/4) D Xc κ A' 1 a0 e0 p0 p1 p2 (zero_le_one.trans hw) zero_lt_one O'.g8 hCk (by omega) hx.1 hx.2.1 hx.2.2.1 J.d J.hv D_ kP -- g indices
 filter_upwards [tQ,x I,eventually_ge_atTop 1] with H mQ η htA
 obtain ⟨U₀,K₀,Y⟩:= totem_F (U:=E) V E W _ I R L' g' q q J.k w J.roomX J.d hA'.1 ha g (show 5+100≤105 from by omega) ht hp (l:=5) le_rfl (by omega) J.hv J.knot J.hr J.ht jk J.n D_ D M0 mC C C' w' Xc hm hmC κ (zero_le_one.trans hw) Jp F hQ H htA η β kP k₀ hβ htK mQ -- tune
 exact ⟨F,K₀,U₀,I.r0,O'.g8,hA'.1,Y⟩
end YM.CF.Py


