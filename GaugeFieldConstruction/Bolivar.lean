import GaugeFieldConstruction.Farview
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Py Trees Hake FlightFlux TableF Boom Axon Lenten.ModuleB Flot Taxi
open HarmP
namespace BellPrice
open Lenten FlightFlux Fluxim
open Planned.PrimaryIntegral295 Carrier
open Py Py.Rate Riant
section
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{b n m:Side}{d:ℝ}
  (P:PinRack)(V:Grace K R L)(U:Grasp V.U b d)(W:GivenX V U)(F:Pilot)(I:Stake.Isle)
  {S:StepData (Domain n b) (Domain m b)}{T:Tube SU.group S} {G:Ratio (mid n b) (mid m b)} {q q':Chi}
  (A ε D1 h Jd Jk:ℝ)(NHeat:ℕ)(D:Corset d q' Jd 8 3)(Zp:ℝ)(Jp:PactH d Jd ε Zp q' 8 3 D)
  (x H0f v δ:ℝ){r:ℕ}{γ α:ℝ}(X:GramM (mid n b))(Y:GramM (mid m b))(H:Muster G S x d T)
  (Z:Pluck R)(M:Sheep V U W G Y.J X.J 8 2 A)(mQ:Sheet.isle M=I)(u: SharpHerd M 3) (Qf:Fend V H M Z F q Y.p X.p γ α 105 5 r) (vr:Fend V (Muster3 H) (Sheep3 V (X:=X) (Y:=Y) M u) Z F q (KeyUp Y.p) (KeyUp X.p) γ α 105 5 r)
  {G₀:Scree.Loom (mid n b)}{G₁:Scree.Loom (mid m b)} (FiniteGaugeData: Girt.BaseL U G (Gram3 Y) G₀ G₁ q' Jd)
  (c0 c1:ℕ){s:ℝ}(A₀:Roof _ Jk s c0 G₀)(A₁:Roof _ Jk s c1 G₁) (p₀:c0+c1≤radiusB x) (a0: StatV V G T U W X Y α γ 1 x 2 6) (L0:StageP V H Y X U)
  (P_:∀ X: Support (Domain m b),Lend m b d X){t:ℝ}
  (ht:Vista U Y.J.M Y.J.P P_ (6+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
  (pB:Stake.PondP V F x Jk Jd 105 5 8) (hJ: Jd< firstRadius SU.group)(g₁:0<Jd)(g₂:0<Jk)
  (Aι: Flight 4 4)(p:Aι.L=S.ratio.count)(hp:HEq (linesOf Aι K.bind.penalty) T.R.A0)
  (Zx: Footprint.reserve Y.p.supportExponent (1+2+2) (Footprint.conversion S.ratio (5+90+5)) (1/4))
  (pQ:P.Readied V U W F I A ε h D1 (q:=q) Jd Jk D NHeat x H0f v δ) (hg:0 < h)
  (hw:100*(1+radiusB x)≤ (Domain n b).val) (hv:300 <(mid m b).val)
variable (i:Roc (mid m b))(F₀:InkD (mid m b))(G'T:ℝ)(G₀T:PressB (KeyUp Y.p) i.1 F₀ h G'T)(TX:PressB (KeyUp Y.p) i.1 (actionZ Y i) h (P.wide*G'T))(TZ:PressB (KeyUp Y.p) i.1 (actionZ Y i-F₀) h (H0f*G'T)) (χV:Y.p.mass i.1.val.2 G'T ≤ D1*coin₂ R x) (hθ:K.j=4)
namespace PinRack
lemma Coffer.monoQ{b c a:ℝ}(h:b≤c)(p:0 ≤ a): Oath.Coffer a b ≤ Oath.Coffer a c:=by
 have he:=mul_nonneg cab_pos.le (show (0:ℝ) ≤ 16 by norm_num)
 exact add_le_add (mul_le_mul_of_nonneg_left h (sq_nonneg _)) (max_le_max (mintOrder (mul_le_mul_of_nonneg_left h he)) (mintOrder (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h p) he)))
lemma floored(P:PinRack) :1 ≤ P.mass:= P.planet.2.2.2.2.2.2.1
abbrev Plough(P:PinRack)(k:ℕ)(L:Side)(C:ℝ):ℝ:= stipe P.Fc P.B L*(αN L)^(3+k)*C
abbrev SaltL (F R B:ℝ)(L:Side):=F +2*(αN L)^6 *B
lemma C_Rail {Ay:Vow.Aura (mid n b)} {K K0 Lf Z' t :ℝ}(g: CurrentWork V F Z U W P_ (Muster3 H) (Xs:=Gram3 X) (Y:=Gram3 Y) (M:=Sheep3 V (X:=X) (Y:=Y) M u) vr ht FiniteGaugeData i Ay t h K K0 Lf) (u:K ≤Z') : CurrentWork V F Z U W P_ (Muster3 H) (Xs:=Gram3 X) (Y:=Gram3 Y) (M:=_) vr ht FiniteGaugeData i Ay t h Z' K0 Lf:=by obtain ⟨L,x,v,Y,g,p,q⟩:=g.coin; exact ⟨L,x,v,Y,g,p.trans u,q⟩
-- AB includes approximation, no ages. κ full, use at D
structure Psalm (Ay:Palot.leaf (Site (Domain n b)))(v0 w C:ℝ)(pG:ℝ):Prop where
 young(k:ℕ)(p:k ≤3)(hp:Short S Y.p i.1.val.2 → CarBot _ i.1.val.1 (KeyUp Y.p) M.castX.2 F₀ h k): CurrentWork V F Z U W P_ (Muster3 H) (Xs:=Gram3 X) (Y:=Gram3 Y) (M:=Sheep3 V (X:=X) (Y:=Y) M u) vr ht FiniteGaugeData i Ay (luceL R NHeat x) h (SaltL w pG C R.L + P.Plough k R.L C) w 5
 lucia (hg: Short S Y.p i.1.val.2)(k:ℕ)(p:k ≤ 2)(E:InkD (mid m b))(b0 b1:ℝ)(p0:PressB (KeyUp Y.p) i.1 E h b0)(p1:PressB (KeyUp Y.p) i.1 (F₀-E) h b1)(g0:CarBot _ i.1.val.1 (KeyUp Y.p) M.castX.2 E h k)(g1:CarBot _ i.1.val.1 (KeyUp Y.p) M.castX.2 (F₀-E) h (k+1)): CurrentWork V F Z U W P_ (Muster3 H) (Xs:=Gram3 X) (Y:=Gram3 Y) (M:=Sheep3 V (X:=X) (Y:=Y) M u) vr ht FiniteGaugeData i Ay (luceL R NHeat x) h (SaltL w pG C R.L + (P.Plough k R.L b0+ P.Plough (k+1) R.L b1)) w 5
 nodeC (hg:Short S Y.p i.1.val.2)(k:ℕ)(p:k ≤2)(hp:CarBot _ i.1.val.1 (KeyUp Y.p) M.castX.2 F₀ h k)(Y':i.1.val.2 ⊆ halo 24 {i.1.val.1})(M':Tulip.Male) : Opining V F Z U W P_ (Muster3 H) (Xs:=Gram3 X) (Y:=Gram3 Y) (M:=Sheep3 V (X:=X) (Y:=Y) M u) vr ht FiniteGaugeData i Ay (luceL R NHeat x) h (Coffer SqBrim (((6:ℕ).factorial:ℝ)*SaltL w pG C R.L)+ αN R.L^6*C) (MoonBook _ k h (KeyUp X.p) (KeyUp Y.p) G.count i.1.val.1 M.castX.2 F₀) k M'
include pQ hg Qf vr mQ a0 L0 A₀ A₁ p₀ Zx g₁ g₂ Jp TX TZ χV G₀T hJ pB p hp hw hv hθ
lemma hymn (Ay: Palot.leaf (Site (Domain n b))) (pAy:Ay.val=Lattice.halo (1000*radiusB x) {S.ratio.parent i.1.val.1}): let Z0:=P.APillar Y.p R.L i.1.val.2 G'T; Psalm P V U W F A h Jd NHeat x X Y H Z M u vr FiniteGaugeData P_ ht i F₀ Ay G'T Z0 (P.rising*G'T) v:=by
 obtain ⟨V₀,V₁,s,A',y₀,x',z₀,a',vz⟩:= tiltβ P V U W F I A ε D1 h Jd Jk NHeat D Zp Jp x H0f v δ X Y H Z M mQ u Qf vr FiniteGaugeData c0 c1 A₀ A₁ p₀ a0 L0 P_ ht pB hJ g₁ g₂ Aι p hp Zx pQ hg i F₀ G'T G₀T TX TZ χV Ay
 let Ξ:=Muster3 H; let W0:=s.gear; intro Z0
 let v0:=stat_3 V a0; let Hm:=Sheep3 V (X:=X) (Y:=Y) M u; obtain ⟨Qx,Qv,Hq⟩:=sail_t V (M_:=Hm) (H₀:=Gram3 Y) (H₁:=Gram3 X)
 obtain ⟨K_T,kV⟩:= Py.zoneX G W.health.le -- tune
 have hb:X.p.threshold ≤ 2*Y.p.threshold:=by rw [a0.down.low,a0.down.large]; exact pQ.tempZ
 let Rp:=KeyUp X.p; let Yp:=KeyUp Y.p
 let Nq:= luceL R NHeat x; let Xi:=(hostX (l:= (H.post+90)*radiusB x) S i); let I0:=S.ratio.parent i.1.val.1
 have hw0:=s.bell; have hx:(P.u)*Rp.threshold*(1+(Heir.reach x:ℝ)) < Jd:= by rw [show Rp.threshold=temp x from a0.down.large]; exact pQ.limit
 have hxP:0 ≤ P.u:= zero_le_one.trans P.planet.2.2.1; have hxQ:1 ≤ P.gT:=P.planet.2.2.2.2.2.2.2
 have htU(v:Short S Y.p i.1.val.2):= short_nonwrap v a0.down.hU hw i.1.property
 let hE:= pQ.course (Domain n b) (mid m b) S Yp i.1 v0.down.low v0.down.hU (a0.hunt.cert.got ▸ rfl) -- tune
 let CC:=P.rising*G'T; have hpC:F₀=F₀:=rfl; have hyT:P.wide≤P.rising:=le_add_of_nonneg_right (by norm_num); have hpT:1≤P.wide:=P.planet.2.2.2.2.2.1; have hpK:=skim G₀T hg.le; have hL:0 ≤ CC:=by unfold CC; exact mul_nonneg (zero_le_one.trans (hpT.trans hyT)) hpK
 have hpS:0 ≤ stipe P.Fc P.B R.L:=(by unfold stipe; positivity) -- shadow hb
 have hwQ:PressB Yp i.1 (actionZ (Gram3 Y) i) h CC:=Hope.hi_p TX (mul_le_mul_of_nonneg_right hyT hpK); have hg':G'T≤ CC:=le_mul_of_one_le_left hpK (hpT.trans hyT); have hu0:=Hope.hi_p G₀T hg'; have hu':= Hope.hi_p TZ (show H0f*G'T ≤ ε*G'T from mul_le_mul_of_nonneg_right pQ.lean hpK); let z:= P.ShootZ R.L; let μ:= (αN R.L)^6; have hm:0 ≤ μ:=by unfold μ; have hp:=α_pos R.L; positivity
 let Vz:= Z0+ Zax (radiusB x) Hm.r0 5 (A*followV [] G.count) 0 (mastTar z P.gT) ε CC 3+7*prey z * (ε*G'T)
 have hi:Vz ≤ SaltL Z0 v CC R.L :=by
    have hk₁ :Zax (radiusB x) Hm.r0 5 (A*followV [] G.count) 0 (mastTar z P.gT) ε CC 3 ≤ μ*CC:= by rw [show Hm.r0=I.r0 from congrArg Stake.Isle.r0 mQ,a0.hunt.bill]; exact pQ.apex _ hL
    have hk₂: 7*prey z*(ε*G'T) ≤ μ*CC:=by rw [←mul_assoc]; exact (mul_le_mul_of_nonneg_right pQ.light hpK).trans (mul_le_mul_of_nonneg_left hg' hm)
    exact (add_le_add (add_le_add_right hk₁ _) hk₂).trans_eq (by unfold SaltL μ; ring)
 have hZ:Short S Y.p i.1.val.2 → Stakes z (αN G.count) i.1 Yp:=by rw [a0.hunt.bill]; exact hE -- t shadow mk explicit
 constructor
 · intro j u0 t; by_cases hy:Short S Y.p i.1.val.2; swap
   · have hL':= oldQn V F D Z U W P_ Ξ (M:=Hm) (Xs:=Gram3 X) (Y:=Gram3 Y) vr ht FiniteGaugeData i P.loft P.st P.c P.c' ε P.u v0.down Jp h Ay Xi pAy rfl V₀ V₁ W0 P.Fc Nq (δ/2) s.mark _ 5 s.deep (s.fork0 hy) (by norm_num) -- tune order
     apply C_Rail V U W F A h Jd x X Y H Z M _ vr FiniteGaugeData P_ ht i hL'; exact ((le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hm) hL)).trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hpS (pow_nonneg (α_pos _).le _)) hL))) -- tune many implicit
   have hp':= flareC V F D Z U W P_ Ξ (M:=Hm) (Xs:=Gram3 X) (Y:=Gram3 Y) vr ht s.facet rfl FiniteGaugeData i (half_lt_self g₂) (half_pos g₁) (half_lt_self g₁) c0 c1 A₀ A₁ p₀ (by omega) hJ pQ.pole hw0 P.loft P.st P.c P.c' ε P.u v0.down Jp A' h CC hwQ z₀ y₀ Qx Hq.tax hy Ay Xi pAy rfl V₀ V₁ W0 hθ v0 K_T kV P.Fc Nq (δ/2) s.mark Z0 5 s.tall s.fork1 (by norm_num) Qv Hq x' rfl F₀ (ε*G'T) hu0 hu' a' vz P.F (by omega) hg (htU hy) (by omega) j u0 (hZ hy) pQ.oxy.le pQ.poll rfl P.gT hxQ hx P.planet.2.2.2.1 P.tariff rfl hxP (t hy)
   exact C_Rail V U W F A h Jd x X Y H Z M _ vr FiniteGaugeData P_ ht i hp' (add_le_add hi (stipeV _ _ _ j _ _ v0.down.order hL))
 · intro hy j p E b0 b1 P0 P1 g g';
   have hp':= flareD V F D Z U W P_ Ξ (M:=Hm) (Xs:=Gram3 X) (Y:=Gram3 Y) vr ht s.facet rfl FiniteGaugeData i (half_lt_self g₂) (half_pos g₁) (half_lt_self g₁) c0 c1 A₀ A₁ p₀ (by omega) hJ pQ.pole hw0 P.loft P.st P.c P.c' ε P.u v0.down Jp A' h CC hwQ z₀ y₀ Qx Hq.tax hy Ay Xi pAy rfl V₀ V₁ W0 hθ v0 K_T kV P.Fc Nq (δ/2) s.mark Z0 5 s.tall s.fork1 (by norm_num) Qv Hq x' rfl F₀ (ε*G'T) hu0 hu' a' vz P.F (by omega) hg (htU hy) (by omega) j (by omega) (hZ hy) pQ.oxy.le pQ.poll rfl P.gT hxQ hx P.planet.2.2.2.1 P.tariff rfl hxP E b0 b1 p P0 P1 g g'
   exact C_Rail V U W F A h Jd x X Y H Z M _ vr FiniteGaugeData P_ ht i hp' (add_le_add hi (add_le_add (stipeV _ _ _ j _ _ v0.down.order (skim P0 hg.le)) (stipeV _ _ _ (j+1) _ _ v0.down.order (skim P1 hg.le))))
 intro hy j g t hg' M''
 obtain ⟨σ,Cu,k,Qk,Qh⟩:=pQ.rich.2.1.pull n m b S T (Gram3 X) (Gram3 Y) (a0.hunt.cert.got ▸ rfl) (by omega) rfl v0.down.large ‹X.p.threshold ≤2*Y.p.threshold› Aι p hp
 have hp':= opening_ V F D Z U W P_ Ξ (M:=Hm) (Xs:=Gram3 X) (Y:=Gram3 Y) vr ht s.facet rfl FiniteGaugeData i (half_lt_self g₂) (half_pos g₁) (half_lt_self g₁) c0 c1 A₀ A₁ p₀ (by omega) hJ pQ.pole hw0 P.loft P.st P.c P.c' ε P.u v0.down Jp A' h CC hwQ z₀ y₀ Qx Hq.tax hy Ay Xi pAy rfl V₀ V₁ W0 hθ v0 K_T kV P.Fc Nq (δ/2) s.mark Z0 5 s.tall s.fork1 (by norm_num) Qv Hq x' rfl F₀ (ε*G'T) hu0 hu' a' vz P.F (by omega) hg (htU hy) (by omega) j (by omega) (hZ hy) pQ.oxy.le pQ.poll rfl P.gT hxQ hx P.planet.2.2.2.1 P.tariff Aι p.symm hp K.bind.penalty_pos σ Cu k Qk δ pQ.rich.2.2 Qh M'' rfl hxP g hg' t
 have he:Polaris i.1 Rp Yp z (δ/2) δ G P.B CC j ≤ μ*CC:=by
    apply pQ.rich.1.holds n m b G i.1 S a0.hunt.bill (a0.hunt.cert.got ▸ rfl) _ _ hy v0.down.low v0.down.hU ‹X.p.threshold ≤2*Y.p.threshold› _ _ _ g hL; change _ ≤ (mid n b).val*2 at hw; omega
 exact ⟨fun u v k' t=> HeadX.rise (hp'.price u v k' t) (add_le_add (Coffer.monoQ (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α:=ℝ) (6:ℕ).factorial)) (by unfold SqBrim; positivity)) he)⟩ -- tune
end PinRack
end
end BellPrice
end YM.CF.Oath
end
