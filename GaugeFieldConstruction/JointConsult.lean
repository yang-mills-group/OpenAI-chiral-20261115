import GaugeFieldConstruction.Tutelage
import GaugeFieldConstruction.JointRates
import YM.SU5.Exchange.Reg.May

/-!
# Select one consultant able to afford both costs.

From GaugeFieldConstruction.Tutelage and LocalFieldBounds proof strategy in Reg/May; at the Service application
many more budgets than either alone.
-/
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

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus
private lemma penglJt(z:ℝ): ∃ N:ℕ,∀ y:Side,N≤ y.val → z*(y.val:ℝ)⁻¹^2≤1:=by
 obtain ⟨n,h⟩:=exists_nat_gt z
 refine ⟨n,fun y p=>?_⟩
 let A:ℝ:= y.val; have hu:1 ≤ A:=Nat.one_le_cast.mpr y.property
 rw [inv_pow,←div_eq_mul_inv]; exact (div_le_one (sq_pos_of_pos (zero_lt_one.trans_le hu))).mpr (le_trans (h.trans_le (Nat.cast_le.mpr p) |>.le) (le_self_pow₀ hu (by norm_num)))

-- chronological purchase (history gate costs are chosen later, from these same allowances).
set_option maxHeartbeats 2150000 in
lemma jointCulmen {F:ℕ→(s:Side)→Scree.Loom s → Prop}(z0:AvailableΛ F)(NLeaf Tleaf:ℕ):∃ (K:Teller SU.group)(L:ChartRatio SU.group),K.j=4 ∧ LocalRatio L ∧ K.top.clip.direct ≤1 ∧∃ (C:ℝ)(Pay kC Γ:ℝ)(Tξ:Hove.Grant K.j 2), 0 ≤ Pay ∧ 0 ≤ kC ∧ 0 ≤ Γ ∧ Taxi.DayT 6 Γ ∧∃ (A C':ℝ)(N:ℕ),1≤K.C ∧ 0 < A ∧ CutZ A K.j 3 ∧ (Neon.KX 5)^3<N ∧(Neon.PKard 5)^3<N ∧ 10≤N ∧∀ (P:Patch),N ≤ P.L.val → P.J=4→ (((P.L.val:ℝ)^4)⁻¹ < VolumeRate.propagation) ∧∃ (V:Grace K P L)(T:Acorn.Repair K.j)(l:ℕ),1 ≤ l ∧∀ B:ℕ,l ≤ B → ∃ e:ℝ,0 < e ∧∀ q:Chi,∀ d:ℝ,0<d→ d ≤ e →∃ (U:Grasp V.U (P.L^B) d)(W:GivenX V U)(Fp:Pilot)(I:Stake.Isle)(mo:ℕ), SharpSheep V U W I A 6 2 3 mo ∧ U.baseline ≤ T.d ∧ 1 < I.fine ∧∀ v > (0:ℝ),∀ w >(0:ℝ),∃ (M:Side)(J:Robes M V W)(D':Corset d q J.d 8 3)(z:ℝ), PactH d J.d v z q 8 3 D' ∧ J.d ≤ w ∧ 8 ∣ M.val ∧ J.k ≤ J.roomX ∧∃ (K0 Gv sℝ:ℝ),0<K0∧0<Gv∧0<sℝ∧ Budget (P.L^B) d sℝ ∧ ∃ (F0:Scrolls (P.L^B)) (l':ℕ), (∀ m, ScaleK K0 Gv (F0 m)) ∧ RackedΛ (F l') J ∧∃ Z> (0:ℝ),∀ᶠ h:ℝ in atTop, FinancesVector V q W M J B F0 C Z h (fun n0 Pβ => Tutelage V J Fp I q h n0 A C' Pay kC Γ Tξ NLeaf Pβ ∧ RateCover J q h n0 Pay kC Γ Tξ Tleaf Pβ) ∧ ∀ᶠ N0:ℕ in atTop, WheelExact J q h N0 ∧ WheelX J q h N0 ∧ MeritWheel J q h N0:=by
 let w:ℝ:=1; let p:ℕ:=2; let k:ℕ:=6
 have hb:4≤4:=le_rfl; have u: Even 4:=⟨2,rfl⟩; have hw:0<w:=zero_lt_one; have ht: 6 ≤ k:=le_rfl; have hp:2≤p:=le_rfl
 obtain ⟨K,Z,L',t,uK,A,v,N,P⟩:=Vale.score 4 k p hb u ht hp
 have he:Even K.j:= uK.symm ▸ u; have hz:1 ≤ K.j:= by omega
 obtain ⟨A',hA'⟩:= Stake.granted K.j 3 (by omega) he
 obtain ⟨M0,mC,C,C',w',hm,hmC,hC,hC',hw',hCk⟩:= Oath.cites K k p (by omega) hp (zero_le_one.trans t)
 obtain ⟨Xc⟩:=harvest k C (by omega) hC; obtain ⟨κ⟩:=Oath.prepare k C' (by omega) hC'
 let σ:=w+2+2; let Kp:=keyS σ A' 1 κ.C 5 p k; obtain ⟨n,l⟩:= scope_a w A' hw 5 k
 obtain ⟨D,h,N₀,f⟩:=slice_b σ 1 A' k p 5
 obtain ⟨N₁,ξ⟩:= penglJt κ.C; let Zr:= thermV σ M0 mC (w/4) D Kp 2 Xc p 5
 let Q:= Classical.choice (waver K.j p (by omega) hp he)
 obtain ⟨Aχ,uA,Dχ⟩:= Taxi.ori_u k; obtain ⟨Γχ,hQ,DG⟩:= Taxi.psalmB k
 obtain ⟨Wk,tW,wT⟩:= Haro.nova; let Yv:= pond_X k p w ht hp hw; let Cu:=(Beau.tax_E Yv K.below.clip K.below.width K.below.paths Aχ Γχ + 1)*νC Yv Wk*ray_T p k Zr w Q.C 1
 obtain ⟨N₂,t₂⟩:= exists_nat_gt (4*Cu); obtain ⟨N₃,t₃⟩:=eventually_atTop.mp (propagates.and (reach_fit (Aχ:=Aχ) (Γχ:=Γχ) hz tW Zr Q.C))
 obtain ⟨B₀,bv⟩:= Chaff.coat_H k p (by omega)
 obtain ⟨Kc,Kv⟩:= Tune.tent k (by omega) C hC
 let Tξ:= Classical.choice (Hove.give_a K.j p he (by omega) hp)
 have hμ:0 ≤ Zr:=by
    unfold Zr thermV; have hb:0 ≤ Xc.B:=zero_le_one.trans Xc.hi; have he:=tollPos k p 5 C σ M0 (w/4) mC Xc (by positivity) hm hmC; have hp0:0 ≤ Kp:= keyP σ _ _ _ (zero_le_one.trans κ.lamp) hA'.1.le 5 p k
    let U':=leaps k p 2; have h:1 ≤ D:=h; have hp:0 ≤ Lgrit (w/4):=by unfold Lgrit; positivity
    unfold firmZ leafZ leaps backX; dsimp only; positivity
 refine ⟨K,Z,uK,L',A,Cu,Zr,Kc,Γχ,Tξ,hμ,zero_le_one.trans Kv.ge,hQ,DG,A',C',N+n+N₀+N₁+N₂+N₃+100+(Neon.KX 5)^3+(Neon.PKard 5)^3,t,hA'.1,hA',by omega,by omega,by omega,fun L p' t'=>?_⟩
 obtain ⟨Uσ,Uψ⟩:= t₃ L.L.val (by omega); refine ⟨Uσ,?_⟩
 obtain ⟨V,T,i,hp'⟩:= P L (by omega) t'; obtain ⟨Δ,hu,U⟩:= ample_strict V T (k+2) 3 (by omega) hA'
 obtain ⟨α,e,η⟩:= equipEven z0 V
 obtain ⟨d₀,a₀,μ₀,v₀,p₀,pμ,vμ,hW,n₂,M⟩:=ores V Yv Wk (by omega) tW
 obtain ⟨b0,b1,b2,b3,bζ,bζ',bε,Ξh,nμ,Mμ,Rμ⟩:= empress (V:=V) Yv (mul_pos (by norm_num : (0:ℝ)<2) (show 0< catap Wk from mul_pos (by norm_num) tW)) hz
 let Vet: Major V Wk b0 b1 b2 b3 Aχ Γχ nμ:=⟨Mμ,Rμ,wT,tW,by omega,bζ,bζ',hz,A,DG,Dχ,uA,hQ⟩
 refine ⟨V,T,i+B₀+1,by omega,fun B hB=>?_⟩; obtain ⟨ε,u',Y⟩:= hp' B (by omega)
 obtain ⟨e₁,e₂,pV⟩:=bv (L.L^B) (le_trans (show B₀ ≤ B from by omega) (Vale.huge _ (by omega) _))
 refine ⟨min ε (min Δ (min α (min e₁ (min d₀ b3)))),lt_min u' (lt_min hu (lt_min e (lt_min e₂ (lt_min p₀ bε)))),fun q d p'0 r=>?_⟩; obtain ⟨hf,hf',hg₀,hf₁,hf₂,hg₁⟩ : d≤ ε ∧ d≤Δ∧d≤α∧d ≤ e₁∧d≤d₀ ∧ d≤ b3:= by simp only [le_min_iff] at r; exact r
 obtain ⟨E,W,v,L1,S,hP⟩:=Y _ p'0 hf; obtain ⟨I,g',m,Rf⟩:=U E W hf' L1
 let t:=κ.C*(L.L.val:ℝ)⁻¹^2; have hZ:0<t:=by have he:0<κ.C:=zero_lt_one.trans_le κ.lamp; unfold t; positivity
 obtain ⟨bP,b,β,kp⟩:= pact_l (d:=d) p'0 t hZ (k+2) p q
 obtain ⟨F_,hV⟩:= flyingVolume K L V.L.cloth V.vor L' (k+2) 105 5 (by omega) (by omega) (by omega) q
 have Rq: SharpSheep V E W I A' k p 3 m:= sharp_issue V E W (k:=6) (n:=3) Rf p (by omega)
 let R:SheepP V E W I A' k p m:= SharpSheep.terms V E W @Rq
 refine ⟨E,W,F_,I,m,Rq,L1,g',fun vₓ hₓ wr hr =>?_⟩
 obtain ⟨bP',hgn,bX⟩:=pact_l (d:=d) p'0 vₓ hₓ 8 3 q
 obtain ⟨M',J,jEven,jk,kE,kF,hF⟩:=η E W hg₀ (min bP (min wr bP')) (lt_min b (lt_min hr hgn))
 have hkP:J.d≤ min wr bP':= kE.trans (min_le_right ..) -- fix here kE ≤min bP..., hh direction min_le_*.
 obtain ⟨Dv,zv,vW⟩:=bX.2 J.d J.hv (hkP.trans (min_le_right ..)) J.knot
 obtain ⟨D_,κ0,Jp⟩:= kp J.d J.hv (kE.trans (min_le_left ..)) J.knot
 obtain ⟨G0,Q₀,E₀,hμ',aG,aE,sQ,F0,hπ,zX⟩:=pV d p'0 hf₁ L K Z V E W.pearl V.note hz A
 refine ⟨M',J,Dv,zv,vW,hkP.trans (min_le_left ..),jEven,jk,Q₀,E₀,G0,aG,aE,hμ',sQ,F0,kF,hπ,hF,(mintPressure V L' I +2), add_pos (mintPressure_pos ..) (by norm_num),?_⟩

 obtain ⟨g,x⟩:=l L (by omega); obtain ⟨a0,e0,p0,p1,p2⟩:=Wray.sapI; have hx:= f L (by omega); have htK:= ξ L.L (by omega); let O':= model_b V E W R g'
 obtain ⟨β,hβ,k₀,tQ⟩:=bolts V F_ E W I q q 5 M0 mC C C' w' σ (w/4) D Xc κ A' 1 a0 e0 p0 p1 p2 (zero_le_one.trans hw') zero_lt_one O'.g8 hCk (by omega) hx.1 hx.2.1 hx.2.2.1 J.d J.hv D_ 3
 filter_upwards [tQ,x I,hW,Ξh,eventually_ge_atTop 1] with H mQ η hW Ξh tv
 obtain ⟨n',Z',E₁,H₁Θ⟩:=totem_flux (U:=E) V E W _ I Rq L' g' q q J.k w J.roomX J.d hA'.1 hw g (show 5+100≤105 from by omega) ht hp (l:=5) le_rfl (by omega) J.hv J.knot J.hr J.ht jk J.n D_ D M0 mC C C' w' Xc hm hmC κ (zero_le_one.trans hw') Jp F_ (hV.mono fun i p=>p.master) H tv η β 3 k₀ hβ htK mQ Kc Kv (by omega) (by omega)
 let H₁ := Fiords.hide V E W I q q J.k w J.roomX J.d J.n D_ C' κ Jp F_ Z' E₁ n' H 3 Zr I.r0 Kc k₀ β H₁Θ
 let R_ := retain V E W I q q J.k w J.roomX J.d J.n D_ C' κ Jp F_ Z' E₁ n' H 3 Zr I.r0 H₁
 let t_:Treaty J q A' C' Zr H I.r0:=⟨I,F_,Z',E₁,D_,κ,κ0,Jp,n',hV,g',riverUpgrade V E W I q q J.k w J.roomX J.d J.hr J.ht jk J.n D_ C' κ Jp F_ Z' E₁ n' H tv 3 Zr I.r0 H₁,jk,L',hA'.1,tv,O'.g8⟩
 let hp':=ore_M V E W q q J.k w J.roomX J.d J.hr J.ht jk J.n D_ C' κ Jp F_ Z' n' H tv 3 Zr I.r0 R_; have htX:=ore_B V E W q q J.k w J.roomX J.d J.hr J.ht jk J.n D_ C' κ Jp F_ Z' n' H tv 3 Zr I.r0 R_
 obtain ⟨R0,δ,c,Tlimit,tR⟩:= jointPamphlets (D:=t_) Vet Ξh (J.hr.le.trans hg₁) Uψ k₀ β (show t_.bandsShade Kc k₀ β from river_salt V E W I q q J.k w J.roomX J.d J.hr J.ht jk J.n D_ C' κ Jp F_ Z' E₁ n' H tv 3 Zr I.r0 Kc k₀ β H₁Θ) Tξ NLeaf Tleaf
 obtain ⟨Fq,u,eY⟩:= zX w H tv
 have hU:SunK V w p k J H Fq F0:=by refine ⟨?_⟩; filter_upwards [eY] with x p c T R hx ht u t b' B; exact p c T R J.k J.roomX J.n ht u hx t b' J.hr B
 refine ⟨⟨⟨Fq,u,hU⟩,?_⟩, (eventually_ge_atTop _).mono (fun n v=> ⟨beaconWheel Vet Ξh (J.hr.le.trans hg₁) Uψ n (show t_.size+200+(nμ+1)+Test.perimeter L.L.val≤n from v), cobalt_wheel Vet Ξh (J.hr.le.trans hg₁) Uψ n (show t_.size+200+(nμ+1)+Test.perimeter L.L.val≤n from v), beaconMerit Vet Ξh (J.hr.le.trans hg₁) Uψ n (show t_.size+200+(nμ+1)+Test.perimeter L.L.val≤n from v)⟩)⟩
 filter_upwards [eventually_ge_atTop (n'+n₂), eventually_ge_atTop (t_.size+200+(nμ+1)+Test.perimeter L.L.val)] with n v t
 have hh:Cu/(L.L.val:ℝ) ≤ 1/4:=by rw [div_le_iff₀ (by positivity)]; linarith [(t₂.trans_le (Nat.cast_le.mpr (show N₂≤L.L.val by omega)))]
 have hpT: CoAppointed J q R0 δ c H n (fun Pβ=> Tutelage V J F_ I q H n A' C' Zr Kc Γχ Tξ NLeaf Pβ ∧ RateCover J q H n Zr Kc Γχ Tξ Tleaf Pβ):=by
    obtain ⟨⟨P,x,Q,v,W,u⟩,a,b,d⟩:= tR n t
    exact ⟨⟨P,x,Q,v,W,⟨t_,rfl,rfl,k₀,β,hβ,u.1⟩,u.2⟩,a,b,d⟩
 refine ⟨⟨tv, hh,delay_Coffer V E W q J.k w J.roomX J.d J.n H _ (tree_PS (U:=E) V E W L' q q J.k w J.roomX J.d hA'.1 hw ht hp J.hr J.ht jk J.n D_ C' κ Jp F_ Z' n' H tv 3 Zr I.r0 A Q Aχ Γχ Dχ DG uA hQ Wk a₀ μ₀ v₀ d₀ n₂ (J.hr.le.trans hf₂) (by omega) tW wT M pμ vμ hW O'.g8 (by omega) hp') v,delay_HoldU V E W q J.k w J.roomX J.d J.n H _ (tree_UB (U:=E) V E W L' q q J.k w J.roomX J.d hA'.1 hw ht hp J.hr J.ht jk J.n D_ C' κ Jp F_ Z' n' H tv 3 Zr I.r0 A Q Aχ Γχ Dχ DG uA hQ Wk a₀ μ₀ v₀ d₀ n₂ (J.hr.le.trans hf₂) (by omega) tW wT M pμ vμ hW O'.g8 (by omega) hp') v, ⟨_,delay_VaultXU V E W q J.k w J.roomX J.d J.n H _ (tree_BP (U:=E) V E W L' q q J.k w J.roomX J.d hA'.1 hw ht hp J.hr J.ht jk J.n D_ C' κ Jp F_ Z' n' H tv 3 Zr I.r0 A Q Aχ Γχ Dχ DG uA hQ Wk a₀ μ₀ v₀ d₀ n₂ (J.hr.le.trans hf₂) (by omega) tW wT M pμ vμ hW O'.g8 (by omega) htX) v⟩,n', le_trans ?_ v,tree_L (U:=E) V E W L' q q J.k w J.roomX J.d J.hr J.ht jk J.n D_ C' κ Jp F_ Z' n' H tv 3 Zr I.r0 htX⟩,δ,R0,c,hpT,Tlimit⟩
 omega

#print axioms jointCulmen

end Rate
end YM.CF.Py
end
