import Anomaly.Apert.First
import Anomaly.Apert.Fleet
import YM.CF.Rive.Rays
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Mew PowerSeries
open scoped Mew
open Neon Moto Taxi Bake Clock QuadClock Oise
variable {N B:Side}
local notation "Ω"=> mid N B
variable {P:GramM (mid N B)}{g h d q a μ:ℝ}{n l k m:ℕ}{I:Type} [Fintype I][LinearOrder I]
    (K: Key I→ Rinse (Seat (mid N B)) (Copy (mid N B))) (C:Occlus P.p)
    (σ:I→Site (mid N B))
    {M:Key I→ Orbit (mid N B)→ Aura (mid N B)→ FC (Dwell (mid N B))}
    {y b: Aura (mid N B)→ℝ}{r:Aura (mid N B)→Support (More (mid N B))→ℝ}
    (X:OrbitRack C (Cube.node∘σ) n P.K h K y b r M)
local notation "O"=> Cube.node∘σ
variable (Q: I→ RegBudget (mid N B))(c:I→ ArcΦ)(Fv:I→Cusp (mid N B))(t:I→ℂ)
local notation "T"=> lensCells P.K K k
local notation "Tμ"=> lensG (P:=P.p) P.K K k
local notation "Tp"=> lensSimple P.K K k
local notation "Ψf" => mkCup P.p P.K K k Fv
local notation "QΨ"=> bustle (O) Ψf
variable (Z:∀ i:I,Ice l (σ i) P.p h q d a (coldE P.p (τι (lensG (P:=P.p) P.K K k) [i])) (Q i) (Fv i) (t i) (c i))
variable (τ:Ids (mid N B))
local notation "Ls" τ:max => lensD (P:=P.p) P.K K k τ
local notation "JΦ" => FacetE Tμ Q τ
local notation "E'" => awake (O) (Ls τ) Q

variable (hp:1≤h)
include X Z hp
lemma lust_cash (V:Orbit (mid N B))(p:Rue.FleetS P.p.threshold V.1)(z:Key I)(u:z∈hill I) : hGas (flags P.p.threshold V.1) (hailV (flags P.p.threshold V.1) (T z) V)= exp (α_ξ t z • (1:Cipher Ω)+exponentL P.p (JΦ z) V.1)*fueled P.p (P.K+(Ψf z-Ψf 0)) V:=by
  let w:=Tμ; let r'(z:Key I)(u:z∈hill I):Turf (lensG (P:=P.p) P.K K k z):= Bake.turfK _ (X.plain z k)
  let J:= T z; let H:=flags P.p.threshold V.1
  have ht: hailV H J V=keyL P.p J (Tp z) V:=by
    funext i; unfold keyL; split; next h=> unfold hailV; rw [disjoint_iff_inter_eq_empty.mp h]; rfl
    next h=> rfl
  obtain ⟨c0,c1⟩:= rackMoney C P.K K O n M X k hp
  let v:= (layerSuit C P.K K O n M X k hp z u).1
  have hx:=P.p.exponent_pos; have he:=C.hη
  let Fz:= Φstack Fv z
  let R':=α_ξ t z • (1:Cipher Ω)+exponentL P.p (JΦ z) V.1
  have hr: coldE P.p (Tμ z) V = R' + fuelV P.p Fz V:= hepa_F P.p h l σ Fv (fun _=>d) t Tμ Q (fun _=>q) (fun _=>a) c Z τ r' z u V p -- tune
  change hGas H _=exp R' * _
  rw [ht,Vow.polyH J Fz V _ c0 hp v (by linarith only [hx,he]) p R' hr.symm]
  apply congrArg (exp R' * ·)
  exact TreasuryFog.budgetDisplace V (roomV P.p (lensSimple P.K K k z) (T z) Fz) p P.K (Ψf 0) (fun i v=>by rw [budget_genesis K C σ X k Fv hp,eachFace _ _ i _ inter_subset_right]; exact Finset.not_disjoint_iff_nonempty_inter.mp (fun h=>v h.symm))
lemma rim_same : awake (O) (FacetE (lensG (P:=P.p) P.K K k) Q τ) Q= E':=by
  let z:(∀ i x,River fun z=>Tμ z i x):= lensSimpleR C P.K K O n M X k hp
  have hu(i:Finset I)(u:1 < i.card):νΦX JΦ i=νΦX (Ls τ) i:=by
    funext x y; unfold νΦX; exact pulse_I Tμ Q τ z x y (Mew.Cue I i) (show (Mew.Cue I i).Nodup from Finset.sort_nodup ..) (show 2 ≤ (Mew.Cue I i).length from by rw [Mew.Cue,Finset.length_sort]; omega) -- tune convert u
  funext i; unfold awake; refine congrArg (_ + ·) ?_; exact sum_congr rfl fun j v=>by rw [hu j (mem_filter.mp v).2.1]
lemma send_era (V:Orbit (mid N B))(L:List I)(v:ψS (O) L): Soft L (circE (P:=P.p) V.1 JΦ) (circE (P:=P.p) V.1 E'):=by
  have hx(i: I) :νΦX JΦ {i}=Q i:=by funext X y; unfold νΦX; rw [Py.cue_1]; exact pulse_Z Tμ Q τ (lensSimpleR C P.K K O n M ‹OrbitRack ..› k hp) X y i
  have he:Tμ 0=0:=by funext x; change FeeD _ _ x=0; rw [show Tp (0:Key I)=0 from ?_]; exact TreasuryFog.costBright ..; change (fun i:Aura _=>_)=(0:Pax Ω); unfold lensSimple; rw [X.empty]; exact funext (settle0 P.K)
  rw [←rim_same K C σ X Q c Fv t Z τ hp]
  exact castEra O JΦ Q (punk _ _ _ (lensSimpleR C P.K K O n M X k hp) he) (fun i j=>growth_P _ _ _ (lensSimpleR C P.K K O n M X k hp) i j) (fun i _=> by rw [hx]) L v V.1
variable {L:Side}{h_:Odd L.val}{i_:ℕ}{Y:Pricing i_ L h_ (Thread i_)}{e:ℝ}
    (U:Grasp Y B e)(A:Scree.Loom (mid N B))(V:Orbit (mid N B))
omit X Z hp
lemma switched (F:RegBudget Ω)(Q:ForceBudget Ω)(z:ℂ)(q:IsStarProjection (Dial.spar i_ P.J.M (A V))) : denZ (color_b P P.beta (P.F+F) P.slip Q (P.v+z)) U A V = pilotH U P A V q (poseL _ (exp (z • (1:Cipher Ω)+exponentL P.p F V.1) * fueled P.p Q V)) := by
  let V0:=color_b P P.beta (P.F+F) P.slip Q (P.v+z); let P':=color_b P P.beta (P.F+F) P.slip Q P.v
  have he: V0.betaL A V=z+P'.betaL A V:= by unfold V0 P' color_b GramM.betaL GramM.H0; dsimp only; abel
  have hv: denZ V0 U A V=Complex.exp z • denZ P' U A V:=by unfold denZ; rw [he,Complex.exp_add,mul_smul]; rfl
  letI : NormedAlgebra ℚ (Cipher Ω):= NormedAlgebra.restrictScalars ℚ ℂ _
  rw [hv,showUp U A V q F Q,exp_add, ←show hollow z=(z • 1:Cipher Ω) from rfl, ←Iva.yeaH,show (hollow (Complex.exp z):Cipher Ω)=Complex.exp z • 1 from rfl,Algebra.smul_mul_assoc,one_mul,Algebra.smul_mul_assoc,←map_smul]; unfold poseL; exact congrArg (pilotH U P A V q) (act_smul _ _ _).symm

variable (q':IsStarProjection (Dial.spar i_ P.J.M (A V))) (L' : List I)(v:ψS (Cube.node∘σ) L')
include X Z hp v
lemma sleeve_read (f:Rue.FleetS P.p.threshold V.1)(M':I→ FC (Single (mid N B)))(pM:L'.Pairwise (fun i j=>Commute (M' i) (M' j)))(w:L'.length ≤ k)
    (ht:∀ z∈hill I,∀ X: Wave (Dwell Ω),pilotH U P A V q' (acts (∑ Y:Aura Ω,M z V Y) X)=acts (Liss.waveΦ M' z) (pilotH U P A V q' X)) :
    tipI (fun z=> denZ (color_b P P.beta (P.F+ awake (O) (Ls τ) Q z) P.slip (P.K+ QΨ z) (P.v+α_ξ t z)) U A V) L'=acts (L'.map M').prod (denZ P U A V) := by
  let Φ(z):= (α_ξ t z) • (1:Cipher Ω); let Yζ(z):= exp (Φ z+exponentL P.p (E' z) V.1) * fueled P.p (P.K+ QΨ z) V
  let Yk(z:Key I):= exp (Φ z+ exponentL P.p (JΦ z) V.1)*fueled P.p (P.K+(Ψf z-Ψf 0)) V; let H:= pilotH U P A V q'
  let Z':Cipher Ω→ₗ[ℂ] Phys Ω:= ⟨⟨fun i=>H (Cadre.poseL _ i),fun x y=> (congrArg (fun v=>H v) (act_add ..)).trans (map_add ..)⟩,fun x y=> (congrArg (fun v=>H v) (act_smul ..)).trans (map_smul ..)⟩
  let G:= Z'.toContinuousLinearMap
  have g(z:Key I):denZ (color_b P P.beta (P.F+E' z) P.slip (P.K+ QΨ z) (P.v+α_ξ t z)) U A V=G (Yζ z):= switched U A V (E' z) (P.K+ QΨ z) _ q'
  let D(z:Key I):=H (poseL _ (hGas (flags P.p.threshold V.1) (hailV (flags P.p.threshold V.1) (T z) V)))
  have p1:River Φ:=by
    let K':= rer_C (fun i:I=>t i)
    exact (show River (fun z:Key I=>Rep_C (fun i:I=>t i) z • (1:Cipher Ω)) from (κscale K' (zeroR _))) -- tune
  have BV:Soft L' (fun z=> G (Yk z)) (fun i=> G (Yζ i)) := by
    have he:=(Soft.plus (show Soft L' Φ Φ from ⟨p1,p1,fun _ _=>rfl⟩) (send_era K C σ X Q c Fv t Z τ hp V L' v))
    let p:=uS_b (O) v
    have hg:=(Soft.mul (Soft.expΩ he p) (castFuel (P:=P.p) _ _ (fun i v=> (flows_cup K C σ X k Fv hp (fun i=>(Z i).stout) i).2 v) L' v P.K V) p).graph G
    -- only need tip result; drop D.Soft
    exact hg
  rw [funext g, ←BV.tip L' (List.Sublist.refl _), show tipI (fun z=> G (Yk z)) L'=tipI D L' from ?_]
  swap; · symm; refine lace_C L' ?_ roots; exact fun i v=> congrArg H (congrArg (fun x:Cipher Ω=> Cadre.poseL _ x) (lust_cash K C σ X Q c Fv t Z τ hp V f i v))
  let y:= H (poseL _ (hGas (flags P.p.threshold V.1) (hailV (flags P.p.threshold V.1) (settleK P.K) V)))
  have k':tipI D L'=acts (L'.map M').prod y:= (concreteTip (settleK P.K) r X.pigment K _ X.price (zero_le_one.trans hp) V f X.gamb H _ L' k w ht).trans (Liss.ketTip M' L' (uS_b _ v) pM y)
  rw [k']; apply congrArg (acts _)
  have hr:= showUp (R:=P) U A V q' 0 P.K
  have hh:exponentL P.p 0 V.1=0:=by simp [exponentL,numbE]
  unfold y; rw [hh,exp_zero,one_mul,add_zero] at hr
  rw [totGas C P.K K (O) n M X hp, settleSelf V f]; exact hr.symm
end YM.CF.Vow.TreasuryFog
