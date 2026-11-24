import YM.CF.Vp929.Kinematic.Torso
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
namespace Lid
variable (H: Lid o p p' f)
variable {F F': Corr (Scree.mid n B)}
local notation "τ"=> radiusB x
variable (Mk: Monk SU.group (w.step V))(A₀:Ids (Scree.mid m B))(T₁:Ids (Scree.mid n B))
local notation "Rc" v:max=> poleY Mk v (Scales.y SU.group R.L x)
local notation "Δ" => (o.muster.post+90)*radiusB x
local notation "Δ₀"=> (D.pilot.hat R x)
local notation "χ"=> (shotM o.muster.vita)
variable (hF:Location.gross p' D f F)
variable {X X':Pilot}
local notation "θ"=> (vast (k:=D.Z.N1*τ) A')
local notation "Μ"=> Cipher ι
local notation "Λ" z:max l:max=> (H.lantern Mk A₀ T₁ z l hF)
local notation "Tt"=> o.muster.trot
local notation "Tr"=> o.muster.room
local notation "Tx"=> o.muster.post
variable (t:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)))
local notation "B0"=> (penn S' t)
local notation "Hk" z:max l:max=> (Λ z l).stageT x Tx t
variable (l z:ℂ)
-- multiplicative Frozen accounting
def quanta := ∑ j∈ liftK S' t.toLeft, Fintype.card (Frozen j.val x Mk.park)
local notation "Φ"=>l⁻¹^(quanta (x:=x) Mk t)
local notation "p0"=> (Up β).post
lemma brew_quanta: (Λ z l).brew t = Φ • (Λ z 1).brew t:= by
 unfold Eire.Dress.brew; dsimp only
 let Jx(j:Hos S' z'):= Fintype.card (Frozen j.val x Mk.park); let Yx:= penn S' t; let B'(i:Hos S' z'):= H.jewel Mk A₀ T₁ Yx i z; let Fq:= ∏ j∈t.toRight.toRight,H.crown Mk A₀ T₁ Yx j z
 change (∏ i∈ liftK S' t.toLeft,(l⁻¹^(Jx i)) • B' i)*Fq=Φ • ((∏ i∈ liftK S' t.toLeft,((1:ℂ)⁻¹^ (Jx i)) • B' i)*Fq); simp only [inv_one,one_pow,one_smul]; rw [Finset.prod_smul, Finset.prod_pow_eq_pow_sum,Algebra.smul_mul_assoc]; rfl
lemma blazon_quanta (S0: Ride (w.step V)): (Λ z l).blazon x Tx t S0= Φ • (Λ z 1).blazon x Tx t S0:= by
 let D:= Φ; let E(a):= Λ z a; let U(a):= Hk z a; have hg : vig (U l)= D • vig (U 1):= by
    ext1 i; apply Subtype.ext; unfold vig; change tempo (U l) i= _ • tempo (U 1) i; unfold Scion.tempo; split
    next h=>
      have he:=H.brew_quanta Mk A₀ T₁ hF t l z; let W:=U 1; change issue (W.knots i) W.voice (W.rhythm i) * ((Λ z l).brew t).val= _; rw [he]; exact Algebra.mul_smul_comm ..
    rw [smul_zero]
 rw [H.cap_t,H.cap_t]; split; next h=>change reconL.symm (vig (U l)) S0= _; rw [hg,Mew.recon_smul]; rfl
 rw [smul_zero]
section
-- Along holomorphic trajectories, testing every value (not claiming gauge dependence)
variable {Uq:Set ℂ}
variable {G:ℂ→ Corr (Scree.mid n B)} {a b:ℂ→ℂ}
variable (g: ∀ z,Location.gross p' D f (G z))
variable (df:∀ i U,DifferentiableOn ℂ (fun z=>(G z).1 i U) Uq) (dg:∀ i U,DifferentiableOn ℂ (fun z=>(G z).2 i U) Uq)
local notation "uJ" z:max => H.lantern Mk A₀ T₁ (a z) (b z) (g z)
include H df dg
private lemma op_holo(i:Rust η): DifferentiableOn ℂ (fun z=> OpK S' x (Ys y (G z)) (Rc y) T₁ Jq Tt Tr Tx i) Uq:=by
 let M:=Rc y; let S:= M.sent x Jq Tt Tr Tx y; let V(S0):=warmY S' (Ys y 0) M S0; let ηq(S0):=guardB S' x (Ys y 0) M Jq Tt Tr Tx S0
 cases i with
 | inl i=>
    change DifferentiableOn ℂ (fun z=> if V (i.1.val.2) then ηq (i.1.val.2) • (exp (if i.2 then (G z).1 i.1 S else 0)-1) else (0:Cipher η)) Uq; split; swap; · exact differentiableOn_const _
    simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    have h: DifferentiableOn ℂ (fun z=> if i.2 then (G z).1 i.1 S else 0) Uq:= by split;exact df _ _; exact differentiableOn_const _
    exact DifferentiableOn.smul (differentiableOn_const (𝕜:=ℂ) (s:=Uq) (↑(ηq i.1.val.2):ℂ)) (((show Differentiable ℂ (exp (𝔸:=Cipher η)) from fun x=>(NormedSpace.exp_analytic x).differentiableAt).comp_differentiableOn h).sub (differentiableOn_const _))
 | inr i=>
    let E:= i.val.1.val.2\i.val.2; change DifferentiableOn ℂ (fun z=> if V E then ηq E • (G z).2 i (S,T₁) else 0) Uq; split; swap; · exact differentiableOn_const _
    simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact DifferentiableOn.smul (differentiableOn_const (𝕜:=ℂ) (s:=Uq) (↑(ηq E):ℂ)) (dg i (S,T₁))
lemma blazon_curve (ha:DifferentiableOn ℂ a Uq)(hb:DifferentiableOn ℂ b Uq)(hv:∀ z∈Uq,b z≠0) (S0: Ride (w.step V)): DifferentiableOn ℂ (fun z=> (uJ z).blazon x Tx t S0) Uq:= by
 simp_rw [cap_t]; split; swap; · exact differentiableOn_const _
 let M(z:ℂ):= uJ z; let Pq(z):= (M z).stageT x Tx t; refine Mew.vigor_holo Pq Uq (fun p=>?_) S0
 refine Mew.tempo_holo Pq Uq ?_ (fun z=> ?_) (fun z=> ?_) ?_
 · have he:DifferentiableOn ℂ (fun z=> (M z).bodyL x Tx t) Uq:= by
      unfold Eire.Dress.bodyL Eire.lure; apply DifferentiableOn.fun_finsetProd; intro i e; exact H.op_holo (Eire.trot S' Mk B0) T₁ df dg i
   have e := (Mew.sheen (T:= Dwell η)).differentiable.comp_differentiableOn he; exact e
 · have hx: (M z).blocks B0= (M 0).blocks B0:= (H.qori _ _ _ H.living H.living (H.crew y H.living).1 (H.crew y H.living).1 (H.choice H.living (g z)) (H.choice H.living (g 0)) B0).2
   change (M z).heatT t p=(M 0).heatT t p; unfold Eire.Dress.heatT Eire.Dress.coats; rw [hx]; rfl
 · let f(Pq:Rill.Arch w.G d):= Eire.paint S' (20*τ) o.bags o.SheepR.dyes Pq.val.1.1 Pq.val.2 T₁ t.toLeft (Plume.walksK T₁); exact congrArg f ((H.qori _ _ _ H.living H.living (H.crew y H.living).1 (H.crew y H.living).1 (H.choice H.living (g z)) (H.choice H.living (g 0)) B0).2)
 have he:DifferentiableOn ℂ (fun z=> (M z).brew t) Uq:= by
    unfold Eire.Dress.brew; dsimp only; exact (DifferentiableOn.fun_finsetProd (fun i _=> DifferentiableOn.smul ((hb.inv hv).pow _) ((H.jewel_p Mk A₀ T₁ B0 i).entire.comp_differentiableOn ha))).mul (DifferentiableOn.fun_finsetProd (fun i _=>(H.crown_p Mk A₀ T₁ B0 i).entire.comp_differentiableOn ha))
 have e := (Mew.sheen (T:= Dwell ι)).differentiable.comp_differentiableOn he; exact e
omit df dg
lemma blazon_entire(S0: Ride (w.step V)):Differentiable ℂ (fun z:ℂ=> (Λ z 1).blazon x Tx t S0):= differentiableOn_univ.mp (H.blazon_curve (G:=fun _=>F) (a:= _root_.id) (b:=fun _=>1) Mk A₀ T₁ t (fun _=>hF) (fun _ _=>differentiableOn_const _) (fun _ _=>differentiableOn_const _) differentiableOn_id (differentiableOn_const _) (fun _ _=>one_ne_zero) S0)
end
end Lid
end Pitching
end YM.CF.Py.Rate
