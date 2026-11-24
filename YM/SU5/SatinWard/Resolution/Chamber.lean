import SatinThinMonarch
import YM.SU5.Exchange.Force.Jets
import YM.SU5.SatinWard.Resolution.Character
/-!
# The same actual OrbitJet step, now giving X/W-character income on all layouts.

In particular: one response in the **character sector**, common across upper
allocations, arities, locations and labels of the same theme. Retaining flag
widths. Extends SatinThin{Foyer (in Register),Topic,Novella,Script,Monarch}.
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
local notation "TF"=> mid P B
local notation "Tc"=>mid N B

open Oise Rive
structure Theme(n:Side)(χ:SweepSign n) where
 face: Site n → RegBudget n → ForceBudget n → Prop
 color: ∀ (s:Sweep n),s∈χ.group→∀ x y E V F W, Earlier s x y→face x E F→ face y V W→ passingR n s E (χ.sgn s • V) ∧ passingF n s F (χ.sgn s • W)

structure Grows {n m:Side}(A:Ratio n m)(χ:SweepSign n)(ψ:SweepSign m):Prop where
 into(s:Sweep n)(h:s∈χ.group): reSweep A s ∈ ψ.group
 liftSign(s:Sweep n)(h:s∈χ.group): ψ.sgn (reSweep A s)=χ.sgn s

def SweepSign.Eigenspace {n:Side}(χ:SweepSign n)(Z:ArcΦ): Prop:=∀ g∈χ.group,turnD g Z=χ.sgn g • Z

def SweepSign.KillsScalar {n:Side}(χ:SweepSign n): Prop:= ∀ a:Site n→ℂ,SignBent χ tρ a→ a=0

variable {χ:SweepSign (mid N B)}{ψ:SweepSign (mid P B)}(hv:Grows G χ ψ)
variable (U:Observatory G X.p)(F:Theme (mid P B) ψ)(o:Site (mid N B))
variable (σ:ℝ → Cusp (mid N B))
local notation "ST"=> Sweep Tc
-- Ask about current. Single-key only (not returning Ψ yet); u,A not properties of entry here, can select repr and empty-case.
structure LapEvent : Prop where
 bill:∃ E1 K1,F.face (Hove.heel G o) E1 K1∧∀ t:ℝ, |t|≤1→U.source (Y.F+t • E1) (Y.K+t • K1) (σ t)
-- critical `Earlier` torus. hue only along axis.
variable {φ:Sweep (mid N B)}(p:φ∈χ.group)
variable(t:LapEvent (G:=G) X Y U F o σ)
variable (ω₀:Site (mid N B))(τ:ℝ → Cusp (mid N B))(tt:LapEvent (G:=G) X Y U F ω₀ τ)
variable (q1:Odd G.count.val)(a1:∀ s∈ψ.group, passingR (mid P B) s Y.F Y.F)(b1:∀ s∈ψ.group, passingF (mid P B) s Y.K Y.K)(e1:Earlier φ o ω₀)
-- G explicit binder in LapEvent? dependencies through V? print
include hv q1 a1 b1 e1 p t tt
lemma mirrorEvent (k:ℝ)(hk:|k|≤1): MirrorBill Tc X.p φ (σ k) (τ (k*χ.sgn φ)):=by
 obtain ⟨E0,K0,g0,f0⟩:=t.bill; obtain ⟨E1,K1,g1,f1⟩:= tt.bill
 let z:=reSweep G φ; let r:= hv.into φ p; obtain ⟨u,v⟩:= F.color z r _ _ _ _ _ _ (Earlier.goes G q1 e1) g0 g1
 rw [hv.liftSign φ p] at u v; refine U.flies φ _ _ _ _ _ _ (f0 k hk) (f1 _ ((by rw [abs_mul,χ.abs_sgn p,mul_one]; exact hk))) ?_ ?_ <;> rw [mul_smul]
 · exact (a1 _ r).add z (u.smul z k)
 exact (b1 _ r).add z (v.smul z k)
omit t tt -- prep derivative
variable (K0:Pax (mid N B))(q0: adorns X.p σ K0)(K1:Pax (mid N B))(u1:adorns X.p τ K1)
include hv q1 a1 b1 e1 t tt u1 p q0
lemma feeEvent : Fρ φ (χ.sgn φ • coldE X.p K1) = coldE X.p K0:=by
 apply turnG φ; intro i U; let Y:= χ.sgn φ; let z(r:ℝ):=r*Y; let C: Cipher (mid N B)→L[ℝ]Cipher (mid N B):=(suit_Y φ).toLinearMap.toContinuousLinearMap; have he: HasDerivAt z Y 0:=by simpa using (hasDerivAt_id' (0:ℝ)).mul_const Y
 let f:=fun x=> shortDose X.p σ x i U; let a:=(moldA φ i); let g:=fun x=> shortDose X.p τ x a (yellA φ U)
 have hu: g ∘ z=ᶠ[𝓝 0] C ∘ f:=by
    filter_upwards [ball_mem_nhds (0:ℝ) one_pos] with x hx
    have hh:= mirrorEvent G X ‹GramM (mid P B)› hv ‹Observatory G X.p› F o σ p t ω₀ τ tt q1 a1 b1 e1 -- notation U shadow actual X? U shadow
    unfold f g z; simp only [Function.comp_apply,shortDose,Pi.sub_apply,map_sub]
    refine congrArg₂ (· - ·) ((hh x (mem_ball_zero_iff.mp hx).le).wax i U) ?_; have ht:=(hh 0 (by norm_num)).wax i U; rwa [zero_mul] at ht
 change Y • _ = C _; have hk:z 0=0:=zero_mul _; exact (((show HasDerivAt g (K1 a (yellA φ U)) (z 0) from hk.symm ▸ u1 a (yellA φ U)).scomp 0 he).congr_of_eventuallyEq hu.symm).unique (C.hasFDerivAt.comp_hasDerivAt 0 (q0 i U))
omit hv q1 a1 b1 e1 p q0 t tt u1
variable (KΦ:Cusp (mid N B))(kZ:ZealQ KΦ)(K': Site (mid N B)→ Cusp (mid N B))(D: Site (mid N B)→ RegBudget (mid N B))(uK:SignBent χ Kρ K') (uD:SignBent χ Eρ D)
local notation "Pe"=> X.p
structure SignalGraph (Fv:ForceBudget (mid N B)): Prop where
 cost : LapEvent G X Y U F o σ
 speaks : ∀ i:Force (mid N B),∀ V:Orbit (mid N B),Function.Injective (priorP V.2)→HasDerivAt (fun t:ℝ=>rust_L X.p (σ t) (KΦ+t • K' o) i V) (Fv i V) 0
include uK uD hv kZ q1 a1 b1
noncomputable def childTheme : Theme Tc χ where
 face x E Fv:=(E=D x ∧ ∃ σ, SignalGraph G X Y U F x σ KΦ K' Fv)
 color:=by
    rintro s p x y _ _ Fu Fv h ⟨rfl,w,t⟩ ⟨rfl,u,z⟩
    have g:=uD s p x y h; refine ⟨Eρ_pass s _ _ (by rw [map_smul,g,smul_smul,χ.sq p,one_smul]),?_⟩
    intro i v hx; let L:= (suit_Y s).toLinearMap.toContinuousLinearMap; let M:=χ.sgn s; let a(r:ℝ):=r*M; have e:HasDerivAt a M 0:=by simpa using (hasDerivAt_id' (0:ℝ)).mul_const M
    let f:=fun r:ℝ=> rust_L X.p (w r) (KΦ+r • K' x) i v; let g:=fun r:ℝ=> rust_L X.p (u r) (KΦ+r • K' y) (moveForce s i) (yellA s v)
    have he:a 0=0:=zero_mul _; have hw: g ∘ a =ᶠ[𝓝 0] L ∘ f:=by
       filter_upwards [ball_mem_nhds (0:ℝ) one_pos] with t' k; apply (mirrorEvent G X Y hv U F x w p t.cost y u z.cost q1 a1 b1 h t' (mem_ball_zero_iff.mp k).le).lamp _ _ _ _ v hx
       unfold a; rw [mul_smul]; apply passingU_n.add _ (fun i x p X v l=> kZ _ x p i X v l); apply passingU_n.smul; refine no_pr _ _ _ _ (Kρ_pass _ _ _ ?_); rw [map_smul,uK s p x y h,smul_smul,χ.sq p,one_smul]
    let Yv:=yellA s v; have hp:Injective (priorP (Yv).2):=by
       intro i j h; apply (boxA s).injective; exact hx h -- prior of bun tusk?
    exact (((show HasDerivAt g _ (a 0) from he.symm ▸ (z.speaks _ _ hp)).scomp 0 e).congr_of_eventuallyEq hw.symm).unique (L.hasFDerivAt.comp_hasDerivAt 0 (t.speaks i v hx))

omit hv uK uD kZ q1 a1 b1

variable (Ca:ArcΦ→ℝ→ℝ)(α:ℝ)(R:ArcΦ)(κ:ℝ)(vκ:∀ x: Site (mid P B), nun_ω Y.F x=κ)(hs:0≤h)(vH:HavenL (mid N B) X.p l.L.val)
def Opportunity (l:Patch)(x:Site (mid N B))(U':Pax (mid N B)): Prop:= LapEvent G X Y U F x σ∧ adorns X.p σ U'∧ ∃ E K z Y', Ice l.L.val x X.p h (W*κprobe mintR l.L h α T (κ:ℂ) R) (Ca R α) (C*κprobe mintR l.L h α T (κ:ℂ) R) (coldE X.p U') E K z Y'∧ αPrice l.L h α T BQ Rt Zt R Y' X.p Y.p (κ:ℂ)
local notation "OK" x:max σ:max A:max => Opportunity G X Y h T W C BQ Rt Zt U F σ Ca α R κ l x A
local notation "RR"=>κprobe mintR l.L h α T (κ:ℂ) R
open SweepSign
include hv hs vH q1 a1 b1
set_option maxHeartbeats 280000
lemma finance_theme (H:∃ x σ A, OK x σ A)(p:χ.Eigenspace R)(h_:χ.KillsScalar):
  ∃ (S:ArcΦ)(E: Site (mid N B)→ RegBudget (mid N B))(K':Site (mid N B)→ Cusp (mid N B)),
    InΦ S ∧ χ.Eigenspace S ∧ SignBent χ Eρ E ∧ SignBent χ Kρ K' ∧
    αPrice l.L h α T BQ Rt Zt R S X.p Y.p (κ:ℂ) ∧
    ∀ x σ A, LapEvent G X Y U F x σ → adorns X.p σ A →
      Ice l.L.val x X.p h (duty_Q X.p.order X.p.power*(W*RR)) (strive_E X.p.order*Ca R α) (C*RR) (coldE X.p A) (E x) (K' x) 0 S := by
 obtain ⟨x,σ₀,A,h,z,u,K',ξ,D,he,hl⟩ := H; let a:=coldE X.p A; let X':=orbitAverage Fρ x χ a; let Z:=alleyS x χ turnD D x
 have hero (y:Site Tc)(σ:ℝ → Cusp Tc)(A':Pax Tc)(t:LapEvent G X Y U F y σ)(p:adorns X.p σ A'):
     X' y=coldE X.p A':=by
    have p : ∀ s∈ ways χ y x, Fρ s (χ.sgn s • a)=coldE X.p A' := fun s hs'=>
       feeEvent G X Y hv U F y σ ((ways_iff ..).1 hs').1 t x σ₀ h q1 a1 b1 ((ways_iff ..).1 hs').2 A' p A z
    unfold X' orbitAverage alleyS; simp_rw [←map_smul]; rw [sum_congr rfl (fun i u=> p i u),sum_const,← Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ (by exact_mod_cast (card_pos.mpr (anyWay χ y x)).ne') _
 let H:=orbitAverage Eρ x χ u
 obtain ⟨r,w⟩:=average_ice χ vH x hs a u K' ξ D he
 refine ⟨Z,H,orbitAverage Kρ x χ K',?_,r,orbitAvg_E χ x u,orbitAvg_K χ x K', reprice_alpha χ x R D p _ _ _ _ _ _ _ _ _ κ hl,fun y τ Ux Hy hm=>?_⟩
 · apply claim_T _ _ _ vH.door Z (H x) (w x).axle vH.pay hs -- tune abi
 have h:=w y; change Ice _ _ _ _ _ _ _ (X' y) _ _ _ _ at h; rw [hero y τ Ux Hy hm,h_ _ (orbitAvg_t χ x ξ)] at h; exact h
omit hv hs vH q1 a1 b1
variable {J0 flags:ℕ}
lemma opportunityAt (Uκ:OrbitJet V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp U KΦ Ca flags J0)
    (r:J→Site (mid N B))(E:Key J→RegBudget (mid P B))(F':Key J→ForceBudget (mid P B))(j:J)(R:J→ ArcΦ) (a:J→ℝ)
    (t:OrbitPulse G X Y h b g l.L r E F' R a J0)(t':F.face (Hove.heel G (r j)) (νTip E j) (emberTip F' j)) (vκ:∀ x: Site (mid P B), nun_ω Y.F x=κ):
    ∃ σ A, Opportunity G X Y h T W C BQ Rt Zt U F σ Ca (a j) (R j) κ l (r j) A := by
 obtain ⟨Fv,v',hξ,k,_⟩:= Uκ.heat r E F' R a t
 refine ⟨Fv ∘ realKey j,opTip (heat_P X.p Fv) j, ?_, tip_now Fv X.p hξ j,?_⟩
 · refine ⟨νTip E j, _, t', fun x u=>?_⟩
   rw [←t.buy.rail.1,←t.buy.rail.2.2,←t.north j x u,←t.south j x u]; exact v' _ (realKey_mem j x u)
 let W':=k j; dsimp only at W'; rw [vκ] at W'; exact W'

include hv vH hs q1 a1 b1 vκ
/-- Choose common lower shapes and themes BEFORE allocating a layout. Label schedules
and their appointment are fixed for the step. `R0` is a sample layout exercising each theme;
no conclusion for nonexistent programs. -/
lemma coherent_step (Uκ:OrbitJet V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp U KΦ Ca flags J0)
    {ι:Type} {I:Type}[LinearOrder I][Fintype I]
    (R0:I→Site (mid N B))(E0:Key I→RegBudget (mid P B))(F0:Key I→ForceBudget (mid P B))
    (theme:ι→Theme TF ψ)(Z:ι→ ArcΦ)(a:ι→ℝ)(J':I→ι)(tz:OrbitPulse G X Y h b g l.L R0 E0 F0 (Z∘J') (a∘J') J0)
    (all:Surjective J')(Q:∀ i,(theme (J' i)).face (Hove.heel G (R0 i)) (νTip E0 i) (emberTip F0 i))
    (p:∀ i,χ.Eigenspace (Z i))(h_:χ.KillsScalar):∃ (X':ι→ArcΦ)(φ:ι→ Theme Tc χ),
    (∀ i, InΦ (X' i) ∧ χ.Eigenspace (X' i) ∧ αPrice l.L h (a i) T BQ Rt Zt (Z i) (X' i) X.p Y.p (κ:ℂ)) ∧
    ∀ {J:Type}[LinearOrder J][Fintype J](r:J→Site (mid N B))(D:Key J→RegBudget (mid P B))(F':Key J→ForceBudget (mid P B)) (j:J→ι),
      OrbitPulse G X Y h b g l.L r D F' (Z∘j) (a∘j) J0 →
      (∀ i,(theme (j i)).face (Hove.heel G (r i)) (νTip D i) (emberTip F' i))→
      ∃ E K', Cause_P V P_ G S G₀ G₁ X Y D 0 F' Xp q d h Vp Vf r (a∘j) (Z∘j) E K' (X'∘j) 0 T (duty_Q X.p.order X.p.power*W) C BQ Rt Zt κp ∧
        (∀ z∈hill J,FlagWidth X.p (K' z) flags) ∧ ∀ i,(φ (j i)).face (r i) (νTip E i) (emberTip K' i):=by
 have commission(i:ι):∃ x σ A, Opportunity G X Y h T W C BQ Rt Zt U (theme i) σ Ca (a i) (Z i) κ l x A:=by
    obtain ⟨j,rfl⟩:=all i; exact ⟨R0 j, opportunityAt V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp U (theme (J' j)) KΦ Ca κ Uκ R0 E0 F0 j (Z ∘ J') (a ∘ J') tz (Q j) vκ⟩
 choose X' E H t v p1 p2 k W' using fun i:ι=> finance_theme G X Y h T W C BQ Rt Zt hv U (theme i) q1 a1 b1 Ca (a i) (Z i) κ hs vH (commission i) (p i) h_
 refine ⟨X',(fun i=> childTheme G X Y hv U (theme i) q1 a1 b1 KΦ Uκ.light (H i) (E i) (p2 i) (p1 i)),(fun i=>⟨t i,v i,k i⟩),?_⟩
 intro J _ _ r D F' j pay qualifies
 obtain ⟨Fv,v',hξ,uK,c⟩:=Uκ.heat r D F' _ _ pay
 let Eᵪ(i:J):=E (j i) (r i); let Kᵪ(i:J):=H (j i) (r i)
 have kit(i:J): LapEvent G X Y U (theme (j i)) (r i) (Fv ∘ realKey i):=by
    refine ⟨_,_, qualifies i,fun x u=>?_⟩; rw [←pay.buy.rail.1,←pay.buy.rail.2.2,←pay.north i x u,←pay.south i x u]; exact v' _ (realKey_mem _ _ u)
 obtain ⟨A,Bx,Y',T'⟩:= c Eᵪ Kᵪ (X' ∘ j) 0 (fun i=> by
    dsimp only; rw [vκ]
    exact ⟨W' (j i) (r i) (Fv ∘ realKey i) _ (kit i) (tip_now Fv X.p hξ i), k (j i)⟩)
 let Kν(z):=rust_L X.p (Fv z) (KΦ+Φstack Kᵪ z); refine ⟨A,Kν,Bx,Y',fun i=>?_⟩
 refine ⟨T' i,Fv ∘ realKey i,kit i,?_⟩
 intro Z x p; let f(t:Mew.Key J):=Kν t Z x; have hv:= tip_real f i ((Bx.tape Z).2 x); exact hv.congr_of_eventuallyEq (Eventually.of_forall fun t'=>congrArg (fun V:Cusp (mid N B)=> rust_L X.p (Fv _) (KΦ+V) Z x) (stack_axis Kᵪ t' i).symm)
end YM.CF.QuadClock
