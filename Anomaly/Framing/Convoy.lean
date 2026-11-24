import Anomaly.Framing.Round
import Anomaly.Framing.Peers
import YM.CF.Scree.Locus
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Swell
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry Vow
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Paige Salt Phase Acorn Nacre Dial Urn Laic Skye Scree Stax Sour Sault Rill Ione Py QuadClock Turning Levier
variable {B C L:Side}{Z M:SOp C}{o:Seat C}{a b c d v s t r₀ r₁ r₂ r₃:ℝ}{n l q j:ℕ}{p:RG.BudgetPoint}
variable {h:Odd L.val}{H:Paige.Pricing j L h (Vault.Thread j)}{e:ℝ}(P:Grasp H B e)
open Vow.TreasuryFog
local notation "N"=> mid C B
variable (R:GramM (mid C B))(K:Scree.Loom (mid C B))
variable {k m:ℝ} {V:phy (mid C B)} (u:Roof (mid C B) k e q K) (z:P.roundZ≤ (mid C B).val)

lemma invariant_reg {A:RegBudget (mid C B)} (s:Sweep (mid C B))(h:passingR (mid C B) s A A)(V:Orbit N): suit_Y s (exponentL p A V.1)=exponentL p A (yellA s V).1:=by
  rw [←force_r _ s A V]; rw [show base_Q s A=A from ?_]
  funext i W; unfold base_Q step_F; simp only [Function.comp_apply,h i W]; rw [moon_Y,mul_inv_cancel,toon_Q]; -- tune

open scoped Mew
variable {J : Bag (mid C B)}
-- carrier version suppress arbitrary coefficient of betaL. retag readings still keep actual beta!
abbrev pod (P:Grasp H B e)(R:GramM (mid C B))(K:Scree.Loom (mid C B))(x:Orbit (mid C B))(h:IsStarProjection (spar j R.J.M (K x)))(y:Wave (Dwell (mid C B))) : Phys (mid C B):= ballL (nursery _ h) (relV P R.J (K x)) (acts (exp (exponentL R.p R.F x.1+exponentL R.p R.slip x.1)).val y)

lemma link_stance (V':Orbit (mid C B))(t:IsStarProjection (spar j R.J.M (K V')))(x:Wave (Dwell (mid C B))) : pilotH P R K V' t x= (Complex.exp (R.betaL K V')) • pod P R K V' t x:=rfl

abbrev priorNice (x:Orbit N):Prop:=Injective (priorP x.2)

def nestLink (P:Grasp H B e)(R:GramM (mid C B))(K:Scree.Loom (mid C B))(J:Bag (mid C B))(V:phy (mid C B)): Prop:=∀ V':Orbit (mid C B), priorNice V' → ∀ h:IsStarProjection (spar j R.J.M (K V')),∀ p': Wave (Dwell (mid C B)),pilotH P R K V' h (acts (∑ i:Aura (mid C B), J i V') p')= acts (V V') (pilotH P R K V' h p')

def cartPrice {n:Side}(s:Sweep n)(V:phy n) : phy n := fun x=>Hive.teen s (V (yellA s⁻¹ x))
lemma pinject (s:Sweep (mid C B))(x:Orbit N)(v:priorNice x):priorNice (yellA s x):= fun i j h=> (boxA s).injective (v h)

variable (p':Pearl P)(vP:Vault.Stamped j L h H)(vt:1≤j)(A:R.J.P.toll r₀ r₁ r₂ r₃)(F:Reef.Cry R.J.P)
include p' vP vt A F u z
lemma link_framed (s:Sweep N)(g:passingR (mid C B) s R.F R.F)(w:R.slip=0)
    (pK:nestLink P R K J V) : nestLink P R K (cartTurn s J) (cartPrice s V) := by
  intro x t₀ y p
  obtain ⟨x,rfl⟩:=yspec s x; let B:=yellA s x; let W:= K x; let K':=K B; have hx:priorNice x:=fun i j v=> (boxA s).symm.injective (t₀ (show priorP B.2 ((boxA s).symm i)=_ from (by change priorP x.2 (boxA s ((boxA s).symm i))=priorP x.2 (boxA s ((boxA s).symm j)); rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,v])))
  have hp: Guard W e := u.paid x
  have hk:K'=stir (xtra s.charge) (castX s) W:=by
    unfold K' W B; rw [show K (yellA s x)=flashA s (K x) from (u.move _ _ _ hx)] -- tune ..
    rfl
  let α:= spar j R.J.M W; let a':=spar j R.J.M K'
  have hv: IsStarProjection α:= (P.broadness _ z R.J.M).projection W hp
  let c:= s.charge; let r:= detX s.s; let U:=γS s; let D:= angelK (Scree.spice U r) (c.xor r); let H':= arum U c r (mateK _)
  have e_: sings c U α=swapX r a':=by
    unfold a'; rw [hk]; exact funde_f _ _ _ (spinZ c s.s) _ _ vt _ _ (vP.fields_one _ (P.needed.trans z)) (hp.shrink P.gem)
  have hz: H' (relV P R.J W)=relV P R.J K':=by
    unfold H'; rw [hk]; exact Hive.birds c p' vP z vt (castX s) (spinU c s.s) (spinZ c s.s) R.J.P A F W hp -- tune
  have he(x:Orbit N):exponentL R.p R.slip x.1=0:= by rw [w]; simp [exponentL,numbE]
  let T:=(suit_Y s); let E:=exponentL R.p R.F x.1
  have ht:E=exponentL R.p R.F x.1:=rfl
  have hy:exp (exponentL R.p R.F B.1)=T (exp E):=by
    letI :NormedAlgebra ℚ (Cipher N):= NormedAlgebra.restrictScalars ℚ ℂ _
    rw [←invariant_reg s g x,map_exp]; exact T.toLinearMap.continuous_of_finiteDimensional
  have hP(Z:Wave (Dwell N)): H' (pod P R K x hv Z)=pod P R K B y (D Z):=by
    change H' _=ballL (nursery a' y) (relV P R.J K') _
    unfold pod; rw [he x,he B,add_zero,add_zero]; rw [hy]; unfold H'; rw [ball_hover hv y c r U e_, show arum U c r (mateK _) (relV P R.J (K x))=_ from hz, angel_act c r U]; rfl
  let Dg:= Complex.exp (R.betaL K x)
  obtain ⟨f,rfl⟩:= angel_sur (Scree.spice U r) (c.xor r) p
  set β:= ∑ i:Aura N, J i x with he'
  let β':=∑ i:Aura N, cartTurn s J i B
  have A': sauce c r U β=β':=by
    unfold β'; rw [he']; change lotY _ _ _ _=_; rw [map_sum]; exact sum_equiv (moldA s) (by simp) (fun i _=> (runs s J x i).symm)
  have jK:= pK x hx hv f; rw [link_stance,link_stance,map_smul] at jK
  have hs: H' (pod P R K x hv (acts β f))= H' (acts (V x) (pod P R K x hv f)):= congrArg H' (mark_ext (c:=Dg) (Complex.exp_ne_zero _) jK)
  have e: acts (cartPrice s V B) (H' (pod P R K x hv f))=H' (acts (V x) (pod P R K x hv f)):=by
    have h:yellA s⁻¹ B=x:=Prod.ext (revB ..) (tuftT ..)
    rw [cartPrice,h]; exact (arum_act ..).symm
  rw [←e,hP, show H' _= _ from (hP f)] at hs
  have ht: D (acts β f)=acts β' (D f):= (angel_act c r U β f).trans (congrArg (fun k:FC (Dwell N)=>acts k (D f)) A'); rw [ht] at hs
  rw [link_stance,link_stance,map_smul]; exact congrArg ((Complex.exp (R.betaL K (yellA s x))) • ·) hs
end YM.CF.Swell
