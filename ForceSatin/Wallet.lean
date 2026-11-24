import ForceSatin.Pocket
import ForceSatin.RealMean
import YM.SU5.FiniteGaugeData.Tapestry.Neutral
import YM.SU5.FiniteGaugeData.Tower.Reflect
import YM.SU5.Six.RawWard
set_option autoImplicit false
set_option maxHeartbeats 520000
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey
open Loaves Satin Tapestry Six
local notation "⚝" => Lamour.alleyR
-- wallet: entirely on real-profile families before paying any rotations or other Motion
variable {K:Calibration} {F F':Buffered.Family K}{S D:Finset Cover}{m m':ℕ} {a a':ℝ}

structure Wallet (K:Calibration) (F: Buffered.Family K)(S:Finset Cover)(m:ℕ) (a:ℝ) : Prop where
 exam : InTest K false S false F
 purity : LinkIndependent K F
 gauge : Neutral K F
 lane (N:Side) : Street ((Satin.region S (K.c N))) m a (F N (1,1))
namespace Wallet
-- algebra used for all ROOT q_Z(s) comparator words
theorem augment (p:Wallet K F S m a)(h:S⊆D)(e:m ≤ m')(l:a ≤ a'): Wallet K F D m' a':=⟨p.exam.mono h,p.purity,p.gauge,fun N=>Street.enlarge l e ((p.lane N).mono (Finset.image_mono (wrap _) h))⟩
theorem times (p:Wallet K F S m a)(h:Wallet K F' S m' a'):Wallet K (F*F') S (m+m') (a*a'):= ⟨.mul p.exam h.exam,p.purity.mul' h.purity,fun i g U=>by simp_rw [Pi.mul_apply]; rw [p.gauge i g U,h.gauge i g U,map_mul],fun i=>(p.lane i).mul (h.lane i)⟩
theorem plus (p:Wallet K F S m a)(h:Wallet K F' S m a'):Wallet K (F+F') S m (a+a'):=⟨p.exam.add h.exam,p.purity.plus' h.purity,fun i g U=>by simp_rw [Pi.add_apply]; rw [p.gauge i g U,h.gauge i g U,map_add],fun i=>(p.lane i).add (h.lane i)⟩
theorem scale (p:Wallet K F S m a)(z:ℂ):Wallet K (z • F) S m (‖z‖*a):=⟨p.exam.smul z,p.purity.scale' z,fun i g U=>by simp_rw [Pi.smul_apply]; rw [p.gauge i g U,twist_scalar],fun i=>(p.lane i).scale z⟩
theorem one (K:Calibration)(S:Finset Cover):Wallet K 1 S 0 1:=⟨InTest.one,LinkIndependent.one',fun _ _ _=> (map_one _).symm,fun _=> Street.one⟩
theorem flipFront (p:Wallet K F S m a)(i:Axis)(z:ℤ):Wallet K (Tower.mirror K i z F) (Tower.reflectedBox i z S) m a:= by
 refine ⟨Tower.axial K i z p.exam,(fun n _ _=> congrArg (theta _) (p.purity n _ _)), fun n=>covariant_reflected (p.exam.support _) (p.gauge n) z i,fun N=>?_⟩
 let v:=K.c N; change Street _ _ _ (theta _ (F N _))
 rw [p.purity N _ (1,1)]; unfold Tower.reflectedBox Satin.region; rw [Finset.image_image]
 let A:=Buffered.plane i z
 have he:= (p.lane N).reflect i z
 let u:=⇑(wrap (More v)); unfold Satin.region at he; rw [Finset.image_image] at he; rw [show ⇑(wrap (More v)) ∘ A.motion = (A.anon v) ∘ u from (funext (fun x=>(Shape.anno ..).symm))]; exact he
end Wallet
lemma over_K {V U:Side} (g:K.c U=V)(L:List Wine)(p:Wallet K F S m a)(l:F=dek K L) :
 (g▸F U:Mark V)=quietCon _ (motet V L (1,1)) ∧ AtSupport false (Satin.region S V) (quietCon _ (motet V L (1,1))) ∧
   covariant (quietCon _ (motet V L (1,1))) ∧ Street (Satin.region S V) m a (motet V L (1,1)):=by
 subst V; subst F; let Y:=dek K L U; refine ⟨(funext fun i=> p.purity _ i (1,1)), ?_⟩; rw [← (show Y = quietCon _ (motet (K.c U) L (1,1)) from (funext fun i=> p.purity _ i (1,1)))]; exact ⟨p.exam.support _,p.gauge _,p.lane _⟩

def WidthBudget (S:Finset Cover) (u:ℕ) := ∃ s:Cover,∀ i∈S, ∀ k:Axis,s k ≤ i k ∧ i k ≤ s k+u
lemma regionWallet (p:WidthBudget S m)(N:Side) : ∀ i:Axis, cows i (Satin.region S N) m:=by
 obtain ⟨s,p⟩:=p; intro i; refine ⟨s i,fun y v=>?_⟩; obtain ⟨x,e,rfl⟩:=mem_image.mp v; exact ⟨x i,(p x e i).1,(p x e i).2,rfl⟩
open BProof (scaleY)
def budgetWidth (x:ℝ)(u:ℕ):= Nat.ceil ((scaleY x)^u)
lemma budgetStation (K:Calibration)(u:ℕ) : ∀ᶠ x:ℝ in atTop,
   (↑(4*(budgetWidth x u+addgap K):ℕ):ℝ)^4 ≤ poseTill x := by
  have he:Grade 0 (fun x=> (scaleY x)^u):=by simpa only [zero_mul] using Grade.pwr (Grade.stock 0 1) u
  have hv: Grade 0 (fun x=> (budgetWidth x u:ℝ)):= Grade.ceil_float he (Eventually.of_forall fun x=> (pow_pos (BProof.coin_pos ..) u).le) le_rfl
  have ht: Grade (0* (4:ℕ)) (fun x=> ((4:ℝ)*((budgetWidth x u:ℝ)+(addgap K:ℝ)))^4):= (Grade.scaleB 4 (hv.plus (Grade.block _))).pwr _
  exact (ht.cost_p (b:=20*micr) (by norm_num [micr])).mono (fun i h=> le_trans (le_of_eq (by norm_cast : (↑(4*(budgetWidth i u+addgap K):ℕ):ℝ)^4=((4:ℝ)*((budgetWidth i u:ℝ)+(addgap K:ℝ)))^4)) ((le_abs_self _).trans h))
-- keeps all EB joint paths, not only eventual_i after eventual_k. copy Cresc
lemma tide_joint (s:ℕ): ∀ (B:ℕ), ∀ᶠ k in atTop,∀ i:ℕ, B≤ (gram Y s i k).J.M.val.val:=by
 let f (s i k:ℕ):=(gram Y s i k).J.M
 have hp (s i k:ℕ)(v:s < Y.uv k): f s i k= upMale P.R.L P.R.odd_side (f (s+1) i k):=by
    let X:= (Y.voyage i).X (Y.uv k); change (X.gram s).J.M=upMale P.R.L P.R.odd_side (X.gram (s+1)).J.M
    rw [← (X.pull.owns s v.le).taste,← (X.pull.owns (s+1) v).taste]; exact ((P.W.arm _ (Y.uv k)).pass s v).grown
 intro b; filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+b)] with k u i; change b ≤ (f s i k).val.val
 induction b generalizing s with
 | zero=> simp
 | succ b ih=>
    have hv:= ih (s+1) (by omega); rw [hp s i k (by omega)]; change b+1 ≤ P.R.L.val*(f (s+1) i k).val.val
    have he:= P.R.coarse; let X:=(f (s+1) i k).val.val; have p:0<X:=(f (s+1) i k).val.property
    change b≤X at hv; change _ ≤ _ * X; have ht:= Nat.mul_le_mul_right X he; omega
-- **EB** stronger: full election with Universal sees Wage in X^-2.5µ. any legacy path, all wallet. Includes beyond fixed width.
variable {H:Real.exp 1≤P.x}{b C:ℝ}(z0:0<b)(q':CF.Papyrus.Franc.postage 4 b)
variable (p0:∀ᶠ s:ℕ in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k→ s≤ Y.uv k→ TiltWorld Y s i k b C)
variable {u v:ℕ→ℕ}{I E}(U:Universal Y H u v I E)
include z0 q' p0 U
lemma weekFunds (m I':ℕ) : ∀ᶠ s:ℕ in atTop,∀ F:Buffered.Family (tent Y H),∀ S, Wallet (tent Y H) F S m (palmCo (ℶ s)) → WidthBudget S (budgetWidth (ℶ s) I') →
   ∀ L:List Wine, F=dek (tent Y H) L → ‖E s F-tallyW L‖ ≤ wane (ℶ s):=by
 filter_upwards [pencil_custody Y z0 q' H p0 m,(turnover P).eventually (budgetStation (tent Y H) I')] with s h hx F S p e L lL
 let K:=tent Y H; let w:= wane (ℶ s); let D:=tallyW L; let S':=budgetWidth (ℶ s) I'; let V(i k):=Journey.sharp Y H s i k F
 have hw(i): ∃ y,legacy Y (u i) (v y):=(cadence Y v U.pick.grow_k _).exists; choose a vY using hw
 let vp(x):= v (a x); have hh:= (U.together s F (Tapestry.broadCompile K S p.exam.widen)).paths a (Eventually.of_forall vY)
 have hhε(ε:ℝ)(t:0<ε): ‖E s F-D‖≤ w+ε:=by
    obtain ⟨n,p'⟩:=trueWine L ε t
    apply le_of_tendsto (hh.sub_const D|>.norm)
    have ht:= U.pick.walks Y H (Eventually.of_forall vY)
    have hn:= U.pick.grow_i.tendsto_atTop
    filter_upwards [ht.eventually h,ht.eventually (tide_joint Y s n),hn.eventually ((count_la Y s).eventually (ownsHalo (by decide:1 ≤ (4:ℕ)))),hn.eventually ((count_grows Y s).eventually_ge_atTop (S'+addgap K+n))] with i h hp t' g
    let x:=u i; let k:=vp i; let N:= count Y s x; let M:=(gram Y s x k).J.M; have hg:S'+addgap K+n ≤ N.val:=g
    have he:Even N.val:=Vale.val_e ..; let W:=t' he; have hs:=spar_fit (M:=M) W.1; obtain ⟨q,uQ⟩:=phoz hs; let A:= motet N L (1,1)
    obtain ⟨T,U₁,V₁,F₁⟩:=over_K (U:=momentm Y x s) (terrain Y H (Y.ir x) s) L p lL
    have hw:= h x W (U.pick.ticket i _ (vY i)) (Satin.region S N) A U₁ V₁ F₁ S' (by change S'+addgap K ≤ N.val; omega) (regionWallet e N) hx q uQ
    let P:= Lamour.alleyR (mateK N) q A; change ‖V x k - D‖ ≤ w+ε
    rw [show V x k - D=(Journey.compass Y x k s (quietCon N A)-P)+(P-D) from (by rw [show V x k=Journey.compass Y x k s (quietCon N A) from congrArg (Journey.compass Y x k s) T]; abel)]; exact (norm_add_le ..).trans (add_le_add hw (p' _ _ (by omega) (hp _) he hs q uQ))
 by_contra! v; change w< ‖E s F-D‖ at v; have ht:=hhε _ (half_pos (sub_pos.mpr v)); linarith
lemma wiseFunds (m I':ℕ) : ∀ᶠ s:ℕ in atTop,∀ F:Buffered.Family (tent Y H),∀ S, Wallet (tent Y H) F S m (palmCo (ℶ s)) → WidthBudget S (budgetWidth (ℶ s) I') →
 (∃ L:List Wine, F=dek (tent Y H) L) ∧ ∀ L:List Wine, F=dek (tent Y H) L → ‖E s F-tallyW L‖ ≤ wane (ℶ s):=by
 filter_upwards [weekFunds Y z0 q' p0 U m I'] with s b F S h p
 obtain ⟨L,_,e⟩:=Loaves.recipe h.exam; refine ⟨⟨L,e⟩,b _ S h p⟩
#print axioms wiseFunds
#print axioms Wallet.flipFront
end Papal
end LocalLimit
end Rate
end YM.CF.Py
