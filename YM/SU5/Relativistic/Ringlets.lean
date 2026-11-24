import YM.SU5.Relativistic.Teas
import YM.SU5.Relativistic.Joint
import YM.SU5.Relativistic.Temps
import YM.SU5.Relativistic.Ornaments
import YM.SU5.Relativistic.Bailout
/-! # Purchases, keeping track of M horizon; checking real estimate on the chosen course. Includes raw power bill. -/

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
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.ScreeV
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner

open Satin Tapestry
open CF.Crest CF.Crest.Sleet CF.Crest.Sleet.UpStart
open _root_.YM.CF.Buffered.Afterglow.Tower.SlabMark
/-! # purchase on THIS election. caller may increase gaps expressed in chosen level spacings. -/
open Tower.PhaseChoice
open Tower.Selected
open Tower.Reconstruction
local notation "K"=> tent Y H
private def staticB (j l:ℕ)(p:Patch) := 4*Buffered.r₃ p.L (Buffered.Aliases.finite_brix j p.L p.odd_side).choose (distanceLaw l) p.J+1
variable {a b:ℕ→ℕ}{I:ℕ→ Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}{L:Rack P l}{B:Clay P l}
  (D: Exhibition Y H a b I E L B)
local notation "V"=> D.univ_
variable (G:Tower.SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis)(c:∀ a:Axis,Tower.Arena Y H G.history.circuit a 0 false)
-- pricing all characters in this genealogy (exists level uniform in f)
include D G
private lemma lower_R {F:Buffered.Family (tent Y H)}(S:Finset Cover)(d:ℕ)(s:ℕ)(p:0<d)(i:InTest K false S false F)(e: Tower.SlabMark.Between (tent Y H) TA 0 (ruler P.block*d) S)
    (k:∀ n:ℕ,∀ᶠ i in atTop,∀ᶠ k in atTop, ‖sharp Y H s i k (thicket K TA d F n)‖≤Real.exp (-2*(staveP n:ℕ)))
    (f: displayAlgebra Y H D.univ_ G.history G.clipped j false (c j)→⋆ₐ[ℂ] ℂ) : ‖evaluate Y H V G j c (SameCharacter.resident Y H V G j false (c j) f) s F‖ ≤ Real.exp (-2):=by
 let x0:Tower.Field Y H s TA 0 false:=⟨F,(Tower.purpose_ok ..).2 ⟨⟨S,i.widen,(by rw [Tower.SlabMark.area0]; exact fun i h=> (e i h).1)⟩,nofun⟩⟩
 let x:Entry Y H s TA false d:=⟨x0,S,i.widen,e⟩
 rw [show F=(actorLabel Y H s TA false x.val).val from rfl,← selected_here Y H D G j TA c f s (actorLabel Y H s TA false x.val)]; apply Staved.shoulders Y H D.univ_ s G.history G.clipped TA false (c TA) _ x p
 intro n; let f:= thicket K TA d F n
 have he (t:ℕ):TestFamily K true (thicket K TA d F t):=by
    have ht: TestFamily K true F:= Tower.field_test Y H s TA 0 false x0 -- or aux_test
    have hx: TestFamily K true (tripleWide K TA d F):= (reflect_ok K TA _ ht).mul (move_ok K TA _ ht)
    induction t with|zero=>exact hx|succ i ih=>exact hx.mul (move_ok K TA _ ih)
 have ht:= D.univ_.together s f (he n); apply le_of_tendsto ht.periods.norm; exact (D.univ_.pick.grow_i.tendsto_atTop.eventually (k n)).mono (fun i p=> (show ‖I s f (a i)‖ ≤ Real.exp (-2*staveP n) from le_of_tendsto (ht.inner (a i)).norm (D.univ_.pick.grow_k.tendsto_atTop.eventually p)))
-- purchase with packed opportunity. now ζ.C character count nonfactor in odd Hilbert
open CF.Pannier.Chancel.ScreeV.Chateau Crest.Sleet.Sorcerer
omit D G
private def dessert (j w k:ℕ)(R Vx:ℝ)(p:0<R) : Supplier:= fun K' P a x S d D H W J l A=>
 let L:=staticB K'.j l P; let b:=2*(L+4*S.val); let B:=w+j+1; (CF.Pannier.Chancel.ScreeV.Chateau.taste S b L B (zigB S L k) (by unfold b L staticB; positivity) R Vx p 0).choose
open Lifted (nodeC)
-- cuisine: ALL axes. retains powers, strict *selected* uniform cap.
lemma curious {Z R δ C:ℝ}(hv:FairRoute P.P P.J P.h P.N0 Chi.canonical)(t: Inflation Z P)(p:WealthF C)(hx:0≤ C)(n:ℕ)(v:P.d ≤δ)(r:0<R)
    (q:∃ k:ℕ, (∀ n:Side,k≤n.val→∀ S:Finset (Skye.Seat n),Sparse d S→∀ M:Tulip.Male,∀ b,HearthB R (sp b P.K.j M (1:Pane n)) S) ∧ ∀ ε> (0:ℝ),∃ γ> (0:ℝ),∃ w:ℕ,∀ n:Side,k ≤ n.val→Winter P.K.j δ n γ w ε)
    (h:κ*R≤1/3)(ν:0<γ)(g:∀ᶠ i in atTop,∀ (n:Side),i≤n.val→ Winter P.K.j δ n γ w κ)
    (x:decorate (dessert d w n R C r) P l Z ≤ P.h):
     ∃ (v:Cover)(A a:ℕ), v∈ Lattice.box A ∧ (∀ j:Axis,zig K n + a ≤ (v j).natAbs) ∧ (tent Y H).ℓ≤A ∧
       ∀ᶠ s:ℕ in atTop,∀ (c:Fin 3)(m:ℕ),∀ᶠ i in atTop,∀ᶠ k in atTop, ‖sharp Y H s i k (thicket K TA (heightB A) (Banner K v A a c) m)‖ ≤ Real.exp (-2*staveP m):=by
 let S:=P.block; let a₀:= addgap K; let T:= zig K n; let p':=CF.Pannier.Chancel.ScreeV.Chateau.taste P.block a₀ (reserve P l) (w+d+1) T addgap_pos R C r 0; let H₀:= p'.choose
 obtain ⟨A,h',b,e,j₀,X,Y',Y₀,η,ε,μp,E,q_,muZ,k₁,k₂,ρ,p0,hY,g₀,r0,hxY,ε0,εx,b0,hvB,ht,ht',a'⟩:= p'.choose_spec.get; refine ⟨b,A,h',b0,ht,μp,eventually_all.mpr (fun c=>?_)⟩
 -- eventually_all swaps c!
 have L:=TagCost (tent Y H) b A h' c b0
 obtain ⟨Xh,Xt⟩:= CF.Pannier.Chancel.ScreeV.Chateau.tall A; obtain ⟨k,K1,K2⟩:= q; obtain ⟨γ',vγ,u,Q⟩:=K2 ε ε0
 obtain ⟨τ0,hτ,tB,pB,T',P'⟩:= signway K b A h' (κ:=0) b0 hvB E ν vγ g₀ hxY ht' P.K.j (by rw [P.kJ]; exact a') u P.J.n
 apply tufts Y H hv p hx ⟨k,K2⟩ q_ muZ t k₁ k₂ (ρ.trans x) v (γ:=γ) (w:=w) (κ:=κ) (ε:=ε) (γ':=γ') (d:=d) (u:=u) (g.and (eventually_ge_atTop k)|>.mono (fun i p n g=>⟨p.1 n g,Q n (p.2.trans g),fun M b S t=> K1 n (p.2.trans g) S t _ b⟩)) hY h εx r0 p0 pB (Banner K b A h' c) (hallW A) L.widen (bill_A _ A μp) Xh Xt
 have htemp:Tendsto (fun s:ℕ=>temp (hat P.R.L P.x s)) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 filter_upwards [htemp.eventually (ge_mem_nhds hτ)] with s Hτ
 filter_upwards [(count_grows Y s).eventually_ge_atTop T'] with i c'
 filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop s,(tide_M Y s i).eventually_ge_atTop T'] with k eA eB
 let z:=momentm Y i s; let n:=Papal.count Y s i; have ht: (tent Y H).c z=n:=terrain ..; let QX:= CF.Pannier.Chancel.ScreeV.Chateau.Tag K b A h' c z
 let I':=gram Y s i k; let M:=I'.J.M; let W:= I'.p.threshold; have hW:W=temp (hat P.R.L P.x s):= (congrArg BudgetPoint.threshold (prices_plot Y s i k eA).1).trans (Y.meter.boot s).1
 have he:= P' z (by rw [ht]; exact c') M eB (show IsStarProjection _ from by rw [ht]; exact ((P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _).projection _ (guard0 P.dpos.le))) W I'.p.threshold_pos.le (hW ▸ Hτ) c
 refine ⟨[QX],rfl,?_,?_, Company.alone he⟩
 · change QX.broad∪∅⊆_; simp; exact subset_refl _
 rw [probe_cons,CF.Pannier.Chancel.Cliplet.probe_nil,mul_one]

lemma salute (U:Supplier)(k:ℕ)(ε η:ℝ)(h:0<η) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧ FairRoute P.P P.J P.h P.N0 Chi.canonical ∧
      ∃ (v:Cover)(A h':ℕ), v∈ Lattice.box A ∧ (∀ j:Axis,zig (tent Y H) k + h' ≤ (v j).natAbs) ∧ (tent Y H).ℓ≤A ∧
       (∀ᶠ s in atTop,∀ (j:Axis) (c:∀ a:Axis,Tower.Arena Y H G.history.circuit a 0 false) (x:displayAlgebra Y H D.univ_ G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)(r:Fin 3),
        ‖evaluate Y H D.univ_ G j c (SameCharacter.resident Y H D.univ_ G j false (c j) x) s (Banner (tent Y H) v A h' r)‖ ≤ Real.exp (-2)):=by
 obtain ⟨R,δ,r,v,N,d,X,hK⟩:= chosenFlatPrice 4 (by decide); let ε':= (3*R)⁻¹; have he:0<ε':=by unfold ε'; positivity
 obtain ⟨C,hC,g'⟩:=endowed; obtain ⟨γ,t,W,u⟩:= hK _ he; let V₀: Supplier := fun p P a X z c t W' D q k' T=> max (U p P a X z c t W' D q k' T) (dessert d W k R C r p P a X z c t W' D q k' T)
 obtain ⟨P,l,Z,H,Y,q,D,x,C',a,b,I,E,L,YG,T,t',D',G,A,f,F,V',R₀,Q₀,i,p,Bv⟩:= bailout ε (min η δ) (lt_min h v) V₀
 obtain ⟨z,w₀,d₀,y,j₀,Φ,P'⟩:= curious Y H Bv p.korn.extent g' hC k (p.d_le.trans (min_le_right ..)) r (d:=d) (by rw [P.kJ]; exact ⟨N,X,hK⟩) (κ:=ε') (show ε'*R≤ 1/3 from (by unfold ε'; apply le_of_eq; field_simp)) t (w:=W) (by rw [P.kJ]; exact (eventually_ge_atTop N).mono (fun i v n h=>u n (by omega))) ((le_max_right ..).trans p.decorate_le)
 refine ⟨P,l,Z,H,Y,q,D,x,C',a,b,I,E,L,YG,T,t',D',G,A,f,F,V',R₀,Q₀,i,{ p with decorate_le := (le_max_left ..).trans p.decorate_le, d_le:= p.d_le.trans (min_le_left ..)},Bv,z,w₀,d₀,y,j₀,Φ,?_⟩
 exact P'.mono (fun s p j c a r=> lower_R Y H D'.toExhibition G j c _ _ _ (by unfold heightB; positivity) (TagCost (tent Y H) z w₀ d₀ r y) (bill_A (tent Y H) w₀ Φ) (p r) a)
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.salute
