import YM.SU5.Assay.Parcel
import YM.SU5.Assay.SeenBox
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j
/-! # Operator-level actual marginal assessment

Doesn't suffice to polish a propagating thin mark. But obtains much more
than merely convergence of marginal price *numbers* in that test. Use the
literal loose question, Caliper room width as in StationMaster (`μ` below)
including before selection, no gauge projection required on input. Every
marginal sticker asked that carries a charge, and *any* linear combination of
these, is **null as an operator** already there, in every admitted width!
No restriction on complexity/order over overlapping charges in a *linear*
combination. This concerns operators of the individual marginal inputs as
stencils and their summations, NOT products of those operators for poses whose
stencils aren't at separated time-budget positions. Uses Single field erasure
(and the heat monicity for general linear combinations in file on `Cinder`).
-/
local notation "μ"=> P.meanBox j
local notation "Π"=> (P.Hil j).space
local notation "ω"=> P.euclOp j
local notation "α"=>P.piece j s

private lemma puff_out (F : P.Vox j s)(h:P.GFlame (P.voxTest j s F)):α F=0:=by
 obtain ⟨q,r,v,t⟩:=h
 obtain ⟨S,k,a⟩:= (show ∃ S:Finset Cover, InTest K true S false F.val∧Tower.region j (meshface («Λ»:=Λ) 0 s) (K).ℓ S from ((purpose_ok ..).mp F.property).1)
 rw [area0] at a
 let f:=P.voxTest j s F
 have y:=pennantTrace K S r (f:=f) ((Tapestry.locates ..).mpr k)
 rw [show pennant K r f = q • f from t] at y
 have l:=P.erases_at_seam j s F (q•F) S k (InTest.smul q k) a r y
 have p: α (q•F)=q•α F:=show (arrows Y H V (π).circuit j 0 false C₀ s) (q•F)=_ from map_smul _ _ _
 have e: (1-q)•α F=0:=by rw [sub_smul,one_smul,sub_eq_zero];exact l.trans p
 exact (smul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr v.symm)

variable (s)
private lemma ashed_here (t:P.BEntry j w f)(h:P.GFlame f)(F:P.Vox j s):μ s w f (α F)=0:=by
 obtain ⟨S,y,a⟩:= (show ∃ S:Finset Cover, InTest K true S false F.val∧Tower.region j (meshface («Λ»:=Λ) 0 s) (K).ℓ S from ((purpose_ok ..).mp F.property).1)
 obtain ⟨T,k,d⟩:=t.holds
 have v:(P.voxTest j s F)∈bay K S true:=(Tapestry.locates ..).mpr y
 have u: Disjoint T (plow K j w S):=by
   apply Finset.disjoint_left.mpr
   intro i p m
   rw [area0] at a; obtain ⟨r,q,rfl⟩:= plow_stays K j w S m
   have he:0+(K).ℓ≤ r j:=a r q
   have ht:0<(K).ℓ:=(Nat.zero_le _).trans_lt (K).buffer
   have hl:= (d _ p).2
   rw [moves,if_pos rfl] at hl
   change r j + b*(w:ℤ)+(K).ℓ ≤ _ at hl
   omega
 let G:=slabT Y H s j false w (t.card s) F
 have ht:P.voxTest j s G=f*σ w (P.voxTest j s F):=Subtype.ext (slab_eq ..)
 have g':P.GFlame (P.voxTest j s G):=ht.symm ▸ (h.beside k (P.shifts_support j _ S v) u)
 rw [P.meanBox_eq s t]
 exact (snatch_equal Y H V s π Qt j false C₀ w (t.card s) t.pos F).trans (puff_out (P:=P) (s:=s) G g')

private lemma ashed_on (t:P.BEntry j w f)(h:P.GFlame f)(R:P.Register) (n:ℕ)(x:P.Vox j n): μ s w f (P.piece j n x)=0:=by
 let m:=max s n
 let p:=le_max_left s n; let q:=le_max_right s n
 change μ _ _ _ (actor Y H n (π).circuit j 0 false C₀ x)=_
 rw [←meanBox_raise s t m p,←join_actor Y H V (π).circuit j 0 false C₀ n m q]
 exact ashed_here m (t.raise s m p) (h.ascend R s _) _

lemma GFlame.operator (t:P.BEntry j w f)(h:P.GFlame f)(R:P.Register): μ s w f=0:=by
 have d:star (μ s w f)=0:=by
   ext1 y; apply all_voices Y H (π).circuit j 0 false C₀
   intro n x
   change inner ℂ (P.piece j n x) ((μ s w f).adjoint y)=inner ℂ _ (0:Π)
   rw [ContinuousLinearMap.adjoint_inner_right, ashed_on s t h R n x,inner_zero_right,inner_zero_left]
 exact star_eq_zero.mp d
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
